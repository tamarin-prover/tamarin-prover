"""Run against a GUI-enabled build with TAMARIN=/path/to/tamarin-prover."""

import json
import os
from pathlib import Path
import re
import socket
import subprocess
import tempfile
import time
import unittest
from urllib.error import URLError
from urllib.parse import urlencode
from urllib.request import urlopen


CLAIM = "not (Ex #i. Seen(pairSelf('a'))@i)"
MODEL = f"""theory Edit begin
macros: pairSelf(x) = <x,x>
rule Observe: [] --[ Seen(pairSelf('a')) ]-> []
rule Receive: [In('a')] --[ Received() ]-> []
lemma assumption [reuse]: "{CLAIM}"
lemma dependent [passive]: "{CLAIM}"
simplify
by contradiction
lemma independent: exists-trace "T"
simplify
SOLVED
lemma missing_proof: "T"
by INVALIDATED
end
"""


class InteractiveLemmaEdits(unittest.TestCase):
    def setUp(self):
        self.binary = os.environ.get("TAMARIN", "tamarin-prover")
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.folder = Path(folder.name)
        (self.folder / "Edit.spthy").write_text(MODEL)
        with socket.socket() as sock:
            sock.bind(("127.0.0.1", 0))
            port = sock.getsockname()[1]
        self.origin = f"http://127.0.0.1:{port}"
        server = subprocess.Popen(
            [self.binary, "interactive", "--interface=127.0.0.1", f"--port={port}", self.folder],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        self.addCleanup(server.wait, 10)
        self.addCleanup(server.terminate)
        for _ in range(100):
            try:
                index = self.request("/")
                break
            except URLError:
                if server.poll() is not None:
                    self.fail(f"interactive server exited with {server.returncode}")
                time.sleep(0.1)
        else:
            self.fail("interactive server did not start")
        self.theory = re.search(r'(/thy/trace/\d+)/overview', index)[1]

    def request(self, path, form=None):
        body = None if form is None else urlencode(form).encode()
        with urlopen(self.origin + path, body, timeout=15) as response:
            return response.read().decode()

    def source(self):
        return self.request(self.theory + "/download/Edit.spthy")

    def edit(self, path, text=""):
        return self.request(self.theory + "/edit/" + path, {"lemma-text": text})

    def verify(self, name):
        result = json.loads(self.request(self.theory + "/verify/proof/" + name))
        self.assertIn("redirect", result)

    def follow_action(self, path):
        result = json.loads(self.request(self.theory + path))
        self.theory = re.search(r'(/thy/trace/\d+)/overview', result["redirect"])[1]

    def summary(self):
        exported = self.folder / "export.spthy"
        exported.write_text(self.source())
        result = subprocess.run([self.binary, exported], check=True, capture_output=True, text=True, timeout=20)
        return result.stdout.split("summary of summaries:")[-1]

    def test_edit_then_verify(self):
        page = self.edit("edit/assumption", f'lemma renamed [reuse]: "{CLAIM}"')
        self.assertIn("verify it", page)
        self.assertIn("dependent (all-traces): proof has been invalidated", self.summary())
        self.verify("dependent")
        self.assertIn("dependent (all-traces): verified (2 steps)", self.summary())
        self.assertRegex(self.source(), r'lemma renamed \[reuse\]:\s*all-traces "[^"]*pairSelf')

    def test_delete_then_verify(self):
        page = self.edit("delete/assumption")
        self.assertIn("verify it", page)
        self.verify("dependent")
        self.verify("independent")
        summary = self.summary()
        self.assertIn("dependent (all-traces): analysis incomplete", summary)
        self.assertIn("independent (exists-trace): verified (2 steps)", summary)

    def test_rejected_edits_preserve_original(self):
        original = self.source()
        for replacement in ('lemma independent: "T"', 'lemma assumption [passive, sources]: "T"'):
            with self.subTest(replacement=replacement):
                self.edit("edit/assumption", replacement)
                self.assertEqual(original, self.source())

    def test_delete_path_invalidates_reused_proofs(self):
        self.follow_action("/del/path/lemma/assumption")
        self.assertIn("dependent (all-traces): proof has been invalidated", self.summary())

    def test_passive_reuse_only_invalidates_passive_proofs(self):
        self.edit("edit/assumption", f'lemma assumption [passive, reuse]: "{CLAIM}"')
        self.verify("independent")
        self.verify("dependent")
        self.edit("delete/assumption")
        summary = self.summary()
        self.assertIn("dependent (all-traces): proof has been invalidated", summary)
        self.assertIn("independent (exists-trace): verified (2 steps)", summary)

    def test_add_first_passive_lemma_to_empty_theory(self):
        for name in ("missing_proof", "independent", "dependent", "assumption"):
            self.edit("delete/" + name)
        claim = 'exists-trace "Ex #i. Received()@i"'
        self.edit("add/%3Cfirst%3E", f"lemma first [passive]: {claim}")
        self.follow_action("/autoprove/idfs/15/False/proof/first")
        self.assertIn("first (exists-trace): falsified - no trace found", self.summary())
        self.edit("edit/first", f"lemma first: {claim}")
        self.follow_action("/autoprove/idfs/15/False/proof/first")
        self.assertIn("first (exists-trace): verified", self.summary())

    def test_verify_without_saved_steps(self):
        self.verify("missing_proof")
        self.assertIn("missing_proof (all-traces): analysis incomplete", self.summary())


if __name__ == "__main__":
    unittest.main()
