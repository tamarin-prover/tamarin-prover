#!/usr/bin/env python3

"""
Write the per-page pandoc metadata for the HTML manual.

For every page this produces OUTDIR/<name>.json with the chapter list for the
sidebar (marking the current chapter), the previous and next chapters, the page
title, and the version label. Chapter titles are taken from the first heading
of each source file, so the navigation always matches the chapter headings.

Usage:

    chapters.py OUTDIR BRANCH VERSION --pages SRC... --chapters SRC...

Builds on the stable branch are labelled with the Tamarin version; all other
builds are labelled as the development branch and link to the stable manual.
"""

import argparse
import json
import os
import re

STABLE_BRANCH = "master"
STABLE_URL = "https://tamarin-prover.com/manual/master/book/"


def heading(path):
    """Return the text of the first level-1 heading (setext or ATX) of a file."""
    previous = ""
    with open(path, encoding="utf-8") as source:
        for line in source:
            line = line.rstrip()
            atx = re.match(r"#\s+(.*?)\s*#*$", line)
            if atx:
                title = atx.group(1)
                break
            if previous and re.fullmatch(r"=+", line):
                title = previous
                break
            previous = line
        else:
            raise SystemExit(f"{path}: no level-1 heading found")
    # Drop pandoc header attributes such as {#sec:label}.
    return re.sub(r"\s*\{[^}]*\}$", "", title).strip()


def page(path):
    name = os.path.splitext(os.path.basename(path))[0]
    return {
        "name": name,
        "file": name + ".html",
        "number": str(int(name.split("_")[0])),
        "title": heading(path),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("outdir")
    parser.add_argument("branch")
    parser.add_argument("version")
    parser.add_argument("--pages", nargs="+", required=True)
    parser.add_argument("--chapters", nargs="+", required=True)
    args = parser.parse_args()

    pages = {path: page(path) for path in args.pages + args.chapters}
    chapters = [pages[path] for path in args.chapters]
    sidebar = [{key: c[key] for key in ("file", "number", "title")} for c in chapters]

    stable = args.branch == STABLE_BRANCH
    release = ".".join(args.version.split(".")[:2])
    label = f"Manual for Tamarin {release}".strip() if stable else "Manual for the development branch"

    for path in args.pages:
        this = pages[path]
        meta = {
            "pagetitle": f"{this['title']} – Tamarin Prover Manual",
            "manual-label": label,
            "chapters": [dict(c, current=True) if c["file"] == this["file"] else c for c in sidebar],
        }
        if not stable:
            meta["development"] = True
            meta["stable-url"] = STABLE_URL + this["file"]
        if this in chapters:
            index = chapters.index(this)
            meta["pagination"] = True
            if index > 0:
                meta["prev"] = sidebar[index - 1]
            if index + 1 < len(chapters):
                meta["next"] = sidebar[index + 1]
        with open(os.path.join(args.outdir, this["name"] + ".json"), "w", encoding="utf-8") as out:
            json.dump(meta, out, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
