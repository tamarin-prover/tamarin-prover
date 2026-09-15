#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
model="$repo_dir/examples/regression/trace/export-property-instrumentation.spthy"
restriction_model="$repo_dir/examples/regression/trace/export-restriction-disjunction.spthy"
knowledge_model="$repo_dir/examples/regression/trace/export-knowledge-fragment.spthy"
refactoring_model="$repo_dir/examples/regression/trace/export-refactoring-regressions.spthy"
equivalence_model="$repo_dir/examples/regression/trace/export-backend-characterization.spthy"
constraint_scope_model="$repo_dir/examples/regression/trace/export-constraint-scope.spthy"
deepsec_model="$repo_dir/examples/sapic/export/toy-example.spthy"
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-export-properties.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

export_model_lemma() {
  input=$1
  lemma=$2
  output=$3
  "$tamarin" -d=0 -m=proverif "--lemma=$lemma" "-o=$output" "$input" >/dev/null
}

export_lemma() {
  export_model_lemma "$model" "$1" "$2"
}

require_pattern() {
  pattern=$1
  output=$2
  if ! grep -Eq "$pattern" "$output"; then
    echo "missing pattern in $output: $pattern" >&2
    exit 1
  fi
}

completion="$tmp_dir/completion.pv"
export_lemma completion_required "$completion"
require_pattern '^event eRuleCompleted\(bitstring\)\.$' "$completion"
require_pattern 'event\(eRuleCompleted\( rid[^)]*\)\)' "$completion"
require_pattern 'event eRuleCompleted\(rid_rEmitTogether\)' "$completion"

tautology="$tmp_dir/tautology.pv"
export_lemma completion_not_required_for_same_fact "$tautology"
if grep -q 'RuleCompleted' "$tautology"; then
  echo "same-fact correspondence unexpectedly requested completion" >&2
  exit 1
fi

temporal="$tmp_dir/temporal.pv"
export_lemma temporal_equality_uses_rule_ids "$temporal"
require_pattern '^event eFirst\(bitstring, bitstring\)\.$' "$temporal"
require_pattern '^event eSecond\(bitstring, bitstring\)\.$' "$temporal"
require_pattern 'rid_[[:alnum:]_]+ = rid_[[:alnum:]_]+' "$temporal"

split_notice="$tmp_dir/split-notice.pv"
if ! "$tamarin" -d=0 -m=proverif --quit-on-warning --lemma=split_queries_notice \
  "-o=$split_notice" "$model" >/dev/null 2>&1; then
  echo "informational query recombination triggered --quit-on-warning" >&2
  exit 1
fi
require_pattern '^Export notes$' "$split_notice"
require_pattern 'Lemma `split_queries_notice`: was emitted as 2 queries.*\[PV-GOAL-SPLIT\]' "$split_notice"
if grep -q '^WARNING: export omitted or approximated proof-relevant input\.$' "$split_notice"; then
  echo "informational query recombination was rendered as a warning" >&2
  exit 1
fi

shadowed="$tmp_dir/independent-shadowed-binders.pv"
export_lemma independent_shadowed_binders "$shadowed"
require_pattern 'event\(eFirst\( x \)\)' "$shadowed"
require_pattern 'event\(eSecond\( x_1 \)\)' "$shadowed"
if grep -Eq 'event\(eFirst\( ([[:alnum:]_]+) \)\).*event\(eSecond\( \1 \)\)' "$shadowed"; then
  echo "independent universal disjunct binders were conflated" >&2
  exit 1
fi

mixed_quantifiers="$tmp_dir/mixed-quantifier-negated-disjunct.pv"
export_lemma mixed_quantifier_negated_disjunct "$mixed_quantifiers"
require_pattern 'Lemma translation failed: formula has 2 quantifier alternations; ProVerif supports at most one' "$mixed_quantifiers"
require_pattern 'Lemma `mixed_quantifier_negated_disjunct`: produced no ProVerif query.*\[PV-GOAL-OMITTED\]' "$mixed_quantifiers"
if grep -q '^query ' "$mixed_quantifiers"; then
  echo "mixed existential/universal negated disjunct produced an unsound query" >&2
  exit 1
fi

constraint_scope="$tmp_dir/existential-constraint-scope.pv"
export_model_lemma "$constraint_scope_model" existential_constraint_scope "$constraint_scope"
require_pattern 'Lemma translation failed: formula is outside the supported ProVerif query fragment' "$constraint_scope"
if grep -q '^query ' "$constraint_scope"; then
  echo "constraint escaped its existential scope" >&2
  exit 1
fi

constraint_scope_reversed="$tmp_dir/existential-constraint-scope-reversed.pv"
export_model_lemma "$constraint_scope_model" existential_constraint_scope_reversed "$constraint_scope_reversed"
require_pattern 'Lemma translation failed: formula is outside the supported ProVerif query fragment' "$constraint_scope_reversed"
if grep -q '^query ' "$constraint_scope_reversed"; then
  echo "constraint escaped its reversed existential scope" >&2
  exit 1
fi

restriction="$tmp_dir/restriction.pv"
"$tamarin" -d=0 -m=proverif --lemma=no_link_chain "-o=$restriction" "$restriction_model" >/dev/null
if [ "$(grep -c '==> false\.' "$restriction")" -ne 2 ]; then
  echo "forbidden disjunction did not produce two false-conclusion restrictions" >&2
  exit 1
fi
require_pattern 'event\(eLink\( x, y \)\).*event\(eLink\( y, z \)\)' "$restriction"
require_pattern 'event\(eLink\( x, y \)\).*event\(eLink\( z, x \)\)' "$restriction"
if grep -q 'Restriction has negated event' "$restriction"; then
  echo "forbidden disjunction retained a negated-event restriction" >&2
  exit 1
fi

knowledge_supported="$tmp_dir/knowledge-supported.pv"
export_model_lemma "$knowledge_model" supported_k "$knowledge_supported"
if grep -q 'Lemma translation failed' "$knowledge_supported"; then
  echo "supported T-UKF formula was rejected" >&2
  exit 1
fi
require_pattern 'attacker\( x \)@j' "$knowledge_supported"
require_pattern 'supported_positive_k_restriction' "$knowledge_supported"
require_pattern 'supported_positive_k_axiom \[reuse/source lemma translated as axiom\]' "$knowledge_supported"
require_pattern 'rejected_negative_k_restriction' "$knowledge_supported"
require_pattern 'Restriction translation failed: NNF\(phi\) contains a negative K atom' "$knowledge_supported"
require_pattern 'rejected_ku_restriction' "$knowledge_supported"
require_pattern 'Restriction translation failed: formula contains KU fact' "$knowledge_supported"
require_pattern 'rejected_negative_k_axiom \[reuse/source lemma not translated as axiom\]' "$knowledge_supported"
require_pattern 'Axiom translation failed: NNF\(phi\) contains a negative K atom' "$knowledge_supported"
require_pattern 'rejected_ku_axiom \[reuse/source lemma not translated as axiom\]' "$knowledge_supported"
require_pattern 'Axiom translation failed: formula contains KU fact' "$knowledge_supported"

knowledge_ku="$tmp_dir/knowledge-ku.pv"
export_model_lemma "$knowledge_model" rejected_ku "$knowledge_ku"
require_pattern 'Lemma translation failed: formula contains KU fact' "$knowledge_ku"

knowledge_exists="$tmp_dir/knowledge-exists.pv"
export_model_lemma "$knowledge_model" rejected_exists_k "$knowledge_exists"
require_pattern 'Lemma translation failed: exists-trace formula contains K fact' "$knowledge_exists"

knowledge_negative="$tmp_dir/knowledge-negative.pv"
export_model_lemma "$knowledge_model" rejected_negative_k "$knowledge_negative"
require_pattern 'Lemma translation failed: formula is outside T-UKF: NNF\(not\(phi\)\) contains a negative K atom' "$knowledge_negative"
require_pattern '^WARNING: export omitted or approximated proof-relevant input\.$' "$knowledge_negative"
require_pattern '^Changed assumptions$' "$knowledge_negative"
require_pattern 'Restriction `rejected_negative_k_restriction`: was not emitted' "$knowledge_negative"
require_pattern 'Axiom `rejected_negative_k_axiom`: was not emitted' "$knowledge_negative"
require_pattern '^Untranslated goals$' "$knowledge_negative"
require_pattern 'Lemma `rejected_negative_k`: produced no ProVerif query' "$knowledge_negative"

knowledge_skipped="$tmp_dir/knowledge-skipped.pv"
"$tamarin" -d=0 -m=proverif --lemma=supported_k \
  --proverif-no-reuse-lemmas --proverif-no-source-lemmas --proverif-no-restrictions \
  "-o=$knowledge_skipped" "$knowledge_model" >/dev/null
if grep -q '^WARNING: export omitted or approximated proof-relevant input\.$' "$knowledge_skipped"; then
  echo "explicitly skipped assumptions unexpectedly produced export diagnostics" >&2
  exit 1
fi

if "$tamarin" -d=0 -m=proverif --quit-on-warning --lemma=rejected_ku \
  "-o=$tmp_dir/quit-on-warning.pv" "$knowledge_model" >/dev/null 2>&1; then
  echo "--quit-on-warning ignored an untranslated selected goal" >&2
  exit 1
fi

# Focused invariants for prepared properties and allocated instrumentation.
refactoring_collision="$tmp_dir/refactoring-collision.pv"
export_model_lemma "$refactoring_model" generated_rule_id_avoids_source_variable "$refactoring_collision"
require_pattern 'event\(eBranchB\( rid, x \)\)' "$refactoring_collision"
require_pattern 'event\(eBranchC\( rid, x \)\)' "$refactoring_collision"
require_pattern '^event eAxiomA\(bitstring, bitstring\)\.$' "$refactoring_collision"
require_pattern 'event\(eAxiomA\( rid, x \)\)' "$refactoring_collision"
require_pattern 'event\(eAxiomB\( rid, x \)\)' "$refactoring_collision"
require_pattern 'event\(eRuleCompleted_1\( rid \)\)' "$refactoring_collision"
require_pattern 'event\(eAxiomC\( rid, x \)\)' "$refactoring_collision"
require_pattern 'event eRuleCompleted_1\(rid_rEmitAxiomEvents\)\.' "$refactoring_collision"
require_pattern 'new rid_rCollision_1: bitstring;' "$refactoring_collision"
require_pattern 'in\(publicChannel, rid_rCollision: bitstring\);' "$refactoring_collision"
require_pattern 'event eCollisionA\(rid_rCollision_1, rid_rCollision\);' "$refactoring_collision"

refactoring_query_collision="$tmp_dir/refactoring-query-collision.pv"
export_model_lemma "$refactoring_model" generated_query_id_avoids_source_variable "$refactoring_query_collision"
require_pattern 'query rid_1:bitstring, rid:bitstring' "$refactoring_query_collision"
require_pattern 'event\(eAxiomA\( rid_1, rid \)\)' "$refactoring_query_collision"
require_pattern 'event\(eAxiomB\( rid_1, rid \)\)' "$refactoring_query_collision"

refactoring_completion="$tmp_dir/refactoring-completion.pv"
export_model_lemma "$refactoring_model" internal_completion_avoids_user_event "$refactoring_completion"
if [ "$(grep -c '^event eRuleCompleted(bitstring)\.$' "$refactoring_completion")" -ne 1 ]; then
  echo "user completion event declaration was not preserved" >&2
  exit 1
fi
require_pattern '^event eRuleCompleted_1\(bitstring\)\.$' "$refactoring_completion"
require_pattern 'event eRuleCompleted\(x\);' "$refactoring_completion"
require_pattern 'event eRuleCompleted_1\(rid_rUserCompletion\)\.' "$refactoring_completion"

induction="$tmp_dir/induction.pv"
export_lemma induction_composite "$induction"
require_pattern '==> \(event\(eFirst\( x \)\)@j' "$induction"
require_pattern '\)\[induction\]\.$' "$induction"

equivalence="$tmp_dir/equivalence.pv"
"$tamarin" -d=0 -m=proverifequiv "-o=$equivalence" "$equivalence_model" >/dev/null
require_pattern '^equivalence$' "$equivalence"
require_pattern 'new x_[[:digit:]]+:bitstring' "$equivalence"

deepsec="$tmp_dir/equivalence.dps"
"$tamarin" -d=0 -m=deepsec "-o=$deepsec" "$deepsec_model" >/dev/null
require_pattern '^query session_equiv\($' "$deepsec"
require_pattern '!\^3\(' "$deepsec"

if command -v proverif >/dev/null 2>&1; then
  proverif -parse-only "$completion" >/dev/null
  proverif -parse-only "$tautology" >/dev/null
  proverif -parse-only "$temporal" >/dev/null
  proverif -parse-only "$shadowed" >/dev/null
  proverif -parse-only "$mixed_quantifiers" >/dev/null
  proverif -parse-only "$constraint_scope" >/dev/null
  proverif -parse-only "$constraint_scope_reversed" >/dev/null
  proverif -parse-only "$restriction" >/dev/null
  proverif -parse-only "$knowledge_supported" >/dev/null
  proverif -parse-only "$refactoring_collision" >/dev/null
  proverif -parse-only "$refactoring_query_collision" >/dev/null
  proverif -parse-only "$refactoring_completion" >/dev/null
  proverif -parse-only "$induction" >/dev/null
  proverif -parse-only "$equivalence" >/dev/null
elif [ -n "${CI:-}" ]; then
  echo "proverif is required for export parser validation in CI" >&2
  exit 1
else
  echo "skipping export parser validation: proverif not found" >&2
fi

echo "export property instrumentation regression passed"
