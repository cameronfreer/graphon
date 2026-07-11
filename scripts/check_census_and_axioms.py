#!/usr/bin/env python3
"""CI integrity gate for the graphon formalization.

1. **Placeholder census (declaration-name allowlist).** Strips comments and string
   literals from every `Graphon/*.lean` file, finds every `sorry` / `admit` token
   (any form: standalone, `by sorry`, `:= sorry`, ...), maps each to its enclosing
   declaration, and requires the resulting set of (file, declaration) pairs to equal
   EXACTLY the documented frozen known-false stubs (allowlist below).
2. **Axiom audit.** Runs `lake env lean scripts/axiom_audit.lean` and requires that
   (a) exactly the intended declaration list was printed, (b) every reported axiom is
   a member of the allowed set {propext, Classical.choice, Quot.sound} (a declaration
   using FEWER axioms passes), and (c) `sorryAx` and custom axioms are absent.

Run from the repository root after `lake build`. Exit code 0 iff both checks pass.
"""

import re
import subprocess
import sys
from pathlib import Path

# The deliberately-retained refuted-conjecture stubs (issue #19: shrinking to empty;
# the Lovasz/Spectral public stubs were removed 2026-07-10, PR 1 of 2).
ALLOWED_STUBS = {
    ("Graphon/MatrixDetermination.lean", "labeledEvalK_separates"),
    ("Graphon/MatrixDetermination.lean", "vertexOrbit_of_star0_tri0_eq"),
    ("Graphon/MatrixDetermination.lean", "pairOrbit_of_vertexOrbits_and_path"),
}

# The load-bearing declarations whose axiom profile is enforced
# (docs/post-r3-mainline-completion-plan.md §4.4 plus the compactness headline).
AUDITED_DECLS = {
    "Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval",
    "Graphon.MeasureIso.Mod0MeasureIso.toMeasurableEquiv",
    "Graphon.MeasurePreserving.exists_common_coupling_maps",
    "Graphon.cutNormDiff_pullback_le",
    "Graphon.MeasurePreserving.exists_controlled_cell_alignment",
    "Graphon.exists_mpEquiv_cutNormDiff_lt_add",
    "Graphon.cutDistance_triangle",
    "Graphon.totallyBounded",
    "Graphon.complete",
    "Graphon.compact",
    "Graphon.first_sampling_lemma",
    "Graphon.cutDistance_zero_of_homDensity_eq",
    "Graphon.homDensity_eq_sum_sampleMass",
    "Graphon.sampleMass_map_perm",
    "Graphon.samplePMF_map_comap",
    "Graphon.sampleLaw_map_comap",
    "Graphon.sampleLaw_const_eq_binomial",
    "GraphonSpace.mk_eq_mk_iff",
    "GraphonSpace.instCompactSpace",
    "Graphon.samplePMF_eq_all_iff_weaklyIsomorphic",
    "GraphonSpace.isClosedEmbedding_sampleCoordinates",
    "GraphonSpace.mixturePMF_map_comap",
    "GraphonSpace.continuous_mixturePMF_apply_toReal",
    "GraphonSpace.exists_subseq_tendsto",
    "Graphon.homDensity_sum",
    "GraphonSpace.mixtureExchangeableLaw_injective",
    "Graphon.sampleMass_ofSimpleGraphOn",
}

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

DECL_RE = re.compile(
    r"(?:^|\n)[ \t]*(?:@\[[^\]]*\][ \t\n]*)?"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+|unsafe[ \t]+|scoped[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example)[ \t]+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)"
)
TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_'])(sorry|admit)(?![A-Za-z0-9_'])")


def strip_comments_and_strings(src: str) -> str:
    """Blank out nested block comments `/- ... -/`, line comments `--`, and string
    literals, preserving offsets (replaced by spaces, newlines kept)."""
    out = list(src)
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
            elif two == "-/":
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif two == "/-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
        elif two == "--":
            while i < n and src[i] != "\n":
                out[i] = " "
                i += 1
        elif c == '"':
            out[i] = " "
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    out[i] = " "
                    i += 1
                    if i < n:
                        out[i] = " "
                        i += 1
                    continue
                if src[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


def census() -> bool:
    found = set()
    for path in sorted(Path("Graphon").glob("*.lean")):
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        decls = [(m.start(1), m.group(1)) for m in DECL_RE.finditer(stripped)]
        for m in TOKEN_RE.finditer(stripped):
            name = "<no enclosing declaration>"
            for pos, decl in decls:
                if pos < m.start():
                    name = decl
                else:
                    break
            found.add((str(path), name))
    ok = found == ALLOWED_STUBS
    print("== Placeholder census (sorry/admit tokens by declaration) ==")
    for f, d in sorted(found):
        marker = "" if (f, d) in ALLOWED_STUBS else "  <-- NOT ALLOWLISTED"
        print(f"  {f}: {d}{marker}")
    for f, d in sorted(ALLOWED_STUBS - found):
        print(f"  MISSING expected stub: {f}: {d}")
    print("census:", "OK" if ok else "FAIL")
    return ok


def axiom_audit() -> bool:
    proc = subprocess.run(
        ["lake", "env", "lean", "scripts/axiom_audit.lean"],
        capture_output=True,
        text=True,
    )
    out = proc.stdout + proc.stderr
    print("== Headline axiom audit ==")
    print(out.strip())
    if proc.returncode != 0:
        print("axiom audit: FAIL (lean invocation failed)")
        return False
    reported = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out, re.DOTALL):
        axioms = {a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()}
        reported[m.group(1)] = axioms
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
        reported[m.group(1)] = set()
    ok = True
    if set(reported) != AUDITED_DECLS:
        print("FAIL: printed declaration set differs from the intended audit list.")
        for d in sorted(AUDITED_DECLS - set(reported)):
            print(f"  missing: {d}")
        for d in sorted(set(reported) - AUDITED_DECLS):
            print(f"  unexpected: {d}")
        ok = False
    for decl, axioms in sorted(reported.items()):
        bad = axioms - ALLOWED_AXIOMS
        if bad:
            print(f"FAIL: {decl} uses disallowed axiom(s): {sorted(bad)}")
            ok = False
    print("axiom audit:", "OK" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    c = census()
    a = axiom_audit()
    if c and a:
        print("OK: census and axiom audit passed.")
        sys.exit(0)
    sys.exit(1)
