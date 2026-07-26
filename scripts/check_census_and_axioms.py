#!/usr/bin/env python3
"""CI integrity gate for the graphon formalization.

1. **Placeholder census (declaration-name allowlist).** Strips comments and string
   literals from every `Graphon/*.lean` file, finds every `sorry` / `admit` token
   (any form: standalone, `by sorry`, `:= sorry`, ...), maps each to its enclosing
   declaration, and requires the resulting set of (file, declaration) pairs to equal
   EXACTLY the allowlist below — empty since issue #19: strictly zero tokens.
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

# Issue #19 complete (PR 2 of 2, 2026-07-11): the last frozen known-false stubs in
# MatrixDetermination.lean were deleted, so the census now enforces strictly ZERO
# sorry/admit tokens across the project.
ALLOWED_STUBS = set()

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
    "GraphonSpace.abs_integral_homDensityCoord_empiricalMixing_sub_le",
    "GraphonSpace.exists_mixtureExchangeableLaw_eq",
    "GraphonSpace.graphon_mixture_representation",
    "GraphonSpace.isDissociated_mixtureExchangeableLaw_iff",
    "GraphonSpace.isDissociated_iff_exists_sampleExchangeableLaw",
    "GraphonSpace.empiricalMixing_tendsto_representingMeasure",
    "GraphonSpace.abs_mixturePMF_empiricalMixing_sub_le",
    "InfiniteGraph.probabilityMeasure_ext_of_map_restrictFin",
    "Graphon.ExchangeableGraphLaw.infiniteLaw_map_restrictFin",
    "Graphon.ExchangeableGraphLaw.infiniteLaw_map_relabel",
    "Graphon.exchangeableGraphLawEquivInfinite",
    "GraphonSpace.infiniteMixtureLawEquiv",
    "GraphonSpace.isClosedEmbedding_infiniteSampleLaw",
    "GraphonSpace.empiricalGraphon_law_tendsto",
    "GraphonSpace.isDissociated_iff_exists_infiniteSampleExchangeableLaw",
    "InfiniteGraph.map_sampleInfinite_restrictFin",
    "InfiniteGraph.map_sampleInfinite",
    "GraphonSpace.mixtureInfiniteLaw_eq",
    "InfiniteGraph.sampledEmpiricalGraphon_tendstoInMeasure",
    "ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences",
    "ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences'",
    "Graphon.measureReal_abs_homDensity_sampled_sub_le",
    "InfiniteGraph.tsum_samplerSource_homDensity_tail_ne_top",
    "InfiniteGraph.sampledEmpiricalGraphon_tendsto_ae",
    "GraphonSpace.ae_tendsto_empiricalGraphon_infiniteSampleLaw",
    "GraphonSpace.map_limitGraphon_law",
    "InfiniteGraph.isDissociated_iff_exists_sampler",
    "InfiniteGraph.sampleInfinite_adj",
    "GraphonSpace.tendsto_empiricalGraphon_drop_iff",
    "GraphonSpace.measurable_limitGraphon_vertexTailAlgebra",
    "Graphon.InfiniteExchangeableGraphLaw.law_map_drop",
    "Graphon.InfiniteExchangeableGraphLaw.vertexTailTrivial_of_restrictionIndependent",
    "GraphonSpace.isDissociated_of_vertexTailTrivial",
    "Graphon.InfiniteExchangeableGraphLaw.restrictionIndependent_of_isDissociated",
    "Graphon.InfiniteExchangeableGraphLaw.isDissociated_iff_vertexTailTrivial",
    "Graphon.InfiniteExchangeableGraphLaw.tfae_extremality",
    "GraphonSpace.limitGraphon_relabel",
    "GraphonSpace.measurable_limitGraphon_invariantAlgebra",
    "InfiniteGraph.vertexTailAlgebra_le_invariantAlgebra",
    "Graphon.InfiniteExchangeableGraphLaw.measure_invariant_eq_zero_or_one_of_restrictionIndependent",
    "Graphon.InfiniteExchangeableGraphLaw.tfae_ergodic_extremality",
    "Graphon.InfiniteExchangeableGraphLaw.invariant_ae_eq_limitGraphon_classifier",
    "RelSignature.RelStructure.restrict_pad",
    "RelSignature.RelStructure.restrictLE_restrictFin",
    "RelSignature.generateFrom_cylinders_eq",
    "RelSignature.RelStructure.ext_of_map_restrictFin",
    "digraphStructureEquiv",
    "finiteDigraphEquiv",
    "InfiniteDigraph.ext_of_map_restrictFin",
    "RelSignature.continuous_restrictFin",
    "RelSignature.continuous_pad",
    "RelSignature.measurable_restrict",
    "RelSignature.RelExchangeableLaw.marginal_map_restrictLE",
    "RelSignature.restrict_comp_pad",
    "RelSignature.RelExchangeableLaw.paddedLaw_map_restrictFin",
    "RelSignature.RelExchangeableLaw.infiniteLaw_map_restrictFin",
    "RelSignature.RelExchangeableLaw.infiniteLaw_map_restrict",
    "RelSignature.RelExchangeableLaw.infiniteLaw_map_relabel",
    "RelSignature.relExchangeableLawEquiv",
    "digraphStructureEquiv_comap",
    "digraphLawEquiv",
    "exchangeableDigraphLawEquiv",
    "exchangeableDigraphLawEquiv_marginal_toPMF",
    "MeasureTheory.Digraphon.ext",
    "MeasureTheory.Digraphon.measurable_simplexRep",
    "MeasureTheory.Digraphon.simplexRep_nonneg",
    "MeasureTheory.Digraphon.simplexRep_sum_eq_one",
    "MeasureTheory.Digraphon.simplexRep_swap",
    "MeasureTheory.Digraphon.simplexRep_ae_eq",
    "MeasureTheory.Digraphon.pairPMF_apply",
    "MeasureTheory.Digraphon.pairPMF_swap",
    "MeasureTheory.Digraphon.measurable_catOutcome",
    "MeasureTheory.Digraphon.measurable_catOutcome_joint",
    "MeasureTheory.Digraphon.uniform01_map_catOutcome",
    "MeasureTheory.Digraphon.uniform01_catOutcome_singleton",
    "OffDiagPairIndex.mk_symm",
    "MeasureTheory.Measure.infinitePi_map_comp_of_injective",
    "MeasureTheory.Digraphon.samplerSource_forall_sampleAdj",
    "MeasureTheory.Digraphon.map_sampleInfinite_eq_equiv_law",
    "MeasureTheory.Digraphon.map_sampleFinite_pair_disjoint",
    "MeasureTheory.Digraphon.ofFun_simplexRep_ae",
    "MeasureTheory.Digraphon.map_sampleFinite_ofGraphon",
    "MeasureTheory.Digraphon.ofTournament_sample_isTournament",
    "MeasureTheory.Digraphon.sampleEventIntegrand_ofKernel_ae",
    "Graphon.card_noninjective_div_card_le",
    "Graphon.card_filter_injective_eq_descFactorial",
    "SimpleGraph.tInj_le_one",
    "SimpleGraph.tInd_le_one",
    "Graphon.homDensity_ofSimpleGraphOn_eq_t",
    "Graphon.sampleMass_ofSimpleGraphOn_eq_pullbackCount_div",
    "SimpleGraph.tInj_eq_sum_tInd",
    "SimpleGraph.tInd_eq_sum_neg_one_pow_tInj",
    "RelSignature.InfiniteRelExchangeableLaw.law_map_restrict",
    "RelSignature.RelStructure.iSup_initialAlgebra_eq",
    "RelSignature.InfiniteRelExchangeableLaw.map_blockPair_snd",
    "RelSignature.InfiniteRelExchangeableLaw.IsDissociated.map_restrict_pair",
    "RelSignature.RelStructure.iSup_tailWindowAlgebra_eq",
    "RelSignature.isDissociated_iff_restrictionIndependent",
    "RelSignature.InfiniteRelExchangeableLaw.RestrictionIndependent.vertexTailTrivial",
    "MeasureTheory.tendsto_eLpNorm_condExp_iInf",
    "RelSignature.isDissociated_iff_vertexTailTrivial",
    "RelSignature.isErgodic_iff_isDissociated",
    "RelSignature.InfiniteRelExchangeableLaw.isErgodic_iff_mem_extremePoints",
    "RelSignature.tfae_extremality",
    "RelSignature.mem_invariantProbabilityMeasures_iff_exists_law",
    "RelSignature.RelCoord.pattern_map",
    "RelSignature.LatentIndex.map_injective",
    "RelSignature.patternLatentIndexEquivCoord",
    "RelSignature.CoordLatentIndex.congrMap",
    "RelSignature.CoordLatentIndex.congrMap_toLatentIndex",
    "RelSignature.RelKernelFamily.measurable_evalStructure",
    "RelSignature.RelKernelFamily.evalStructure_relabel",
    "MeasureTheory.Measure.infinitePi_map_comp_equiv",
    "MeasureTheory.Measure.infinitePi_map_prodMk_of_disjoint",
    "RelSignature.LatentIndex.relabelEquiv",
    "RelSignature.RelKernelFamily.eval_comap",
    "RelSignature.latentSource_map_relabel",
    "RelSignature.RelKernelFamily.evalMeasure_map_relabel",
    "RelSignature.RelKernelFamily.evalLaw",
    "RelSignature.LatentIndex.map_ne_map_of_disjoint",
    "RelSignature.RelKernelFamily.evalMeasure_map_restrict",
    "RelSignature.RelKernelFamily.evalMeasure_map_blockPair",
    "RelSignature.RelKernelFamily.evalLaw_isDissociated",
    "ProbabilityTheory.Kernel.exists_measurable_map_eq_uniform01",
    "MeasureTheory.Measure.exists_measurable_map_eq_uniform01",
    "RelSignature.RelStructure.fixingAlgebra_mono",
    "RelSignature.RelStructure.fixingAlgebra_empty",
    "RelSignature.RelStructure.fixingAlgebra_comap_relabel",
    "RelSignature.RelStructure.fixingAlgebra_comap_relabel_of_fintype",
    "Graphon.abs_homDensity_ofSimpleGraphOn_sub_tInj_le",
    "Graphon.abs_sampleMass_ofSimpleGraphOn_sub_tInd_le",
    "MeasureTheory.Digraphon.sampleAdj_pair_of_lt",
    "MeasureTheory.Digraphon.measurable_sampleInfinite",
    "MeasureTheory.Digraphon.measurable_sampleFinite",
    "RelSignature.InfiniteRelExchangeableLaw.condIndep_fixingAlgebra",
    "MeasureTheory.Measure.MeasureDense.exists_generateFrom_ae_eq_of_ne_top",
    "MeasureTheory.Measure.MeasureDense.exists_generateFrom_ae_eq",
    "MeasureTheory.measure_symmDiff_threshold_le",
    "MeasurableSpace.comap_mapNatBool",
    "MeasureTheory.isSeparable_trim",
    "MeasureTheory.exists_measurable_comap_ae_generates",
    "RelSignature.CoherentBasis.exists_comap_factorMap_ae_eq",
    "RelSignature.CoherentBasis.measurable_factorMap",
    "RelSignature.BasisExpr.eval_mem",
    "RelSignature.BasisExpr.act_mul",
    "RelSignature.BasisExpr.anchorOf_act",
    "RelSignature.BasisExpr.eval_act",
    "RelSignature.SaturatedAtom.act_mul",
    "RelSignature.SaturatedAtom.anchor_act",
    "RelSignature.SaturatedAtom.event_act",
    "RelSignature.SaturatedAtom.event_mem",
    "MeasureTheory.Measure.MeasureDense.mono",
    "RelSignature.measureDense_seedOf",
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


def parse_axiom_report(out: str) -> dict:
    """Parse `#print axioms` output into {declaration: set-of-axioms}.

    Lazy `(.+?)` (not `[^']+`) so that primed declaration names, e.g.
    `hasSubgaussianMGF_of_bounded_differences'`, keep their trailing prime. No `re.DOTALL`:
    the name must stay single-line, otherwise a preceding "does not depend on any axioms"
    line is swallowed into the next name; the multi-line axiom list is still captured
    because `[^\\]]*` matches newlines."""
    reported = {}
    for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]", out):
        reported[m.group(1)] = {a.strip() for a in m.group(2).replace("\n", " ").split(",")
                                if a.strip()}
    for m in re.finditer(r"'(.+?)' does not depend on any axioms", out):
        reported[m.group(1)] = set()
    return reported


def _regression_check_axiom_parse() -> None:
    """Regression fixture (issue #104 R1b): an axiom-free line immediately followed by a
    with-axioms line must parse as two distinct declarations, not one swallowed name."""
    sample = ("'A.free' does not depend on any axioms\n"
              "'A.used' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n")
    rep = parse_axiom_report(sample)
    assert set(rep) == {"A.free", "A.used"}, f"axiom-parse regression: {set(rep)}"
    assert rep["A.free"] == set()
    assert rep["A.used"] == {"propext", "Classical.choice", "Quot.sound"}


def axiom_audit() -> bool:
    _regression_check_axiom_parse()
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
    reported = parse_axiom_report(out)
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
