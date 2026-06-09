# How a failed counterexample search proved square-moment descent (#70 test case)

**Date**: 2026-06-09 · **Commits**: `60cdead` (search harness), `59ddb60` (proof + validation)
**Statement resolved**: `sqMoment_descends_of_rootedProfileEquiv` (`Graphon/SimpleRank.lean`)
**Scripts**: `scripts/falsify_classwise_sqmoment.py`, `scripts/validate_sqmoment_cycle_krylov.py`

## 1. The question

The K=1 simple-graph rank theorem (#70) asks: if two vertices `i, j` of a weighted graph
(`B` symmetric real, `W > 0`) are **rooted-profile equivalent** — every rooted simple-graph
evaluation

```
P_F(v) = Σ_σ Π_u W(σ_u) · Π_{(a,b)∈E(F)} B(τ_a, τ_b)      (root pinned to v)
```

agrees at `i` and `j` — must they lie in the same `(B, W)`-automorphism orbit?

The designated minimal obstruction was the **`W`-weighted square moment**

```
sqMoment(v) = Σ_t W_t · B(v,t)²,
```

a *multigraph* observable (it needs a double edge `v–t`): the simple rooted algebra
visibly produces only `W^k`-weighted (k ≥ 2) coincidences, and a `W`-grading argument
shows no uniform span identity for it can exist (under `W ↦ λW` a profile with `m`
unlabeled vertices scales as `λ^m`, the square moment as `λ¹`, leaving only `K₂`/`K₁`
generators — refuted by generic `B`). For 0/1 matrices `B² = B` makes simple = multigraph
and the proved multigraph machinery closes everything, so the open content was genuinely
**real-weighted**.

Following the falsify-first directive, the session goal was: find a real-weighted
twin-free instance with a rooted-profile-equivalent pair whose square moments differ —
or learn from the failure.

## 2. Instrumentation: making "no solution" mean something

Generic random instances have singleton profile-atoms, so they test nothing. The search
must *construct* instances with profile-equal pairs. Two lessons made the search honest:

1. **L-BFGS on a penalty objective is the wrong instrument.** It stalled at residual
   ~1e-7 *even on a control problem where exact solutions provably exist* (no gap
   requirement; symmetric instances solve it). A stall tells you nothing.
2. **Levenberg–Marquardt on the residual *vector*** (`scipy.optimize.least_squares`)
   converges quadratically near solution manifolds. Calibration: the no-gap control hits
   residual **2.6e-33**, converging to an automorphism point. With that instrument,
   "stuck at 1e-4" versus "1e-30" is a real feasibility signal.

The residual system: normalized profile differences at the pair `(0,1)` over all
connected rooted simple graphs with `m ≤ 3` unlabeled vertices (44 observables;
disconnected graphs add nothing — components without the root contribute constants and
root-gluings multiply profiles), plus one residual pinning `gap = 0.5`. Variables: the
symmetric `B` (entries in `[-1.5, 1.5]`, negatives allowed) and `W ∈ [0.05, 3]`.

## 3. The search dynamics — and what they were saying

**Finding 1: small systems are exactly solvable WITH the gap.** At T=5, 8 of 10 LM
starts reached residual ~1e-30 while holding `gap = 0.5`. So profile equality on all
observables with ≤ 3 unlabeled vertices does **not** pin the square moment. Whatever
pins it lives in larger graphs.

**Finding 2: the killers are always cycles.** Every exact solution, verified against the
full `m ≤ 4` family (772 observables), was separated — and the separating graph was
**cyclic every time, never a tree** (sample: rooted `K₅`; `[(0,1),(1,3),(2,3),(2,4),(3,4)]`;
near-complete graphs on 5 vertices). This matched the theory exactly: the session had
already *proved* (`first_moment_descends_of_rootedProfileEquiv`) that decorated-tree
observables are determined by the atom partition's equitable structure, so trees can never
be the binding constraints.

**Finding 3: a sharp size asymmetry.** The adversarial cutting-plane loop (solve the
working set, verify on the full family, add the worst separator, repeat) went infeasible

- at **T=4 after a single cut**, but
- at **T=5 only after five cuts**, with the worst verification diff shrinking
  geometrically (9.6e-2 → 3.1e-2 → 1.1e-2 → 5.0e-3 → 2.1e-3) before dying.

So the constraint structure was *low-dimensional and cyclic*, and its effective size grew
with `T`. That pattern — "trees free, cycles binding, roughly `T`-many of them needed" —
is the signature of a **Krylov sequence**.

**Finding 4 (the tell): which cycle quantities vanish.** Inspecting an exact `m ≤ 3`
solution at T=5, with `ε := B(0,·) − B(1,·)`, `u := B(0,·) + B(1,·)`,
`M := B·D_W`, and `⟨f,g⟩_W := Σ_t W_t f(t) g(t)`:

```
⟨ε, M¹u⟩_W = +5.2e-18     (triangle imposed at m=2  → zero)
⟨ε, M²u⟩_W = +9.3e-18     (4-cycle imposed at m=3   → zero)
⟨ε, M³u⟩_W = −4.2e-03     (5-cycle NOT imposed      → nonzero)
⟨ε, M⁴u⟩_W = −3.2e-02
⟨ε, M⁵u⟩_W = −4.6e-02
```

The optimizer, given only abstract graph observables, had silently set exactly the
quantities `⟨ε, M^q u⟩_W` for the imposed cycle lengths to machine zero. The rooted
`(q+2)`-cycle difference *is* `⟨ε, M^q u⟩_W`. From there the proof is three lines of
linear algebra.

## 4. The proof

Let `ε = B(i,·) − B(j,·)`, `u = B(i,·) + B(j,·)`, `M = B·D_W` (the weighted adjacency
operator `(Mf)(t) = Σ_s W_s B(t,s) f(s)`), self-adjoint w.r.t. `⟨·,·⟩_W` since `B` is
symmetric. Note `gap := sqMoment(i) − sqMoment(j) = ⟨ε, u⟩_W`.

**Step 1 (cycle difference identity).** For the rooted `(q+2)`-cycle (root plus `q+1`
unlabeled vertices in a ring), expanding the two root-incident edges via
`ρ_i ρ_i − ρ_j ρ_j = ε·ρ_i + ρ_j·ε` and using self-adjointness of the inner path kernel:

```
P_cyc(i) − P_cyc(j) = ⟨ε, M^q u⟩_W        exactly, for every q ≥ 1.
```

Rooted-profile equivalence therefore forces `⟨ε, M^q u⟩_W = 0` for all `q ≥ 1`
(cycle lengths 3, 4, …, `T+2` suffice, by Step 3).

**Step 2 (`u ∈ Im M`).** `u = B(e_i + e_j) = M(D_W^{-1}(e_i + e_j))`, using `W > 0`.
This is the step the 2-cycle (the forbidden double edge, `q = 0`) would have provided
directly; positivity of the node weights substitutes for it.

**Step 3 (spectral step).** `M` self-adjoint ⟹ `Im M ⊥ ker M` ⟹ the kernel component
of `u` vanishes ⟹ `u ∈ span{M^q u : q ≥ 1}` (Vandermonde over the distinct nonzero
eigenvalues; at most `T` powers needed).

**Step 4.** `gap = ⟨ε, u⟩_W = Σ_q c_q ⟨ε, M^q u⟩_W = 0`. ∎

**Hypotheses**: only `B` symmetric and `W > 0`. **No twin-freeness.** The forbidden
multigraph observable (`q = 0`) is recovered from the simple ones (`q ≥ 1`) because `u`
is itself made of rows of `B` — the self-referentiality of the rooted problem is exactly
what closes the gap.

## 5. Validation

`scripts/validate_sqmoment_cycle_krylov.py` re-derives everything on a fresh LM-exact
instance:

- the identity of Step 1 against **ground-truth rooted-cycle profiles** (brute-force
  `Σ_σ` evaluation, no matrix shortcuts): mismatch ≤ 2e-15 relative, `q = 1..5`;
- Step 3 membership: relative residual ~1e-22 (rank 5);
- the gap reconstructed from the `q ≥ 1` cycle data equals the pinned `0.5` exactly —
  i.e., every contribution to the gap is an observable that full rpe kills.

The theorem also retro-dicts the search dynamics quantitatively: `m ≤ 4` graphs supply
only `q ≤ 3`, so at T=5 (up to 5 distinct nonzero eigenvalues) the `m ≤ 4` system stays
transiently feasible, while T=4 dies almost immediately — precisely what the cutting-plane
loop observed. A separately run 2-atom stratum analysis corroborates analytically: there
the triangle difference is literally `W₀ ε₀ · gap`, and the stratum-constrained LM search
collapsed to twins (`a = b = c`), as that identity forces.

## 6. What remains

- **Classwise form** (`classwise_sqMoment_descends`, still sorry'd): for atom-invariant
  `g`, palindromic decorated cycles give `⟨ε, D_g M^q D_g u⟩_W = 0`, reducing the
  classwise gap to `⟨D_g ε, P_{ker M}(D_g u)⟩_W` — zero whenever `det B ≠ 0`. The
  singular-`B` stratum is the only open case.
- **Formalization** of the cycle–Krylov proof: the rooted-cycle evaluation identity
  (`rootedCycleGraph` and `weightedAdj`/`weightedAdjIter` already exist in
  `Graphon/Lovasz.lean`; the evaluation bridge
  `rootedProfile_rootedCycleGraph_eq_closedWalkProfile` is an existing focused sorry
  there) plus the finite-dimensional spectral step
  (`Matrix.IsHermitian.spectral_theorem`), in a separate analysis-importing file to
  avoid the known simp-pollution issue.
- **The lift to the full rank theorem** (`vertexOrbitRel_of_rootedProfileEquiv`): higher
  multigraph moments `Σ_t W_t B(i,t)^k g(t)` should fall to the same mechanism applied to
  Hadamard powers `B^{∘(k−1)}` — theta-graph (multi-internally-disjoint-path) rooted
  observables supply kernels in the algebra generated by ordinary *and* Hadamard products
  of `M`, with `B^{∘(k−1)}(e_i)`-type vectors again in the relevant images. Once all
  multigraph rooted evaluations descend, the proved multigraph Lemma 2.4 chain
  (`tupleEquivMulti_implies_orbit` at K=1) closes #70.

## 7. Method notes (for future falsification sessions)

- A penalty-method stall is not evidence; calibrate the solver on a control where
  solutions exist before reading anything into residual plateaus.
- Adversarial cutting planes against a verification family turn "optimizer failed" into
  "the variety emptied after these specific constraints" — and *which* constraints bind
  is the mathematical signal.
- When exact solutions exist transiently, inspect them: the quantities the optimizer
  silently zeroes are the lemma.
