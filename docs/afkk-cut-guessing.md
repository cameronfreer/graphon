# The AFKK cut-guessing step: informal proof for `guessBlock_integral_le_cutNormDiff`

> **OUTCOME (2026-07-08): the campaign succeeded.** `guessBlock_integral_le_cutNormDiff` and
> the whole First Sampling Lemma chain (`first_sampling_lemma`, `Graphon/SamplingLemma.lean`)
> are proved and axiom-clean; `Graphon/SamplingPointwise.lean` is sorry-free. This note is the
> historical mathematical backbone; status language below describes the state at writing time.

**Status**: mathematical backbone for the Layer-3 campaign of PR #11A (point-sampling,
historical). Target: what was then the single remaining `sorry` in
`Graphon/SamplingPointwise.lean`, `guessBlock_integral_le_cutNormDiff`.

**Sources**: Fekete–Kunszenti-Kovács, *The cut norm and Sampling Lemmas for unbounded
kernels*, arXiv:2203.07581, §6.2 and Appendix §10 (Lemmas 6.2, 6.3, 10.1); Alon–Fernandez de
la Vega–Kannan–Karpinski, JCSS 67 (2003), Lemma 3; Lovász, *Large Networks*, Lemma 10.7.

---

## 1. Statement

Fix a graphon `W` on a standard probability space `(α, μ)`, `ε' > 0`, `U := chosenStep W ε'`,
and `k ≥ 1` (`[NeZero k]`). Write

- `D(x) i j := coreDiff W ε' x i j = clampEval W x i j − clampEval U x i j`, a `k × k`
  matrix-valued function of the sample `x : Fin k → α`, with `|D| ≤ 1` (`abs_coreDiff_le_one`)
  and `D i j = D j i` **pointwise** (min/max indexing; `coreDiff_symm`);
- `π := Measure.pi (fun _ : Fin k ↦ μ)` (iid sample);
- `q := ⌈√k⌉₊`, `Q₀ := guessBlock k` = the first `q` coordinates (`|Q₀| ≤ q`);
- `‖·‖_□ := cutNormDiff W U` (sup over pairs of measurable sets of |rectangle integral|),
  and recall a.e. `D(x) i j = (W − U)(x_{min i j}, x_{max i j})` for `i ≠ j`
  (`ae_coreDiff_eq`).

**Claim.**

```
∫ (1/k²) · max_{A,B ⊆ [k]} |Σ_{i∈A\Q₀} Σ_{j∈B\Q₀} D(x) i j| dπ(x)  +  2|Q₀|/k
    ≤ ‖W−U‖_□ + 8 k^{−1/4}.
```

## 2. Reductions

**Small k.** For `k < 2401 = 7⁴` the claim is trivial: the integrand is ≤ 1
(each rectangle sum ≤ k², times 1/k²; the `hg_le` argument already in the file), so
`LHS ≤ 1 + 2q/k` and `1 + 2q/k ≤ 8k^{−1/4}` holds for all `1 ≤ k ≤ 2400`
(§6, verified exhaustively; in polynomial form `t⁴ + 2t² + 2 ≤ 8t³` on `t = k^{1/4} ∈ [1,7]`,
minimum slack 3 at t = 1). The trivial branch would continue to work up to `k = 3591`, so
`k₀ = 2401` has safety margin but **may not be raised past ~3591**.

Henceforth `k ≥ 2401`, so `t := k^{1/4} ≥ 7`, `1 ≤ q ≤ k`, `√k ≤ q ≤ √k + 1`.

**Fixed block ⇒ free cuts.** Each pair `(A\Q₀, B\Q₀)` is itself a cut, so pointwise

```
max_{A,B} |Σ_{A\Q₀} Σ_{B\Q₀} D|  ≤  max_{A,B} |Σ_A Σ_B D|.                          (H1)
```

After (H1) the deterministic block `Q₀` appears **only** in the LHS cost term `2|Q₀|/k ≤ 2q/k`.
Everything below concerns the free maximum. This is the entire "fixed-Q vs averaged-Q bridge":
no exchangeability or permutation-invariance of `π` is used anywhere.

## 3. Layer 1 — the guessing chain (pointwise, finite combinatorics)

All of §3 is a statement about an arbitrary **fixed** real `k × k` matrix `m` with
`m i j = m j i` and `|m i j| ≤ 1`; no probability. Write `avg_Q` for the uniform average over
`Q ∈ powersetCard q [k]` (all `C(k,q)` subsets of size `q`).

**Sign sets and rules.** For `R ⊆ [k]` let `signSet m R := {i : Σ_{j'∈R} m i j' > 0}`, and for
a pair `(R, R')` let `ruleVal m R R' := Σ_{i ∈ signSet m R'} Σ_{j ∈ signSet m R} m i j`.

**(H5) positive part.** For any `c : [k] → ℝ` and `B ⊆ [k]`:
`Σ_{j∈B} c j ≤ Σ_{j : c j > 0} c j` (drop negative terms, add positive ones).

**(H6) sign mismatch.** For any `c, ĉ : [k] → ℝ`:
`Σ_{c j > 0} c j ≤ Σ_{ĉ j > 0} c j + Σ_j |c j − ĉ j|.`
*Proof:* the two index sets differ only where the signs of `c j, ĉ j` disagree; there
`|c j| ≤ |c j − ĉ j|`. ∎

**(H7) subsample estimator, second moment.** Let `f : [k] → ℝ`, `|f| ≤ 1`, `0 < q ≤ k`,
`S₁ := Σ f`, `S₂ := Σ f²`, and `X(Q) := (k/q) Σ_{i∈Q} f i`. Counting incidences
(`#{Q : i ∈ Q} = C(k−1,q−1)`, `#{Q : i,l ∈ Q} = C(k−2,q−2)` for `i ≠ l`, and the cast
identities `q·C(k,q) = k·C(k−1,q−1)`, `q(q−1)·C(k,q) = k(k−1)·C(k−2,q−2)`):

- `avg_Q X(Q) = S₁`;
- `avg_Q X(Q)² = (k/q) S₂ + (k(q−1)/(q(k−1))) (S₁² − S₂)`  (for `q ≥ 2`; `q = 1` directly),

hence, using `k(q−1) ≤ q(k−1)` (⟺ `q ≤ k`),

```
avg_Q (X(Q) − S₁)² ≤ (k/q) S₂ ≤ k²/q,
```

and by Cauchy–Schwarz on the finite average (`(Σ|g|)² ≤ N Σ g²`),

```
avg_Q |X(Q) − S₁| ≤ k/√q.                                                       (H7c)
```

**(H8) one guessing step (columns).** Fix a cut `(A, B)`. Set `c j := Σ_{i∈A} m i j` and, per
`Q`, `ĉ j := (k/q) Σ_{i∈Q∩A} m i j`. By symmetry of `m`,
`{j : ĉ j > 0} = signSet m (Q∩A)`. Then (H5), (H6), and (H7c) applied per column
(`f i := 1_{i∈A}·m i j`, summed over the `k` columns) give

```
Σ_{i∈A} Σ_{j∈B} m i j ≤ avg_Q [ Σ_{i∈A} Σ_{j ∈ signSet m (Q∩A)} m i j ] + k²/√q.
```

**(H9a) both directions.** Apply (H8) to the pair `(A, B)` (columns, average over `Q`), then —
for each fixed `Q`, with `B₁(Q) := signSet m (Q∩A)` — apply (H8) transposed (rows, average
over `Q'`) to the pair `(A, B₁(Q))`. The final rectangle is
`signSet m (Q'∩B₁(Q)) × signSet m (Q∩A) = ruleVal m (Q∩A) (Q'∩B₁(Q))` with
`Q∩A ∈ Q.powerset`, `Q'∩B₁(Q) ∈ Q'.powerset`. Bounding the data-dependent rule by the max:

```
Σ_A Σ_B m ≤ avg_{Q,Q'} max_{R⊆Q, R'⊆Q'} ruleVal m R R' + 2k²/√q,
```

for **every** cut `(A,B)`, hence for `max_{A,B} Σ_A Σ_B m`.

**(H9b) absolute values.** `|Σ_A Σ_B m| = max(Σ_A Σ_B m, Σ_A Σ_B (−m))`; apply (H9a) to `m`
and `−m` (hypotheses stable) and enlarge both rule maxima to the **signed** rule set
`{±1} × Q.powerset × Q'.powerset` of size `2·4^q`:

```
max_{A,B} |Σ_A Σ_B m| ≤ avg_{Q,Q'} max_{ρ ∈ signedRules Q Q'} ruleVal (ρ.sgn·m) ρ.R ρ.R'
                         + 2k²/√q.                                              (★)
```

**(H9c) bridge gate.** Substituting `m := D(x)` (symmetric pointwise, `|D| ≤ 1`) in (★),
integrating over `x ∼ π`, and combining with (H1): the exact inequality consumed by the
master proof,

```
∫ max_{A,B} |Σ_{A\Q₀}Σ_{B\Q₀} D(x)| dπ
   ≤ avg_{Q,Q'} ∫ max_{ρ} ruleVal (ρ.sgn·D(x)) ρ.R ρ.R' dπ + 2k²/√q.
```

This is proved (in normalized `1/k²` form) **before** any of §4–§5 is attempted.

## 4. Layer 2 — fixed rule, conditional mean ≤ cut norm

Fix `Q, Q'` and set `B := Q ∪ Q'` (`|B| ≤ 2q`), and fix one signed rule
`ρ = (s, R, R')`, `R ⊆ Q`, `R' ⊆ Q'`. Split `π` at the block `B` via the measurable equiv
`e : (Fin k → α) ≃ᵐ (B → α) × (Bᶜ → α)` (`measurePreserving_piEquivPiSubtypeProd`); write
`y` for the block coordinates and `z` for the fresh ones.

**Key locality.** For a fresh coordinate `i ∉ B`, membership `i ∈ signSet (±D(x)) R'`
reads `0 < Σ_{j'∈R'} ±D(x) i j'`, which depends only on `(x_i, x_{R'})` and hence only on
`(z_i, y)` — a **pointwise rule**: `i` belongs iff `z_i ∈ S̄_ρ(y)` for a measurable set
`S̄_ρ(y) ⊆ α` (similarly `T̄_ρ(y)` for the column rule). This is the continuum reading of the
sign sets, exactly Lemma 10.1(A) of the source.

**Conditional mean (H11).** Decompose `ruleVal = Σ_{i,j}` (indicator·indicator·±D):

- **fresh × fresh, `i ≠ j`**: given `y`, the coordinates `z_i, z_j` are iid `μ` and a.e.
  `D(x) i j = (W−U)(x_{min}, x_{max})` (`ae_coreDiff_eq` pushed through `e`), so the section
  integral is `± ∫∫ 1_{S̄}(u) 1_{T̄}(v) (W−U) dμ dμ` — up to the min/max orientation a
  rectangle integral — whose absolute value is ≤ `‖W−U‖_□` (`abs_rectIntegralDiff_le`).
  (The sets `S̄, T̄` depend on the ordered pair `(i,j)` through the orientation; harmless,
  the bound is per pair.) Number of pairs ≤ `k²`.
- **pairs touching `B`**: `|term| ≤ 1`, at most `2|B|k` pairs.
- **diagonal `i = j`**: `|term| ≤ 1`, at most `k` pairs.

Hence, for a.e. `y`:

```
∫_z ruleVal (ρ.sgn·D) ρ.R ρ.R' dπ_F  ≤  k²·‖W−U‖_□ + 2|B|k + k =: M_ρ(y)-bound.   (H11c)
```

## 5. Layer 3 — deviations and the union over rules

**Bounded differences (H12).** Fix `y` and the rule `ρ`. As a function of the fresh
coordinates `z`, changing one coordinate `z_{i₀}`:

- memberships of every other fresh `l` are unchanged (their sign sums use only `(z_l, y)`);
- membership of `i₀` and the matrix row/column of `i₀` change; row contribution lies in
  `[−k, k]`, likewise column.

So the rule value changes by at most `c := 4k`.

**McDiarmid at MGF level (H13).** Mathlib has no McDiarmid/Azuma; we prove the specialized
form needed: for a bounded measurable `f` on a finite product `ν^{⊗n}` with two-point bounded
differences ≤ `c` in each coordinate,

```
∫ exp(t (f − ∫f)) dν^{⊗n} ≤ exp( n (c/2)² t² / 2 )       for all t.
```

*Proof (coordinate peeling).* Induct on `n`. Peel coordinate 0: with
`g(w) := ∫ f(a,w) dν(a)`, factor `f − ∫f = (f(a,w) − g(w)) + (g(w) − ∫g)`. Given `w`, the
section `a ↦ f(a,w)` has range inside an interval of length ≤ `c` (two-point hypothesis), so
by **Hoeffding's lemma** (Mathlib `hasSubgaussianMGF_of_mem_Icc`, sharp constant `((b−a)/2)²`)
the inner factor's conditional MGF is ≤ `exp((c/2)²t²/2)`; the outer function `g` inherits the
same bounded differences (integrate the two-point bound) and `∫g = ∫f`, so the induction
hypothesis applies. The sharp constant `(c/2)²` is **mandatory** — the doubled constant
`c²` blows the §6 budget (total ≈ 9.7 > 8). ∎

**Soft-max (H14).** For finitely many centered variables `Z_ρ` (ρ in a finite set of size
`N ≥ 2`) each with MGF ≤ `exp(σ² t²/2)`, and `t* := √(2 log N / σ²)`:

```
exp(t* · E[max_ρ Z_ρ]) ≤ E[exp(t* max_ρ Z_ρ)]        (Jensen, convexity of exp)
                       = E[max_ρ exp(t* Z_ρ)] ≤ Σ_ρ E[exp(t* Z_ρ)] ≤ N·exp(σ²t*²/2),
```

so `E[max_ρ Z_ρ] ≤ √(2 σ² log N)`. (For `N = 1`, `E Z = 0` directly.) No tail bounds, no
measurable selection of an argmax.

**Per-block assembly (H15).** Fix `(Q,Q')`, `B = Q∪Q'`. Pointwise
`max_ρ Z_ρ ≤ max_ρ M_ρ(y) + max_ρ (Z_ρ − M_ρ(y))` where `M_ρ(y)` is the conditional mean.
Integrate: the first term by (H11c) uniformly in ρ; the second, for every fixed `y`, by
(H14) with `σ² = (#fresh)·(4k/2)² ≤ 4k³` (from H13 + H12) and
`N = |signedRules| = 2·4^{|Q|+|Q'|}·…` — using only `|Q|, |Q'| ≤ q`: `log N ≤ (2q+1) log 2`.
Hence, for every block pair with `|Q|,|Q'| ≤ q`:

```
∫ max_ρ ruleVal dπ ≤ k²·‖W−U‖_□ + 4qk + k + √(2·4k³·(2q+1)·log 2).            (H15)
```

## 6. Layer 4 — rate assembly and the numeric budget

Combine (H1) + (H9c) + (H15) (uniform in `(Q,Q')`, so the average collapses), normalize by
`1/k²`, and add the LHS cost `2|Q₀|/k ≤ 2q/k`:

```
total error ≤ 2q/k + 2/√q + (4qk + k)/k² + √(8k³(2q+1)log 2)/k².
```

With `√k ≤ q ≤ √k+1` and `k ≥ 2401` (`t = k^{1/4} ≥ 7`), the coefficients of `k^{−1/4}`:

| term | value at k = 2401 | asymptotic |
|---|---|---|
| block cost `2q/k` | 0.29 | → 0 |
| L1 chain `2/√q` | 2.00 | 2.00 |
| L2 boundary `(4qk+k)/k²` | 0.57 | → 0 |
| L3 soft-max `√(8k³(2q+1)log2)/k²` | 3.35 | √(16 log 2) ≈ 3.33 |
| **total** | **6.21** | **5.33** |

**Numerically verified** (script in Appendix): worst coefficient **6.24 < 8** over an
exhaustive scan `k ∈ [2401, 2·10⁵]` plus spot checks to `10¹⁰`; trivial branch verified
exhaustively for all `k ∈ [1, 2400]` (worst margin 0.10 at `k = 2400`); trivial branch hard
ceiling `k = 3591`.

## 7. Corrections to the in-file docstrings (to be applied when the proof lands)

The current docstrings of `guessBlock_integral_le_cutNormDiff` and
`coreTerm_expectation_le_cutNormDiff` claim the deterministic first-`⌈√k⌉` block makes the
hypergeometric second moment unnecessary ("the Q-block is exactly independent of the fresh
complement, so no hypergeometric second moment is needed") and sketch an estimator
`(k/|Q|)Σ_{j∈B*∩Q} D`. **Both claims are wrong as written**: after restricting cuts to the
fresh complement, `B* ∩ Q = ∅` and the estimator is vacuous. The actual proof (above) uses
the faithful random-subset average internal to the pointwise inequality (★) — the
sampling-without-replacement second moment (H7) **is** needed, but it is elementary Finset
combinatorics, not measure theory; and the deterministic `guessBlock` enters only through
(H1) and its cardinality.

## 8. Helper map (Lean campaign)

See the session plan for full statements. `D0–D3`: `sgnR`, `signSet`, `ruleVal`,
`signedRules`. `H1–H4`: trivialities (fresh-sup ≤ full-sup; `coreDiff` symmetry/locality;
`|ruleVal| ≤ k²`; `⌈√k⌉₊` arithmetic). `H5–H9c`: §3 (subsection I: hypergeometric moments).
`H10–H12`: §4 + bounded differences. `H13` (subsection II): McDiarmid MGF; `H14`
(subsection III): soft-max. `H15–H19`: §5–§6 assembly, budget (`k₀ = 2401`), small-k branch,
master. All private to `SamplingPointwise.lean`.

## Appendix — budget verification script

```python
import math

def qceil(k):
    r = math.isqrt(k)
    return r if r * r == k else r + 1

def main_branch_error(k):
    q = qceil(k)
    return (2*q/k + 2/math.sqrt(q) + (2*(2*q)*k + k)/k**2
            + math.sqrt(2*(k*(2*k)**2)*(2*q+1)*math.log(2))/k**2)

def rhs(k):
    return 8 * k ** (-0.25)

assert all(1 + 2*qceil(k)/k <= rhs(k) for k in range(1, 2401))          # trivial branch
assert all(main_branch_error(k) <= rhs(k) for k in range(2401, 200001)) # main branch scan
assert max(main_branch_error(k) * k**0.25 for k in range(2401, 200001)) < 6.3
for k in (10**6, 10**8, 10**10):
    assert main_branch_error(k) <= rhs(k)
print("budget OK")
```
