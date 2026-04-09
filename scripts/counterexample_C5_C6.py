#!/usr/bin/env python3
"""
Counterexample to `pairOrbitRel_of_pairProfile_eq` (line 4467 in
`Graphon/MatrixDetermination.lean`).

The claim is: for twin-free B with positive W, if two pairs have the same
5-motif `pairProfile`, they are in the same pair orbit under `Aut(B, W)`.

**This is FALSE** for sparse twin-free matrices.

**Witness**: `B := C₅ ⊔ C₆` — the adjacency matrix of the disjoint union of
a 5-cycle and a 6-cycle, on `Fin 11`, with uniform weights `W = 1/11`.

- `B` is symmetric.
- `W > 0`.
- `B` is twin-free (rows are all pairwise distinct because each vertex has
  a unique neighbor set modulo the cycle structure).
- Every vertex has `star0 = 2/11` and `tri0 = 0` (no triangles in either
  cycle), so the 5-motif profile is constant across all vertices and all
  diagonal pairs.
- Pairs `(0, 0)` (in `C₅`) and `(5, 5)` (in `C₆`) have the SAME
  `pairProfile = (2/11, 2/11, 2/11, 0, 0)`.
- But they lie in DIFFERENT orbits: `Aut(C₅ ⊔ C₆) = D₅ × D₆`, which acts
  component-wise. No automorphism swaps a `C₅` vertex with a `C₆` vertex,
  since such a swap would have to carry the 5-cycle to a subgraph of
  `C₆` isomorphic to `C₅` — which doesn't exist.

The earlier test scripts (`vertex_orbit_subclaim.py`,
`cross_term_coherence.py`, `vertex_orbit_minimal_motifs.py`) tested only
dense matrices with entries in `[0.1, 0.9]` and missed this sparse
counterexample.

Running this script prints the explicit witness data and confirms the
counterexample.
"""

import numpy as np


def main() -> None:
    T = 11
    B = np.zeros((T, T))
    # C5 on vertices 0..4
    for i in range(5):
        B[i, (i + 1) % 5] = 1.0
        B[(i + 1) % 5, i] = 1.0
    # C6 on vertices 5..10 (shift indices by 5)
    for i in range(6):
        B[5 + i, 5 + (i + 1) % 6] = 1.0
        B[5 + (i + 1) % 6, 5 + i] = 1.0
    W = np.ones(T) / T

    # Sanity checks
    assert np.allclose(B, B.T), "B must be symmetric"
    assert all(W[i] > 0 for i in range(T)), "W must be positive"

    # Twin-free: no two rows identical
    for a in range(T):
        for b in range(a + 1, T):
            assert not np.allclose(B[a], B[b]), f"twin pair: {a}, {b}"

    # Compute pairProfile at (0, 0) and (5, 5)
    def star0(i: int, j: int) -> float:
        return sum(W[m] * B[i][m] for m in range(T))

    def star1(i: int, j: int) -> float:
        return sum(W[m] * B[j][m] for m in range(T))

    def path(i: int, j: int) -> float:
        return sum(W[m] * B[i][m] * B[m][j] for m in range(T))

    def tri0(i: int, j: int) -> float:
        return sum(
            W[m1] * W[m2] * B[i][m1] * B[i][m2] * B[m1][m2]
            for m1 in range(T)
            for m2 in range(T)
        )

    def tri1(i: int, j: int) -> float:
        return sum(
            W[m1] * W[m2] * B[j][m1] * B[j][m2] * B[m1][m2]
            for m1 in range(T)
            for m2 in range(T)
        )

    def profile(i: int, j: int) -> tuple:
        return (star0(i, j), star1(i, j), path(i, j), tri0(i, j), tri1(i, j))

    p1 = profile(0, 0)
    p2 = profile(5, 5)

    print(f"pairProfile(0, 0) = {tuple(round(x, 6) for x in p1)}")
    print(f"pairProfile(5, 5) = {tuple(round(x, 6) for x in p2)}")
    assert all(
        abs(a - b) < 1e-9 for a, b in zip(p1, p2)
    ), "Profiles must match for this to be a counterexample"

    # Orbit argument: Aut(C5 ⊔ C6) = D5 × D6 acts component-wise.
    # A component-wise action cannot map vertex 0 (in C5) to vertex 5 (in C6),
    # so (0, 0) and (5, 5) are in different pair orbits.
    print()
    print("Aut(C5 ⊔ C6) = D5 × D6 (acts component-wise).")
    print("Orbit of (0, 0) = {(i, i) : i ∈ C5} = {(0,0),(1,1),(2,2),(3,3),(4,4)}")
    print("Orbit of (5, 5) = {(i, i) : i ∈ C6} = {(5,5),...,(10,10)}")
    print()
    print("RESULT: profiles match, but pair orbits differ.")
    print("=> pairOrbitRel_of_pairProfile_eq (line 4467 in MatrixDetermination.lean)")
    print("   is FALSE as stated. The counterexample is sparse (has zero entries).")


if __name__ == "__main__":
    main()
