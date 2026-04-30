/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Graphon.Basic
import Graphon.Step
import Graphon.HomDensity
import Graphon.Pullback
import Graphon.Operations
import Graphon.Operator
import Graphon.CutNorm
import Graphon.CutDistance
import Graphon.Approximation
import Graphon.Counting
import Graphon.Regularity
import Graphon.Compactness
import Graphon.Sampling
import Graphon.Lovasz
import Graphon.MatrixDetermination
import Graphon.InverseCounting
import Graphon.Convergence

/-!
# Graphons in Lean 4

A formalization of graphons — the theory of limits of dense graph sequences —
in Lean 4 using Mathlib.

## Stable core

* `Graphon.Basic` — Graphon definition, symmetry, boundedness
* `Graphon.Pullback` — Pullback under measure-preserving maps
* `Graphon.Step` — Measurable partitions, step functions
* `Graphon.HomDensity` — Homomorphism density definition
* `Graphon.CutNorm` — Cut norm, graphon integrability
* `Graphon.Approximation` — Rectangle averages, cut norm approximation
* `Graphon.CutDistance` — Cut distance, pseudometric properties
* `Graphon.Regularity` — Energy increment, Frieze–Kannan weak regularity lemma
* `Graphon.Counting` — Homomorphism density, counting lemma
* `Graphon.Compactness` — Total boundedness, completeness
* `Graphon.Lovasz` — Connection-matrix algebra scaffolding (Lovász §3)
* `Graphon.MatrixDetermination` — Algebraic determination of step graphons
* `Graphon.InverseCounting` — Inverse counting lemma, convergence equivalence
* `Graphon.Convergence` — Top-level convergence characterization

## Experimental

* `Graphon.Operations` — Pointwise product (direct sum and operator product are future work)
* `Graphon.Operator` — Kernel operator pointwise definition (full L² API is future work)
* `Graphon.Sampling` — Expected edge density (concentration bounds are future work)
-/
