/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 01cd9a8d-4981-45c4-aeed-c30d84e75bb9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example : Kᗮᗮ = K
-/

import Mathlib


variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (K : Submodule ℂ H)
  (h : IsClosed (K : Set H))

noncomputable section AristotleLemmas

/-
Assume H is complete.
-/
variable [CompleteSpace H]

end AristotleLemmas

example : Kᗮᗮ = K := by
  rw [ Submodule.orthogonal_orthogonal_eq_closure, IsClosed.submodule_topologicalClosure_eq ] ; assumption