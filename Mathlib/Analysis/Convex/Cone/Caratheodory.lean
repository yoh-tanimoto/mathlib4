/-
Copyright (c) 2023 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Module.Submodule.Basic

variable {𝕜 E F G : Type*}

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

/-- Give a set `s` in `E`, `toPointedCone 𝕜 s` is the cone consisting of linear combinations of
elements in `s` with non-negative coefficients. -/
abbrev Set.toPointedCone (𝕜) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (s : Set E) :=
  Submodule.span {c : 𝕜 // 0 ≤ c} s
