/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
/-!
# Canonial Hilbert space from Inner product space

This file defines a complete inner product space from a preinner product space by
quotienting the null space and taking the completion.

## Main results

- **

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

-/


noncomputable section

open RCLike Real Filter

open Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

open InnerProductSpace.Core

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Nullspace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def nullSpace : Submodule 𝕜 E where
  carrier := {v : E | ‖v‖ = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq] at hy
    simp only [Set.mem_setOf_eq]
    apply le_antisymm _ (norm_nonneg (x+y))
    apply le_trans (norm_add_le x y)
    rw [hx, hy]
    linarith
  zero_mem' := norm_zero
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    rw [norm_smul, hx, mul_zero]

-- use https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Quotient.html#Submodule.hasQuotient
-- to define quotient space, define inner product on it,
-- then make an instance of PreInnerProductSpace.Core

end Nullspace

end
