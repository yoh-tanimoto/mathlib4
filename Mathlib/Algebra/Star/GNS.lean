/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Defs

/-!
# Symmetric linear functionals, representations

-/

open Submodule Quotient

variable {R : Type*} {A : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A]
  [Algebra R A] [StarModule R A]

def IsSymmetric (ψ : A →ₗ[R] R) : Prop := ∀ x y, ψ (star x * y) = ψ (star y * x)

def nullIdeal (ψ : A →ₗ[R] R) : Ideal A where
  carrier := {x : A | ∀ y, ψ (star y * x) = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq]
    intro z
    rw [mul_add, map_add, hx, hy]
    exact AddZeroClass.zero_add 0
  zero_mem' := by simp
  smul_mem' := by
    intro x y hy
    simp only [smul_eq_mul, Set.mem_setOf_eq]
    intro z
    rw [← mul_assoc, ← star_star_mul, hy]

variable (ψ : A →ₗ[R] R)

#synth Module R (A ⧸ nullIdeal ψ)

#check (Quotient.module' (nullIdeal ψ)).smul
