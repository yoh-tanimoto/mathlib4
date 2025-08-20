import Mathlib

open Set ContinuousLinearMap
open scoped ComplexInnerProductSpace

section ScalarSMulCLM

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarSMulCLM : ℂ →L[ℂ] H →L[ℝ] H where
  toFun c := c • (id ℝ H)
  map_add' _ _ := Module.add_smul _ _ (id ℝ H)
  map_smul' _ _ := IsScalarTower.smul_assoc _ _ (id ℝ H)

end ScalarSMulCLM

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def symplComp (S : Submodule ℝ H) : ClosedSubmodule ℝ H where
  carrier := { x : H | ∀ y : S, ⟪x, y⟫.im = 0 }
  add_mem' := sorry
  zero_mem' := fun y => by simp
  smul_mem' := sorry
  isClosed' := sorry

end Submodule

section StandardSubspace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure StandardSubspace where
  toSubspace : ClosedSubmodule ℝ H
  separating : toSubspace ⊓ (toSubspace.map (scalarSMulCLM H Complex.I)) = ⊥
  cyclic : (toSubspace ⊔ toSubspace.map (scalarSMulCLM H Complex.I)).closure = ⊤

def symplComp (S : StandardSubspace H) : StandardSubspace H where
  toSubspace := S.toSubspace.symplComp
  separating := sorry
  cyclic := sorry

end StandardSubspace
