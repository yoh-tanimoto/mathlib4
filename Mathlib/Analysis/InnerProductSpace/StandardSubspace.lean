import Mathlib

open Set ContinuousLinearMap

section ScalarSMulCLM

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarSMulCLM : ℂ →L[ℂ] H →L[ℂ] H where
  toFun c := c • (id ℂ H)
  map_add' _ _ := Module.add_smul _ _ (id ℂ H)
  map_smul' _ _ := IsScalarTower.smul_assoc _ _ (id ℂ H)

end ScalarSMulCLM

section StandardSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : Submodule ℝ H)


-- TODO define various coercions
#check (scalarSMulCLM H Complex.I : H →ₗ[ℂ] H)
#check ((scalarSMulCLM H Complex.I : H →ₗ[ℂ] H) : H →ₗ[ℝ] H)
#check (scalarSMulCLM H Complex.I : H →ₗ[ℝ] H)
#check (scalarSMulCLM H Complex.I : H →L[ℝ] H)

-- TODO use `ClosedSubmodule`
structure standardSubspace where
  toSubspace : Submodule ℝ H
  separating : toSubspace ⊓ (toSubspace.map ((scalarSMulCLM H Complex.I : H →ₗ[ℂ] H) : H →ₗ[ℝ] H))
    ≠ ⊥
  cyclic : (toSubspace ⊔
    (toSubspace.map ((scalarSMulCLM H Complex.I : H →ₗ[ℂ] H) : H →ₗ[ℝ] H))).closure = ⊤

end StandardSubspace
