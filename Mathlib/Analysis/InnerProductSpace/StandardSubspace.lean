import Mathlib

open Set ContinuousLinearMap
open scoped ComplexInnerProductSpace

section ScalarSMulCLM

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def scalarSMulCLM : ℂ →L[ℂ] H →L[ℝ] H where
  toFun c := c • (id ℝ H)
  map_add' _ _ := Module.add_smul _ _ (id ℝ H)
  map_smul' _ _ := IsScalarTower.smul_assoc _ _ (id ℝ H)

@[simp]
lemma scalarSMulCLM_apply (c : ℂ) (x : H) : scalarSMulCLM H c x = c • x := rfl

noncomputable def scalarSMulCLE (c : ℂ) [h : NeZero c] : H ≃L[ℝ] H where
  toFun := c • (id ℝ H)
  continuous_toFun := by
    have : Continuous (fun (x : H) => c • x) := continuous_const_smul c
    congr
  map_add' x y := by simp
  map_smul' a x := by
    simp only [coe_id', Pi.smul_apply, id_eq, RingHom.id_apply]
    exact smul_comm c a x
  invFun := c⁻¹ • (id ℝ H)
  left_inv := by
    intro x
    simp only [coe_id', Pi.smul_apply, id_eq]
    exact inv_smul_smul₀ h.out x
  right_inv := by
    intro x
    simp only [coe_id', Pi.smul_apply, id_eq]
    refine smul_inv_smul₀ h.out x
  continuous_invFun := by
    have : Continuous (fun (x : H) => c⁻¹ • x) := continuous_const_smul c⁻¹
    congr

@[simp]
lemma scalarSMulCLE_apply (c : ℂ) [NeZero c] (x : H) : scalarSMulCLE H c x = c • x := rfl

lemma IsInvertible_scalarSMulCLM_of_neZero (c : ℂ) [NeZero c] :
    IsInvertible (scalarSMulCLM H c) := by
  use scalarSMulCLE H c
  ext x
  simp

end ScalarSMulCLM

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- variable (S : ClosedSubmodule ℂ H)

-- variable (T : Submodule ℂ H) [IsClosed T.carrier]

-- #synth CompleteSpace T

-- #synth HasOrthogonalProjection T

abbrev mulI (S : ClosedSubmodule ℝ H) := S.map (scalarSMulCLM H Complex.I)

-- maybe use `InnerProductSpace.orthogonal`, but making it to `ClosedSubmodule.orthogonal`?
-- see `Mathlib.Analysis.InnerProductSpace.Projection.Submodule`
-- `Mathlib.Analysis.InnerProductSpace.Orthogonal`

def symplComp (S : Submodule ℝ H) : ClosedSubmodule ℝ H where
  carrier := { x : H | ∀ z : S, ⟪x, z⟫.im = 0 }
  add_mem' {x y} hx hy := by
    intro z
    simp only [inner_add_left, Complex.add_im]
    rw [hx, hy, add_zero]
  zero_mem' := fun y => by simp
  smul_mem' {c x} h := by
    intro z
    simp only [CStarModule.inner_smul_left_real, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [h, mul_zero]
  isClosed' := by
    suffices h : {x : H| ∀ (z : ↥S), ⟪x, z⟫.im = 0} = ⋂ z ∈ S, { x : H | ⟪x, z⟫.im = 0} by
      rw [h]
      apply isClosed_biInter
      intro z hz
      suffices hz : {x | ⟪x, z⟫.im = 0} = ((fun (x : H) => ⟪x, z⟫.im) ⁻¹' {0}) by
        rw [hz]
        exact IsClosed.preimage (by continuity) isClosed_singleton
      ext x
      simp
    ext x
    simp

end Submodule

namespace ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev mulI (S : ClosedSubmodule ℝ H) := S.map (scalarSMulCLM H Complex.I)

@[simp]
lemma mulI_mulI_eq (S : ClosedSubmodule ℝ H) : S.mulI.mulI = S := by
  let I := neZero_iff.mpr Complex.I_ne_zero
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    sorry
    -- note that `S.mulI` is not exactly `Submodule.map` because of closure. need to use
    -- that `(scalarSMulCLM H Complex.I)` is one-to-one.
  · intro h
    sorry

lemma inf_symplComp_eq_symplcomp_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).symplComp = S.mulI.symplComp ⊓ T.mulI.symplComp := by sorry

lemma sup_symplComp_eq_symplcomp_inf (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).symplComp = S.mulI.symplComp ⊔ T.mulI.symplComp := by sorry

end ClosedSubmodule

section StandardSubspace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure StandardSubspace where
  toSubspace : ClosedSubmodule ℝ H
  separating : toSubspace ⊓ toSubspace.mulI = ⊥
  cyclic : (toSubspace ⊔ toSubspace.mulI).closure = ⊤

def mulI (S : StandardSubspace H) : StandardSubspace H where
  toSubspace := S.toSubspace.mulI
  separating := by
    simp only [ClosedSubmodule.mulI_mulI_eq]
    rw [inf_comm]
    exact S.separating
  cyclic := by
    simp only [ClosedSubmodule.mulI_mulI_eq]
    sorry -- need first to show `sup_comm` for ClosedSubmodule through `SemilatticeSup`
    -- rw [sup_comm]
    -- exact S.cyclic

def symplComp (S : StandardSubspace H) : StandardSubspace H where
  toSubspace := S.toSubspace.symplComp
  separating := sorry
  cyclic := sorry

end StandardSubspace
