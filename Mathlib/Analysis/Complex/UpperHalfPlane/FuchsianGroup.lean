import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

open MatrixGroups Matrix SpecialLinearGroup UpperHalfPlane

noncomputable section

-- IsometryEquiv.isometry File
  -- @[simp]


-- IsometricSMul FIle

def IsometricSMul.toMulHom (G X : Type _)
    [Group G] [MetricSpace X] [MulAction G X] [IsometricSMul G X] :
    G →* (X ≃ᵢ X) :=
  { toFun := fun g ↦
    { toFun := fun x ↦ g • x
      invFun := fun x ↦ g⁻¹ • x
      left_inv := by
        intro X
        simp
      right_inv := by
        intro X
        simp
      isometry_toFun := by
        intro x Y
        simp }
    map_one' := by
      ext
      simp
    map_mul' := by
      intro x y
      ext z
      simp [MulAction.mul_smul] }


@[simp]
lemma IsometricSMul.toMulHom_apply (G X : Type _)
    [Group G] [MetricSpace X] [MulAction G X] [IsometricSMul G X] (g : G) (x : X) :
  IsometricSMul.toMulHom G X g x = g • x := by
    rfl


-- SpecialLinearGroup FIle

lemma mem_center_SpecialLinearGroup_two_iff {A : SL(2,ℝ)} :
    A ∈ Subgroup.center SL(2,ℝ) ↔ A = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∨ A = (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Subgroup.mem_center_iff]
    constructor
    swap
    · intro h B ; cases' h with h' h' <;> rw [Subtype.ext_iff] <;> simp only [coe_mul, h', Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
    intro ha
    let S : SL(2, ℝ) := ⟨!![1, 1; 0, 1], by simp only [det_fin_two_of, mul_one, mul_zero, sub_zero]⟩
    let T : SL(2, ℝ) := ⟨!![1, 0; 1, 1], by simp only [det_fin_two_of, mul_one, mul_zero, sub_zero]⟩
    have h₁ : (S * A = A * S) := ha S
    have h₂ : (T * A = A * T) := ha T
    induction' A using SpecialLinearGroup.fin_two_induction with a b c d h₃
    rw [Subtype.ext_iff] at h₁ h₂
    simp only at h₁ h₂ ⊢
    rw [← Matrix.ext_iff] at h₁ h₂ 
    simp only [Fin.forall_fin_two] at h₁ h₂ 
    simp only [coe_mul, cons_mul, vecMul_cons, head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons,
      empty_add_empty, zero_smul, zero_add, empty_mul, Equiv.symm_apply_apply, of_apply, cons_val', cons_val_zero,
      empty_val', cons_val_fin_one, smul_cons, smul_eq_mul, mul_one, smul_empty, mul_zero, add_right_eq_self,
      cons_val_one, head_fin_const, self_eq_add_left, true_and, self_eq_add_right, and_true, add_left_eq_self] at h₁ h₂ 
    rw [h₁.right]
    rw [h₂.left]
    have had : a = d := by
      have := h₁.left.right
      rw [h₂.left] at this
      simp only [zero_add, add_zero] at this 
      rw [this]
    rw [had] 
    rw [h₂.left, h₁.right, had, mul_zero, sub_zero, ← sq, sq_eq_one_iff] at h₃ 
    cases' h₃ with hd hd
    · rw [hd]
      left
      rw [one_fin_two]
    rw [hd]
    right
    rw [one_fin_two]
    simp

instance (n R : Type _) [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R] :
    TopologicalSpace (SpecialLinearGroup n R) := by
  apply TopologicalSpace.induced (β := n → (n → R))
  · exact (fun A i j ↦ A i j)
    -- exact (fun A ↦ (fun i ↦ (fun j ↦ A i j)))
  · infer_instance


-- stays here-----------------

variable (n R : Type _) [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]


def ProjectiveLinearGroup := (SpecialLinearGroup n R)⧸Subgroup.center (SpecialLinearGroup n R)

scoped[MatrixGroups] notation "PSL(" n ", " R ")" => ProjectiveLinearGroup (Fin n) R

instance: Group (ProjectiveLinearGroup n R) := by
  unfold ProjectiveLinearGroup
  infer_instance

instance : TopologicalSpace (ProjectiveLinearGroup n R) := by
  unfold ProjectiveLinearGroup
  apply TopologicalSpace.coinduced (QuotientGroup.mk (s := Subgroup.center (SpecialLinearGroup n R) ))
  infer_instance


structure FuchsianGroup extends Subgroup PSL(2,ℝ) where
  discreteTop : DiscreteTopology carrier


def Action : PSL(2, ℝ) →* (ℍ ≃ᵢ ℍ) := by
  apply QuotientGroup.lift (Subgroup.center SL(2,ℝ)) (IsometricSMul.toMulHom SL(2,ℝ) ℍ )
  intro A hA
  rw [mem_center_SpecialLinearGroup_two_iff] at hA
  ext1 x
  simp only [IsometricSMul.toMulHom_apply, IsometryEquiv.coe_one, id_eq]
  cases' hA with h' h'
  · suffices : A = 1
    · simp only [this, one_smul]
    rw [Subtype.ext_iff, h']
    rfl
  · induction' A using SpecialLinearGroup.fin_two_induction with a b c d h₃
    simp only at h'
    rw [Subtype.ext_iff]
    obtain ⟨z, hz ⟩ := x
    simp only
    change (a * z + b)/(c * z + d)= z
    rw [← Matrix.ext_iff] at h'
    simp only [of_apply, cons_val', empty_val', cons_val_fin_one, Matrix.neg_apply, ne_eq, Fin.forall_fin_two,
      cons_val_zero, cons_val_one, head_cons, one_apply_eq, one_apply_ne, neg_zero, head_fin_const] at h' 
    obtain ⟨ ⟨ha, hb ⟩, ⟨hc, hd ⟩ ⟩ := h'
    rw [ha, hb, hc, hd]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, Complex.ofReal_zero, add_zero, zero_mul,
      zero_add, div_neg, div_one, neg_neg]

instance : SMul PSL(2, ℝ) ℍ where
  smul := fun A x ↦ Action A x

instance :IsometricSMul PSL(2, ℝ) ℍ where
  isometry_smul := by
    intro A
    change Isometry (Action A)
    apply IsometryEquiv.isometry
    --simp

    
