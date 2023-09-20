import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.NormalClosure

lemma normal_sbgp_iff_stabilizing {F L : Type*}
  [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [FiniteDimensional F L] (K : IntermediateField F L) :
  K.fixingSubgroup.Normal ↔ ∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K := by
  constructor
  · intros hk_normal g x hxk
    rw [← IsGalois.fixedField_fixingSubgroup K]
    rintro ⟨ϕ, hϕ⟩
    exact inv_smul_eq_iff.mp (hk_normal.conj_mem ϕ hϕ g⁻¹ ⟨x, hxk⟩)
  · intro hgfix
    refine' ⟨fun n hn g x ↦ _⟩
    replace hn : n • g⁻¹ • (x : L) = g⁻¹ • (x : L) := hn ⟨g.symm x, hgfix g.symm x x.2⟩
    rw [mul_smul, mul_smul, hn, smul_inv_smul]

lemma stabilizing_iff_normal_ext {F L : Type*}
  [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [FiniteDimensional F L] (K : IntermediateField F L) :
  (∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K) ↔ Normal F K := by
  rw [IntermediateField.normal_iff_forall_map_le']
  constructor
  · rintro h g x ⟨y, hy, rfl⟩
    exact h g y hy
  · intro h g x hx
    exact h g ⟨x, hx, rfl⟩

theorem normal_correspondence (F L : Type*)
  [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [FiniteDimensional F L] (K : IntermediateField F L) :
  Normal F K ↔ K.fixingSubgroup.Normal := by
  rw [normal_sbgp_iff_stabilizing, stabilizing_iff_normal_ext]
