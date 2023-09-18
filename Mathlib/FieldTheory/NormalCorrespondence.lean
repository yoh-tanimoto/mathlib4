import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.NormalClosure

lemma normal_sbgp_iff_stabilizing {F L : Type*}
  [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [FiniteDimensional F L] (K : IntermediateField F L) :
  K.fixingSubgroup.Normal ↔ ∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K := by
  constructor
  · intros hk_normal g x hxk
    have hk_fixing := IsGalois.fixedField_fixingSubgroup K
    rw [← hk_fixing]
    rw [IntermediateField.fixedField]
    rw [FixedPoints.intermediateField]
    rintro ⟨ϕ, hϕ⟩
    change ϕ (g x) = g x
    suffices: g.symm (ϕ (g x)) = x
    · apply_fun g at this
      rw [←AlgEquiv.mul_apply] at this
      simp at this
      exact this
    have := hk_normal.conj_mem ϕ hϕ g.symm ⟨x, hxk⟩
    simpa
  · intro hgfix
    refine' ⟨fun n hn g x ↦ _⟩
    rw [mul_smul, mul_smul]
    have hx := hgfix g.symm x x.mem
    specialize hn ⟨g.symm x, hx⟩
    rw [Subtype.coe_mk] at hn
    change n • g⁻¹ x = g⁻¹ x at hn
    change g (n • g⁻¹ x) = _
    rw [hn]
    exact g.apply_symm_apply x

lemma stabilizing_iff_normal_ext {F L : Type*}
  [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [FiniteDimensional F L] (K : IntermediateField F L) :
  (∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K) ↔ Normal F K := by
  rw [IntermediateField.normal_iff_forall_map_le']
  constructor
  · rintro h g x ⟨y, hy, rfl⟩
    exact h g y hy
  · intro h g x hx
    refine' h g _
    use x
    constructor
    · exact hx
    · rfl

theorem normal_correspondence (F L : Type*)
  [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [FiniteDimensional F L] (K : IntermediateField F L) :
  Normal F K ↔ K.fixingSubgroup.Normal := by
  rw [normal_sbgp_iff_stabilizing, stabilizing_iff_normal_ext]
