import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.CFC.CFCv2

attribute [-instance] AlgHom.instContinuousLinearMapClassToSemiringToDivisionSemiringToSemifieldToFieldToTopologicalSpaceToUniformSpaceToPseudoMetricSpaceToSeminormedRingToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToTopologicalSpaceToUniformSpaceToPseudoMetricSpaceToSeminormedRingToSeminormedCommRingToNormedCommRingToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocCommSemiringToNonUnitalNonAssocCommRingToNonUnitalCommRingToNonUnitalSeminormedCommRingToModuleToSeminormedAddCommGroupToNonUnitalSeminormedRingToNonUnitalNormedRingToNormedSpace'ToModuleToSeminormedAddCommGroupToNonUnitalSeminormedRingToNormedSpace
attribute [-instance] StarAlgHom.instContinuousLinearMapClassComplexInstSemiringComplexToTopologicalSpaceToUniformSpaceToPseudoMetricSpaceToSeminormedRingToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToTopologicalSpaceToUniformSpaceToPseudoMetricSpaceToSeminormedRingToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToModuleInstNormedFieldComplexToSeminormedAddCommGroupToNonUnitalSeminormedRingToNonUnitalNormedRingToNormedSpace'ToModuleToSeminormedAddCommGroupToNonUnitalSeminormedRingToNonUnitalNormedRingToNormedSpace'

noncomputable section

section prereqs

variable {A : Type*} [NormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]
variable {B : Type*} [NormedRing B] [StarRing B] [CstarRing B] [CompleteSpace B]
variable [NormedAlgebra ℂ B] [StarModule ℂ B]

lemma StarAlgEquiv.nnnorm_map (φ : A ≃⋆ₐ[ℂ] B) (a : A) : ‖φ a‖₊ = ‖a‖₊ := by
  have : spectralRadius ℂ (φ (star a * a)) = spectralRadius ℂ (star a * a) := by
    rw [spectralRadius, spectralRadius]
    congr!
    exact AlgEquiv.spectrum_eq φ (star a * a)
  iterate 2 rw [IsSelfAdjoint.spectralRadius_eq_nnnorm] at this
  · norm_cast at this
    simpa [CstarRing.nnnorm_star_mul_self, map_star, ←sq]
  · exact IsSelfAdjoint.star_mul_self a
  · simpa only [map_mul, map_star] using IsSelfAdjoint.star_mul_self (φ a)

lemma StarAlgEquiv.norm_map (φ : A ≃⋆ₐ[ℂ] B) (a : A) : ‖φ a‖ = ‖a‖ :=
  congr_arg NNReal.toReal (φ.nnnorm_map a)

lemma StarAlgEquiv.isometry (φ : A ≃⋆ₐ[ℂ] B) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ φ.norm_map

end prereqs

section Normal

variable {A : Type*} [NormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

-- yes, we have all the necessary assumptions
example (a : A) [IsStarNormal a] : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] elementalStarAlgebra ℂ a :=
  continuousFunctionalCalculus a

-- we want this instance
instance {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [CompleteSpace A]
    [NormedAlgebra 𝕜 A] [ProperSpace 𝕜] (a : A) : CompactSpace (spectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| spectrum.isCompact a

instance : CFC ℂ (IsStarNormal : A → Prop) where
  toStarAlgHom {a} ha := (elementalStarAlgebra ℂ a).subtype.comp <| continuousFunctionalCalculus a
  hom_closedEmbedding {a} ha :=
    isometry_subtype_coe.comp (continuousFunctionalCalculus a).isometry |>.closedEmbedding
  hom_map_id {a} ha := congr_arg Subtype.val <| continuousFunctionalCalculus_map_id a
  hom_map_spectrum {a} ha f := by
    simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
    rw [← StarSubalgebra.spectrum_eq (elementalStarAlgebra.isClosed ℂ a),
      AlgEquiv.spectrum_eq (continuousFunctionalCalculus a), ContinuousMap.spectrum_eq_range]
  hom_predicate_preserving {a} ha f := ⟨by rw [← map_star]; exact Commute.all (star f) f |>.map _⟩

lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reClm where
  rightInvOn _x hx := ha.mem_spectrum_eq_re hx |>.symm
  left_inv := Complex.ofReal_re

/-- An element in a C⋆-algebra is selfadjoint if and only if it is normal and its spectrum is
contained in `ℝ`. -/
lemma isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ SpectrumRestricts a Complex.reClm := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ha.spectrumRestricts⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  classical
  rw [isSelfAdjoint_iff]
  nth_rw 2 [← cfcBare_id ha₁ (R := ℂ)]
  rw [← cfcBare_star ha₁ (R := ℂ)]
  refine cfcBare_eq_of_eqOn fun x hx ↦ ?_
  obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
  exact Complex.conj_ofReal _

instance : CFC ℝ (IsSelfAdjoint : A → Prop) :=
  cfc_of_spectrumRestricts (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reClm
    Complex.isometry_ofReal (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts)
    (fun _ _ ↦ inferInstance)

end Normal

section PrePositive


open NNReal ENNReal

def ContinuousMap.toNNReal : C(ℝ, ℝ≥0) := .mk Real.toNNReal continuous_real_toNNReal

@[simp]
lemma ContinuousMap.coe_toNNReal : ⇑ContinuousMap.toNNReal = Real.toNNReal := rfl

-- MOVE ME
lemma spectrumRestricts_nnreal_iff {A : Type*} [Ring A] [Algebra ℝ A] {a : A} :
    SpectrumRestricts a ContinuousMap.toNNReal ↔ ∀ x ∈ spectrum ℝ a, 0 ≤ x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact spectrumRestricts_of_subset_range_algebraMap _ _ (fun _ ↦ Real.toNNReal_coe)
      fun x hx ↦ ⟨⟨x, h x hx⟩, rfl⟩

-- MOVE ME
lemma spectrumRestricts_real_iff {A : Type*} [Ring A] [Algebra ℂ A] {a : A} :
    SpectrumRestricts a Complex.reClm ↔ ∀ x ∈ spectrum ℂ a, x = x.re := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    simp
  · exact spectrumRestricts_of_subset_range_algebraMap _ _ Complex.ofReal_re
      fun x hx ↦ ⟨x.re, (h x hx).symm⟩

-- MOVE ME
lemma spectrumRestricts_nnreal_iff_spectralRadius_le {A : Type*} [Ring A] [Algebra ℝ A]
    {a : A} {t : ℝ≥0} (ht : spectralRadius ℝ a ≤ t) :
    SpectrumRestricts a ContinuousMap.toNNReal ↔ spectralRadius ℝ (algebraMap ℝ A t - a) ≤ t := by
  have : spectrum ℝ a ⊆ Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← coe_nnnorm, NNReal.coe_le_coe,
      ← ENNReal.coe_le_coe]
    exact le_iSup₂ (α := ℝ≥0∞) x hx |>.trans ht
  rw [spectrumRestricts_nnreal_iff]
  refine ⟨fun h ↦ iSup₂_le fun x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ spectrum ℝ a, ↑t - y = x := by simpa using hx
    obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp <| this hy
    lift y to ℝ≥0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : ∀ x ∈ spectrum ℝ a, ‖t - x‖₊ ≤ t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    peel h with x hx h_le
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_le] at h_le
    linarith [h_le.2]

-- MOVE ME
@[to_additive]
theorem Isometry.nnnorm_map_of_map_one {E F : Type*} [SeminormedGroup E] [SeminormedGroup F]
    {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
  Subtype.ext <| hi.norm_map_of_map_one h₁ x

-- MOVE ME
instance {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] : NormedAlgebra ℝ A where
  norm_smul_le r a := by simpa using norm_smul_le (r : ℂ) a

-- MOVE ME
lemma SpectrumRestricts.spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAlgebra 𝕜₂ A] [Algebra 𝕜₁ 𝕜₂] [IsScalarTower 𝕜₁ 𝕜₂ A]
    {f : 𝕜₂ → 𝕜₁} (h_isom : Isometry (algebraMap 𝕜₁ 𝕜₂)) {a : A} (h : SpectrumRestricts a f) :
    spectralRadius 𝕜₁ a = spectralRadius 𝕜₂ a := by
  rw [spectralRadius, spectralRadius]
  apply le_antisymm
  all_goals apply iSup₂_le fun x hx ↦ ?_
  · have := h_isom.nnnorm_map_of_map_zero (map_zero _) x
    refine (congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) this).symm.trans_le <| le_iSup₂ (α := ℝ≥0∞) _ ?_
    exact (spectrum.algebraMap_mem_iff _ _).mpr hx
  · have ⟨y, hy, hy'⟩ := h.algebraMap_image.symm ▸ hx
    subst hy'
    rw [h_isom.nnnorm_map_of_map_zero (map_zero _)]
    exact le_iSup₂ (α := ℝ≥0∞) y hy

-- MOVE ME
protected lemma IsSelfAdjoint.algebraMap {R : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [StarRing R] [StarMul A] [StarModule R A] {r : R} (hr : IsSelfAdjoint r) :
    IsSelfAdjoint (algebraMap R A r) := by
  rw [isSelfAdjoint_iff, ← algebraMap_star_comm]
  exact congr(algebraMap R A $(hr.star_eq))

variable {A : Type*} [NormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

lemma spectrumRestricts_nnreal_iff_nnnorm {a : A} {t : ℝ≥0} (ha : IsSelfAdjoint a)
    (ht : ‖a‖₊ ≤ t) : SpectrumRestricts a ContinuousMap.toNNReal ↔ ‖algebraMap ℝ A t - a‖₊ ≤ t := by
  have : IsSelfAdjoint (algebraMap ℝ A t - a) := IsSelfAdjoint.algebraMap A (.all (t : ℝ)) |>.sub ha
  rw [← ENNReal.coe_le_coe, ← IsSelfAdjoint.spectralRadius_eq_nnnorm,
    ← SpectrumRestricts.spectralRadius_eq (f := Complex.reClm) (algebraMap_isometry ℝ ℂ)] at ht ⊢
  exact spectrumRestricts_nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

lemma SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a)
    (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.toNNReal)
    (hb₂ : SpectrumRestricts b ContinuousMap.toNNReal) :
    SpectrumRestricts (a + b) ContinuousMap.toNNReal := by
  rw [spectrumRestricts_nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b), NNReal.coe_add,
    map_add, add_sub_add_comm]
  refine nnnorm_add_le _ _ |>.trans ?_
  gcongr
  all_goals rw [← spectrumRestricts_nnreal_iff_nnnorm]
  all_goals first | rfl | assumption

lemma IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts (a ^ 2) ContinuousMap.toNNReal := by
  classical
  rw [spectrumRestricts_nnreal_iff, ← cfc_id ha (R := ℝ), ← map_pow, cfc_map_spectrum ha]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

open ComplexStarModule

-- MOVE ME
lemma star_mul_self_add_self_mul_star {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (a : A) :
    star a * a + a * star a = 2 • ((ℜ a) ^ 2 + (ℑ a) ^ 2) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • ((ℜ a) ^ 2 + (ℑ a) ^ 2) := by
      simp [mul_add, add_mul, smul_smul, two_smul, sq]
      abel

lemma SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a)
    (ha₁ : SpectrumRestricts a ContinuousMap.toNNReal) (ha₂ : SpectrumRestricts (-a) ContinuousMap.toNNReal) :
    a = 0 := by
  nontriviality A
  rw [spectrumRestricts_nnreal_iff] at ha₁ ha₂
  classical
  apply eq_zero_of_spectrum_eq_zero (R := ℝ) ha
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, ?_⟩
  · exact ha.spectrumRestricts.image.symm ▸ (spectrum.nonempty a).image _
  · simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
    peel ha₁ with x hx _
    linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

-- Move Me
lemma SpectrumRestricts.of_spectrum_eq  {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra S A] [Algebra R A] [Algebra R S] [IsScalarTower R S A] {a b : A} {f : S → R}
    (ha : SpectrumRestricts a f) (h : spectrum S a = spectrum S b) :
    SpectrumRestricts b f where
  rightInvOn := h ▸ ha.rightInvOn
  left_inv := ha.left_inv

lemma SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra ℝ A] {a : A}
    (ha : SpectrumRestricts a ContinuousMap.toNNReal) {r : ℝ} (hr : 0 ≤ r) :
    SpectrumRestricts (r • a) ContinuousMap.toNNReal := by
  rw [spectrumRestricts_nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp [hr'] at hx ⊢
    exact hx.symm.le
  · lift r to ℝˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def, spectrum.unit_smul_eq_smul, Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

lemma spectrum_star_mul_self_nonneg {b : A} : ∀ x ∈ spectrum ℝ (star b * b), 0 ≤ x := by
  set a := star b * b
  classical
  let a_neg : A := cfc a (- ContinuousMap.id ℝ ⊔ 0)
  set c := b * a_neg
  have h_eq_a_neg : - (star c * c) = a_neg ^ 3 := by
    simp (config := { zeta := false }) only [c, a_neg, star_mul]
    rw [← mul_assoc, mul_assoc _ _ b, ← map_star, ← cfc_id (IsSelfAdjoint.star_mul_self b) (R := ℝ),
      ← map_mul, ← map_mul, ← map_pow, ← map_neg]
    congr
    ext x
    by_cases hx : x ≤ 0
    · rw [← neg_nonneg] at hx
      simp [sup_eq_left.mpr hx, pow_succ']
    · rw [not_le, ← neg_neg_iff_pos] at hx
      simp [sup_eq_right.mpr hx.le]
  have h_c_spec₀ : SpectrumRestricts (- (star c * c)) ContinuousMap.toNNReal := by
    simp only [spectrumRestricts_nnreal_iff, h_eq_a_neg, ← map_pow,
      cfc_map_spectrum (IsSelfAdjoint.star_mul_self b)]
    rintro - ⟨x, -, rfl⟩
    simp
  have c_eq := star_mul_self_add_self_mul_star c
  rw [← eq_sub_iff_add_eq', sub_eq_add_neg] at c_eq
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.toNNReal := by
    rw [c_eq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
    · exact IsSelfAdjoint.smul (by rfl) <| ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
    · exact (IsSelfAdjoint.star_mul_self c).neg
    · rw [nsmul_eq_smul_cast ℝ]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
        (ℑ c).2.sq_spectrumRestricts |>.smul_of_nonneg <| by norm_num
  have h_c_spec₂ : SpectrumRestricts (star c * c) ContinuousMap.toNNReal := by
    rw [spectrumRestricts_nnreal_iff] at h_c_spec₁ ⊢
    intro x hx
    replace hx := Set.subset_diff_union _ {(0 : ℝ)} hx
    rw [spectrum.nonzero_mul_eq_swap_mul, Set.diff_union_self, Set.union_singleton,
      Set.mem_insert_iff] at hx
    obtain (rfl | hx) := hx
    exacts [le_rfl, h_c_spec₁ x hx]
  have bar := h_c_spec₂.eq_zero_of_neg (.star_mul_self c) h_c_spec₀
  rw [bar, neg_zero] at h_eq_a_neg
  simp (config := {zeta := false}) only [a_neg, ← map_pow, ← map_zero (cfc a (R := ℝ))] at h_eq_a_neg
  have baz := cfc_eqOn_of_eq (IsSelfAdjoint.star_mul_self b) _ _ h_eq_a_neg
  intro x hx
  specialize baz hx
  by_contra! hx'
  rw [← neg_pos] at hx'
  simp [sup_eq_left.mpr hx'.le] at baz
  exact (pow_pos hx' 3).ne baz


end PrePositive


variable {A : Type*} [NormedRing A] [CompleteSpace A]
variable [PartialOrder A] [StarOrderedRing A] [CstarRing A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

lemma nonneg_iff_isSelfAdjoint_and_spectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ SpectrumRestricts a ContinuousMap.toNNReal := by
  refine ⟨fun ha ↦ ?_, ?_⟩
  · rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction' with
    | Hs x hx =>
      obtain ⟨b, rfl⟩ := hx
      simp only
      refine ⟨IsSelfAdjoint.star_mul_self b, ?_⟩
      rw [spectrumRestricts_nnreal_iff]
      exact spectrum_star_mul_self_nonneg
    | H1 =>
      rw [spectrumRestricts_nnreal_iff]
      nontriviality A
      simp
    | Hmul x _ y _ hx hy =>
      exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩
  · rintro ⟨ha₁, ha₂⟩
    classical
    let s := cfc a (.mk Real.sqrt Real.continuous_sqrt)
    have : a = star s * s := by
      rw [← cfc_id ha₁ (R := ℝ)]
      simp only [← map_star, ← map_mul]
      apply cfc_eq_of_eqOn ha₁
      rw [spectrumRestricts_nnreal_iff] at ha₂
      peel ha₂ with x hx _
      simp [Real.mul_self_sqrt this]
    exact this ▸ star_mul_self_nonneg s

open NNReal
instance : CFC ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  cfc_of_spectrumRestricts (q := IsSelfAdjoint) ContinuousMap.toNNReal
    isometry_subtype_coe (fun _ ↦ nonneg_iff_isSelfAdjoint_and_spectrumRestricts)
    (fun _ _ ↦ inferInstance)

end
