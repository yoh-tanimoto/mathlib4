/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Number field discriminant
This file defines the discriminant of a number field.

## Main definitions

* `NumberField.discr`: the absolute discriminant of a number field.

## Main result

* `NumberField.abs_discr_gt_two`: **Hermite-Minkowski Theorem**. A nontrivial number field has
nontrivial discriminant.

## Tags
number field, discriminant
-/

-- TODO. Rewrite some of the FLT results on the disciminant using the definitions and results of
-- this file

namespace NumberField

open Classical NumberField Matrix NumberField.InfinitePlace FiniteDimensional

open scoped Real nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant of a number field. -/
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)

theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) :=
  (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm

theorem discr_ne_zero : discr K ≠ 0 := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, coe_discr]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀, Basis.coe_reindex, Algebra.discr_reindex]

theorem discr_eq_discr_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[ℚ] L) :
    discr K = discr L := by
  let f₀ : 𝓞 K ≃ₗ[ℤ] 𝓞 L := (f.restrictScalars ℤ).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj, coe_discr, Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f,
    ← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap ℤ ℚ _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) L]
  congr
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl

open MeasureTheory MeasureTheory.Measure Zspan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal Complex

theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ := by
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun ℂ _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)
  let N := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K ∘ f.symm)
    RingHom.equivRatAlgHom
  suffices M.map Complex.ofReal = (matrixToStdBasis K) *
      (Matrix.reindex (indexEquiv K).symm (indexEquiv K).symm N).transpose by
    calc volume (fundamentalDomain (latticeBasis K))
      _ = ‖((mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)).det‖₊ := by
        rw [← fundamentalDomain_reindex _ e.symm, ← norm_toNNReal, measure_fundamentalDomain
          ((latticeBasis K).reindex e.symm), volume_fundamentalDomain_stdBasis, mul_one]
        rfl
      _ = ‖(matrixToStdBasis K).det * N.det‖₊ := by
        rw [← nnnorm_real, ← ofReal_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, this,
          det_mul, det_transpose, det_reindex_self]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card {w : InfinitePlace K // IsComplex w} * sqrt ‖N.det ^ 2‖₊ := by
        have : ‖Complex.I‖₊ = 1 := by rw [← norm_toNNReal, norm_eq_abs, abs_I, Real.toNNReal_one]
        rw [det_matrixToStdBasis, nnnorm_mul, nnnorm_pow, nnnorm_mul, this, mul_one, nnnorm_inv,
          coe_mul, ENNReal.coe_pow, ← norm_toNNReal, IsROrC.norm_two, Real.toNNReal_ofNat,
          coe_inv two_ne_zero, coe_ofNat, nnnorm_pow, NNReal.sqrt_sq]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card { w // IsComplex w } * NNReal.sqrt ‖discr K‖₊ := by
        rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_reindex,
          ← coe_discr, map_intCast, ← Complex.nnnorm_int]
  ext : 2
  dsimp only
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.coe_reindex, Function.comp_apply,
    Equiv.symm_symm, latticeBasis_apply, ← commMap_canonical_eq_mixed, Complex.ofReal_eq_coe,
    stdBasis_repr_eq_matrixToStdBasis_mul K _ (fun _ => rfl)]
  rfl


section Hermite

open scoped Polynomial IntermediateField BigOperators

variable (A : Type*) [Field A] [CharZero A]

-- theorem aux1 (S : Set { F : IntermediateField ℚ A // FiniteDimensional ℚ F }) {T : Set ℚ[X]}
--     (hT : T.Finite) (h : ∀ F ∈ S, ∃ P ∈ T, ∃ a : A, a ∈ Polynomial.rootSet P A ∧ F = ℚ⟮a⟯) :
--     S.Finite := by
--   let R := ⋃ P ∈ T, Polynomial.rootSet P A
--   have : Finite R := by
--     rw [Set.finite_coe_iff]
--     refine Set.Finite.biUnion hT ?_
--     intro P _
--     exact Polynomial.rootSet_finite P A
--   let f : S → R := by
--     intro K
--     have : K.val ∈ S := by exact Subtype.mem K
--     have ex := h K (Subtype.mem K)
--     have hPS := ex.choose_spec.1
--     let a := ex.choose_spec.2.choose
--     have ha₁ := ex.choose_spec.2.choose_spec.1
--     refine ⟨a, ?_⟩
--     refine Set.mem_biUnion hPS ha₁
--   have : Function.Injective f := by
--     intro F F' hf
--     have exF := h F (Subtype.mem F)
--     have tF := exF.choose_spec.2.choose_spec.2
--     have exF' := h F' (Subtype.mem F')
--     have tF' := exF'.choose_spec.2.choose_spec.2
--     have : exF.choose_spec.2.choose = exF'.choose_spec.2.choose := by
--       rwa [Subtype.mk_eq_mk] at hf
--     rwa [this, ← tF', Subtype.val_inj, Subtype.val_inj] at tF
--   rw [← Set.finite_coe_iff]
--   refine Finite.of_injective f this

theorem aux2 {B : ℝ≥0} (hB₂ : minkowskiBound K < (convexBodyLtFactor K) * B)
    {w : InfinitePlace K} (hw : IsReal w) :
    ∃ a : 𝓞 K, (∀ z :InfinitePlace K, z a ≤ max 1 B) ∧ ℚ⟮(a:K)⟯ = ⊤ := by
  let f : InfinitePlace K → ℝ≥0 := fun _ => 1
  have : ∀ z, z ≠ w → f z ≠ 0 := sorry
  obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
  obtain ⟨a, h_anz, h_ale⟩ := exists_ne_zero_mem_ringOfIntegers_lt (f := g)
    (by rw [convexBodyLt_volume]; convert hB₂)
  have h_gew  : 1 ≤ w a := by
    have h_nm : (1:ℝ) ≤ |(Algebra.norm ℚ) (a:K)| := by
      rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_coe_int, Int.cast_le]
      exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr h_anz)
    contrapose! h_nm
    rw [← InfinitePlace.prod_eq_abs_norm]
    have : (1:ℝ) = ∏ w : InfinitePlace K, 1 := by
      simp only [Finset.prod_const_one]
    rw [this]
    refine Finset.prod_lt_prod_of_nonempty ?_ ?_ ?_
    · intro w' _
      refine pow_pos ?_ _
      rw [InfinitePlace.pos_iff]
      rwa [ne_eq, ZeroMemClass.coe_eq_zero]
    · intro w' _
      refine pow_lt_one ?_ ?_ ?_
      exact map_nonneg _ _
      by_cases hw' : w' = w
      · rwa [hw']
      · have := h_geqf w' hw' ▸ (h_ale w')
        exact this
      · rw [mult]; split_ifs; norm_num; exact two_ne_zero
    exact Finset.univ_nonempty
  refine ⟨a, ?_, ?_⟩
  · sorry
  · let φ := w.embedding.toRatAlgHom
    have hφ : w = InfinitePlace.mk φ.toRingHom := by
      exact (InfinitePlace.mk_embedding w).symm
    rw [Field.primitive_element_iff_algHom_eq_of_eval ℚ ℂ ?_ (a:K) φ]
    intro ψ hψ
    let w' := InfinitePlace.mk ψ.toRingHom
    have h1 : w' a = w a := by
      rw [← InfinitePlace.norm_embedding_eq w, show w' a = ‖ψ a‖ by rfl, ← hψ]
      sorry
    have h2 : w' = w := by
      by_contra h2
      have := h_geqf w' h2 ▸ (h_ale w')
      rw [h1] at this
      rw [lt_iff_not_le] at this
      exact this h_gew
    rw [hφ, eq_comm, InfinitePlace.mk_eq_iff] at h2
    rw [ComplexEmbedding.isReal_iff.mp, or_self] at h2
    exact congr_arg RingHom.toRatAlgHom h2
    erw [← InfinitePlace.isReal_iff]
    exact hw
    exact fun x ↦ IsAlgClosed.splits_codomain (minpoly ℚ x)
variable (N : ℕ)

theorem aux30 (hK : |discr K| ≤ N) :
    finrank ℚ K ≤ max 1 (Real.log ((9 / 4 : ℝ) * N) / Real.log (3 * π / 4)) := by
  by_cases hN : 1 ≤ N
  · obtain h | h := lt_or_le 1 (finrank ℚ K)
    · refine le_trans ?_ (le_max_right _ _)
      rw [_root_.le_div_iff', ← Real.exp_le_exp, ← Real.rpow_def_of_pos (by positivity),
        Real.exp_log (by positivity), ← inv_mul_le_iff (by positivity), inv_div, Real.rpow_nat_cast]
      · exact le_trans (abs_discr_ge K h) (Int.cast_le (α := ℝ).mpr hK)
      · sorry
    · have : finrank ℚ K = 1 := sorry
      have : K ≃+* ℚ := by
        let b := (finBasisOfFinrankEq ℚ K this).repr
        sorry
      sorry
  · sorry

-- FIXME: make this more general
theorem aux3 : ∃ D : ℕ, ∀ F ∈ {F : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
    haveI :  NumberField F := @NumberField.mk _ _ inferInstance F.prop
    |discr F| ≤ N }, finrank ℚ F ≤ D := by
  sorry

theorem aux4 : ∃ B : ℝ≥0, ∀ F ∈ {F : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
      haveI :  NumberField F := @NumberField.mk _ _ inferInstance F.prop
      |discr F| ≤ N },
    haveI :  NumberField F := @NumberField.mk _ _ inferInstance F.prop
    minkowskiBound F < (convexBodyLtFactor F) * B := sorry

example : {F : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
      haveI :  NumberField F := @NumberField.mk _ _ inferInstance F.prop
      |discr F| ≤ N }.Finite := by
  let S := { F : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
      haveI :  NumberField F := @NumberField.mk _ _ inferInstance F.prop
      |discr F| ≤ N }
  obtain ⟨D, hD⟩ := aux3 A N
  have ex := aux4 A N
  let B := ex.choose
  have hB := ex.choose_spec
  let C := Nat.ceil (max B 1 ^ D * D.choose (D / 2)) -- Use a sup?
  let R := (⋃ (P : ℤ[X]) (_ : P.natDegree ≤ D ∧ ∀ i, P.coeff i ∈ Set.Icc (-C:ℤ) C),
      ((P.map (algebraMap ℤ A)).roots.toFinset.toSet : Set A))
  have hR : Finite R := by
    rw [Set.finite_coe_iff]
    refine Polynomial.bUnion_roots_finite _ _ <| Set.finite_Icc _ _
  have h_gen : ∀ F ∈ S, ∃ α ∈ R, ℚ⟮α⟯ = F := by
      intro F hF
      have : NumberField F := @NumberField.mk _ _ inferInstance F.prop
      by_cases hw : ∃ w : InfinitePlace F, IsReal w
      · obtain ⟨w, hw⟩ := hw
        have := aux2 F (hB F hF) hw
        obtain ⟨α, hα⟩ := this
        have h_minpoly  : minpoly ℚ (α:F.val) =
              Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ (α:F.val)) := by
          refine minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) (S := F.val) ?_
          exact α.prop
        refine ⟨?_, ?_, ?_⟩
        use (α:F.val)
        let P := minpoly ℤ (α:F.val)
        rw [Set.mem_iUnion]
        refine ⟨P, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have : Polynomial.natDegree (minpoly ℤ (α:F.val)) =
              Polynomial.natDegree (minpoly ℚ (α:F.val)) := by
            rw [h_minpoly]
            refine (Polynomial.Monic.natDegree_map ?_ _).symm
            refine minpoly.monic ?_
            exact α.prop
          rw [this]
          refine le_trans (minpoly.natDegree_le _) ?_
          exact hD F hF
        · intro i
          rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
          have := (InfinitePlace.le_iff_le _ _).mp hα.1
          have := Embeddings.coeff_bdd_of_norm_le this i
          refine (Eq.trans_le ?_ <| le_trans this ?_).trans (Nat.le_ceil _)
          · rw [h_minpoly, Polynomial.coeff_map, eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs,
            Int.cast_abs]
          · sorry
        · refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero ?_, ?_⟩
          · exact α.prop
          · have := minpoly.aeval ℤ (α:A)
            convert this
            change P = minpoly ℤ (algebraMap F A (α:F.val))
            refine (minpoly.algebraMap_eq ?_ _).symm
            exact NoZeroSMulDivisors.algebraMap_injective _ A
        · convert congr_arg IntermediateField.lift hα.2
          · rw [IntermediateField.lift_adjoin, Set.image_singleton]
          · exact (IntermediateField.lift_top _ _).symm
      · sorry
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := R) ?_ ?_
  · intro F
    have ex := h_gen F F.prop
    let a := ex.choose
    have := ex.choose_spec.1
    exact ⟨a, this⟩
  · intro F F' hf
    have exF := h_gen F F.prop
    have tF := exF.choose_spec.2
    have exF' := h_gen F' F'.prop
    have tF' := exF'.choose_spec.2
    have : exF.choose = exF'.choose := by
      rwa [Subtype.mk_eq_mk] at hf
    rwa [← this, tF, Subtype.val_inj, Subtype.val_inj] at tF'

end Hermite

end NumberField

namespace Rat

open NumberField

/-- The absolute discriminant of the number field `ℚ` is 1. -/
@[simp]
theorem numberField_discr : discr ℚ = 1 := by
  let b : Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Basis.map (Basis.singleton (Fin 1) ℤ) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr ℚ
    _ = Algebra.discr ℤ b := by convert (discr_eq_discr ℚ b).symm
    _ = Algebra.trace ℤ (𝓞 ℚ) (b default * b default) := by
      rw [Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    _ = Algebra.trace ℤ (𝓞 ℚ) 1 := by
      rw [Basis.map_apply, RingEquiv.toAddEquiv_eq_coe, AddEquiv.toIntLinearEquiv_symm,
        AddEquiv.coe_toIntLinearEquiv, Basis.singleton_apply,
        show (AddEquiv.symm ↑ringOfIntegersEquiv) (1 : ℤ) = ringOfIntegersEquiv.symm 1 by rfl,
        map_one, mul_one]
    _ = 1 := by rw [Algebra.trace_eq_matrix_trace b]; norm_num

alias _root_.NumberField.discr_rat := numberField_discr

end Rat

variable {ι ι'} (K) [Field K] [DecidableEq ι] [DecidableEq ι'] [Fintype ι] [Fintype ι']

/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι ℚ K} {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' := by
  replace h' : ∀ i j, IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b')) i j)
  · intro i j
    convert h' i ((b.indexEquiv b').symm j)
-- Porting note: `simp; rfl` was `simpa`.
    simp; rfl
  classical
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b', discr_of_matrix_vecMul,
    ← one_mul (discr ℚ b), Basis.coe_reindex, discr_reindex]
  congr
  have hint : IsIntegral ℤ ((b.reindex (b.indexEquiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r := by
    have : IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine' isUnit_iff_exists_inv.2 ⟨r', _⟩
    suffices algebraMap ℤ ℚ (r * r') = 1 by
      rw [← RingHom.map_one (algebraMap ℤ ℚ)] at this
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [RingHom.map_mul, hr, hr', ← Matrix.det_mul,
      Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [← RingHom.map_one (algebraMap ℤ ℚ), ← hr]
  cases' Int.isUnit_iff.1 hunit with hp hm
  · simp [hp]
  · simp [hm]
#align algebra.discr_eq_discr_of_to_matrix_coeff_is_integral Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
