/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Localization.NormTrace

import Mathlib.Sandbox

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

theorem exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a:K)| ≤ FractionalIdeal.absNorm I.1 * (4 / π) ^ NrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  -- The smallest possible value for `exists_ne_zero_mem_ideal_of_norm_le`
  let B := (minkowskiBound K I * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank ℚ K : ℝ))
  have h_le : (minkowskiBound K I) ≤ volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBodySum_volume, ← ENNReal.ofReal_pow (by positivity), ← Real.rpow_nat_cast,
      ← Real.rpow_mul toReal_nonneg, div_mul_cancel, Real.rpow_one, ofReal_toReal, mul_comm,
      mul_assoc, ENNReal.inv_mul_cancel (convexBodySumFactor_ne_zero K)
      (convexBodySumFactor_ne_top K), mul_one]
    · exact mul_ne_top (ne_of_lt (minkowskiBound_lt_top K I))
        (ENNReal.inv_ne_top.mpr (convexBodySumFactor_ne_zero K))
    · exact (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))
  convert exists_ne_zero_mem_ideal_of_norm_le K I h_le
  rw [div_pow B, ← Real.rpow_nat_cast B, ← Real.rpow_mul (by positivity), div_mul_cancel _
    (Nat.cast_ne_zero.mpr <| ne_of_gt finrank_pos), Real.rpow_one, mul_comm_div, mul_div_assoc']
  congr 1
  rw [eq_comm]
  calc
    _ = FractionalIdeal.absNorm I.1 * (2:ℝ)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ *
          (2:ℝ) ^ finrank ℚ K * ((2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K /
            (Nat.factorial (finrank ℚ K)))⁻¹ := by
      simp_rw [minkowskiBound, convexBodySumFactor,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_inv, toReal_div, toReal_mul,
        coe_toReal, toReal_pow, toReal_inv, toReal_ofNat, mixedEmbedding.finrank, toReal_div,
        toReal_ofNat, coe_toReal, coe_real_pi, toReal_nat, mul_assoc]
      rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1))]
    _ = FractionalIdeal.absNorm I.1 * (2:ℝ) ^ (finrank ℚ K - NrComplexPlaces K - NrRealPlaces K +
          NrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) *
            π⁻¹ ^ (NrComplexPlaces K) := by
      simp_rw [inv_div, div_eq_mul_inv, mul_inv, ← zpow_neg_one, ← zpow_coe_nat, mul_zpow,
        ← zpow_mul, neg_one_mul, mul_neg_one, neg_neg, Real.coe_sqrt, coe_nnnorm, sub_eq_add_neg,
        zpow_add₀ (two_ne_zero : (2:ℝ) ≠ 0)]
      ring
    _ = FractionalIdeal.absNorm I.1 * (2:ℝ) ^ (2 * NrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ *
          Nat.factorial (finrank ℚ K) * π⁻¹ ^ (NrComplexPlaces K) := by
      congr
      rw [← card_add_two_mul_card_eq_rank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = FractionalIdeal.absNorm I.1 * (4 / π) ^ NrComplexPlaces K * (finrank ℚ K).factorial *
          Real.sqrt |discr K| := by
      rw [show ‖discr K‖ = |(discr K : ℝ)| by rfl, zpow_mul, show (2:ℝ) ^ (2:ℤ) = 4 by norm_cast,
        div_pow, inv_eq_one_div, div_pow, one_pow, zpow_coe_nat]
      ring

theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr :
    ∃ (a : 𝓞 K), a ≠ 0 ∧
      |Algebra.norm ℚ (a:K)| ≤ (4 / π) ^ NrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  obtain ⟨_, h_mem, h_nz, h_nm⟩ := exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K 1
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  refine ⟨a, ne_zero_of_map h_nz, ?_⟩
  simp_rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h_nm
  exact h_nm

variable {K}

theorem abs_discr_ge (h : 1 < finrank ℚ K) :
    (4 / 9 : ℝ) * (3 * π / 4) ^ finrank ℚ K ≤ |discr K| := by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr K
  have h_nm : (1:ℝ) ≤ |(Algebra.norm ℚ) (x:K)| := by
    rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_coe_int, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr h_nz)
  replace h_bd := le_trans h_nm h_bd
  rw [← inv_mul_le_iff (by positivity), inv_div, mul_one, Real.le_sqrt (by positivity)
    (by positivity), ← Int.cast_abs, div_pow, mul_pow, ← pow_mul, ← pow_mul] at h_bd
  refine le_trans ?_ h_bd
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction an uniform
  -- lower bound for this sequence from which we deduce the result.
  let a : ℕ → ℝ := fun n => (n:ℝ) ^ (n * 2) / ((4 / π) ^ n * (n.factorial:ℝ) ^ 2)
  suffices ∀ n, 2 ≤ n → (4 / 9 : ℝ) * (3 * π / 4) ^ n ≤ a n by
    refine le_trans (this (finrank ℚ K) h) ?_
    simp only -- unfold `a` and beta-reduce
    gcongr
    · exact (one_le_div Real.pi_pos).2 Real.pi_le_four
    · rw [← card_add_two_mul_card_eq_rank, mul_comm]
      exact Nat.le_add_left _ _
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq <| by norm_num [Nat.factorial_two]; field_simp; ring
  | succ m _ h_m =>
      suffices (3:ℝ) ≤ (1 + 1 / m : ℝ) ^ (2 * m) by
        convert_to _ ≤ (a m) * (1 + 1 / m : ℝ) ^ (2 * m) / (4 / π)
        · simp_rw [add_mul, one_mul, pow_succ, Nat.factorial_succ]
          field_simp; ring
        · rw [_root_.le_div_iff (by positivity), pow_succ]
          convert (mul_le_mul h_m this (by positivity) (by positivity)) using 1
          field_simp; ring
      refine le_trans (le_of_eq (by field_simp; norm_num)) (one_add_mul_le_pow ?_ (2 * m))
      exact le_trans (by norm_num : (-2:ℝ) ≤ 0) (by positivity)

/-- **Hermite-Minkowski Theorem**. A nontrivial number field has nontrivial discriminant. -/
theorem abs_discr_gt_two (h : 1 < finrank ℚ K) : 2 < |discr K| := by
  have : Algebra (𝓞 K) K := by exact Subalgebra.toAlgebra (𝓞 K)
  have h₁ : 1 ≤ 3 * π / 4 := by
    rw [_root_.le_div_iff (by positivity), ← _root_.div_le_iff' (by positivity), one_mul]
    linarith [Real.pi_gt_three]
  have h₂ : (9:ℝ) < π ^ 2 := by
    rw [ ← Real.sqrt_lt (by positivity) (by positivity), show Real.sqrt (9:ℝ) = 3 from
    (Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)).mpr (by norm_num)]
    exact Real.pi_gt_three
  refine Int.cast_lt.mp <| lt_of_lt_of_le ?_ (abs_discr_ge h)
  rw [← _root_.div_lt_iff' (by positivity), Int.int_cast_ofNat]
  refine lt_of_lt_of_le ?_ (pow_le_pow_right (n := 2) h₁ h)
  rw [div_pow, _root_.lt_div_iff (by norm_num), mul_pow, show (2:ℝ) / (4 / 9) * 4 ^ 2 = 72 by
    norm_num, show (3:ℝ) ^ 2 = 9 by norm_num, ← _root_.div_lt_iff' (by positivity),
    show (72:ℝ) / 9 = 8 by norm_num]
  linarith [h₂]

section Hermite

open scoped Polynomial IntermediateField BigOperators

variable (A : Type*) [Field A] [CharZero A]

theorem aux1 (S : Set {F : IntermediateField ℚ A // FiniteDimensional ℚ F}) {T : Set A}
    (hT : T.Finite) (h : ∀ F ∈ S, ∃ a ∈ T, F = ℚ⟮a⟯) :
    S.Finite := by
  rw [← Set.finite_coe_iff] at hT
  refine Set.finite_coe_iff.mp <| Finite.of_injective (β := T) (fun ⟨F, hF⟩ ↦ ?_) ?_
  · specialize h F hF
    exact ⟨h.choose, h.choose_spec.1⟩
  · intro F₁ F₂ h_eq
    rw [Subtype.ext_iff_val, Subtype.ext_iff_val]
    convert congr_arg (ℚ⟮·⟯) (Subtype.mk_eq_mk.mp h_eq)
    all_goals exact (h _ (Subtype.mem _)).choose_spec.2

theorem aux2 (B : ℝ≥0) (hB₁ : 1 ≤ B) (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)
    {w : InfinitePlace K} (hw : IsReal w) :
    ∃ a ∈ 𝓞 K, (∀ z : InfinitePlace K, z a ≤ B) ∧ ℚ⟮(a:K)⟯ = ⊤ := by
  obtain ⟨g, h_gf, h_geq⟩ := @adjust_f K  _ (fun _ => 1) _ w B (fun _ _ ↦ by norm_num)
  obtain ⟨a, ha, h_nz, h_le⟩ := exists_ne_zero_mem_ringOfIntegers_lt (f := g)
    (by rw [convexBodyLT_volume]; convert hB)
  have h_lt : ∀ ⦃z⦄, z ≠ w → z a < 1 := fun z hz ↦ by convert h_gf z hz ▸ (h_le z)
  refine ⟨a, ha, fun z ↦ ?_, ?_⟩
  · refine le_of_lt ?_
    by_cases hz : z = w
    · rw [hz, ← h_geq, NNReal.coe_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w),
        Finset.prod_congr rfl (fun z hz ↦ by norm_num [h_gf z (Finset.mem_erase.mp hz).1]) (g := 1)]
      simp_rw [Pi.one_apply, Finset.prod_const_one, NNReal.coe_pow, one_mul, mult]
      split_ifs; norm_num [h_le w]
    · exact lt_of_lt_of_le (h_lt hz) hB₁
  · refine (Field.primitive_element_iff_algHom_eq_of_eval ℚ ℂ ?_ _ w.embedding.toRatAlgHom).mpr ?_
    · exact fun x ↦ IsAlgClosed.splits_codomain (minpoly ℚ x)
    · intro ψ hψ
      suffices w = InfinitePlace.mk ψ.toRingHom by
        rw [(mk_embedding w).symm, mk_eq_iff, conjugate_embedding_eq_of_isReal hw, or_self] at this
        ext x
        exact RingHom.congr_fun this x
      have h : 1 ≤ w (⟨a, ha⟩:(𝓞 K)) := ge_one_of_lt_one (Subtype.ne_of_val_ne h_nz) h_lt
      contrapose! h
      convert h_lt h.symm using 1
      rw [← norm_embedding_eq]
      exact congr_arg (‖·‖) hψ

theorem aux22 (B : ℝ≥0) (hB₁ : 1 ≤ B) {w : InfinitePlace K} (hw : IsComplex w)
    {f : InfinitePlace K → ℝ≥0}
    (hf : ∀ z, z ≠ w → f z = 1)
    (hB : minkowskiBound K 1 < volume (convexBodyLT' K f ⟨w, hw⟩)) :
    ∃ a ∈ 𝓞 K, (∀ z : InfinitePlace K, z a ≤ B) ∧ ℚ⟮(a:K)⟯ = ⊤ := by
  obtain ⟨a, ha, h_nz, h_le, h_w⟩ := exists_ne_zero_mem_ringOfIntegers_lt' K ⟨w, hw⟩ hB
  have h_lt : ∀ ⦃z⦄, z ≠ w → z a < 1 := sorry
  refine ⟨a, ha, fun z ↦ ?_, ?_⟩
  · refine le_of_lt ?_
    by_cases hz : z = w
    · sorry
    · exact lt_of_lt_of_le (h_lt hz) hB₁
  · refine (Field.primitive_element_iff_algHom_eq_of_eval ℚ ℂ ?_ _ w.embedding.toRatAlgHom).mpr ?_
    · exact fun x ↦ IsAlgClosed.splits_codomain (minpoly ℚ x)
    · intro ψ hψ
      have : w = InfinitePlace.mk ψ.toRingHom := by
        have h : 1 ≤ w (⟨a, ha⟩:(𝓞 K)) := ge_one_of_lt_one (Subtype.ne_of_val_ne h_nz) h_lt
        contrapose! h
        convert h_lt h.symm using 1
        rw [← norm_embedding_eq]
        exact congr_arg (‖·‖) hψ
      rw [(mk_embedding w).symm, mk_eq_iff] at this
      have := congr_arg RingHom.toRatAlgHom (this.resolve_right ?_)
      exact this
      have h : 1 ≤ w (⟨a, ha⟩:(𝓞 K)) := ge_one_of_lt_one (Subtype.ne_of_val_ne h_nz) h_lt
      contrapose! h
      have := RingHom.congr_fun h a
      erw [← this] at hψ
      simp at hψ
      have t₀ : (embedding w a).im = 0 := by exact conj_eq_iff_im.mp (id hψ.symm)
      dsimp only
      have : w a = Real.sqrt ((embedding w a).re ^ 2 + (embedding w a).im ^ 2) := by
        rw [← norm_embedding_eq]
        rw [← abs_add_mul_I]
        rw [Complex.norm_eq_abs]
        rw [re_add_im]
      rw [this, t₀, zero_pow, add_zero]
      rwa [Real.sqrt_sq_eq_abs]
      exact zero_lt_two



variable (N : ℕ)

noncomputable def D : ℕ :=
  Nat.ceil (max 1 (Real.log ((9 / 4 : ℝ) * N) / Real.log (3 * π / 4)))

theorem aux30 (hK : |discr K| ≤ N) : finrank ℚ K ≤ D N := by
  sorry
  -- by_cases hN : 1 ≤ N
  -- · obtain h | h := lt_or_le 1 (finrank ℚ K)
  --   · refine le_trans ?_ (le_max_right _ _)
  --     rw [_root_.le_div_iff', ← Real.exp_le_exp, ← Real.rpow_def_of_pos (by positivity),
  --       Real.exp_log (by positivity), ← inv_mul_le_iff (by positivity), inv_div, Real.rpow_nat_cast]
  --     · exact le_trans (abs_discr_ge h) (Int.cast_le (α := ℝ).mpr hK)
  --     · sorry
  --   · have : finrank ℚ K = 1 := sorry
  --     have : K ≃+* ℚ := by
  --       let b := (finBasisOfFinrankEq ℚ K this).repr
  --       sorry
  --     sorry
  -- · sorry

set_option maxHeartbeats 600000 in
example {F : Type*} [Field F] [NumberField F] (hF : |discr F| ≤ N):
    minkowskiBound F 1 < convexBodyLTFactor F * (sqrt N * (2 : ℝ≥0∞) ^ (D N)).toNNReal := by
  rw [minkowskiBound, convexBodyLTFactor, volume_fundamentalDomain_fractionalIdealLatticeBasis,
    Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, ENNReal.ofReal_one, one_mul,
    mixedEmbedding.volume_fundamentalDomain_latticeBasis, mixedEmbedding.finrank,
    toNNReal_mul, toNNReal_pow, toNNReal_coe, coe_mul, ENNReal.coe_pow, coe_toNNReal two_ne_top]
  calc
    _ < (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) * 2 ^ finrank ℚ F := ?_
--    _ ≤ (NNReal.sqrt N) * 2 ^ finrank ℚ F := ?_
    _ ≤ (NNReal.sqrt N) * 2 ^ D N := ?_
    _ < (2:ℝ≥0∞) ^ NrRealPlaces F * pi ^ NrComplexPlaces F * (↑(sqrt N) * 2 ^ D N) := ?_
  ·
    sorry
  · gcongr
    · rw [NNReal.sqrt_le_sqrt_iff]
      sorry
    · exact one_le_two
    · exact aux30 N hF
  · sorry

attribute [-instance] IsDomain.toCancelCommMonoidWithZero IsDomain.toCancelMonoidWithZero

-- attribute [local instance 1001] Algebra.id

set_option trace.profiler true in
open Polynomial in
theorem main : {F : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
      haveI :  NumberField F := @NumberField.mk _ _ inferInstance F.prop
      |discr F| ≤ N }.Finite := by
  let B := (sqrt N * (2 : ℝ≥0∞) ^ (D N)).toNNReal
  let C := Nat.ceil (max B 1 ^ (D N) * Nat.choose (D N) ((D N) / 2))
  let T := {P : ℤ[X] | P.natDegree ≤ D ∧ ∀ i, |P.coeff i| ≤ C}
  have := bUnion_roots_finite (algebraMap ℤ A) (D N) (Set.finite_Icc (-C : ℤ) C)
  refine aux1 A _ this ?_
  rintro ⟨F, hF₁⟩ hF₂
  haveI : NumberField F := @NumberField.mk _ _ inferInstance hF₁
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace F, IsReal w := sorry
  have := aux2 B ?_ ?_ hw
  obtain ⟨a, ha, ha₁, ha₂⟩ := this
  have h_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ ha
  simp_rw [Set.mem_iUnion]
  refine ⟨a, ⟨?_, ?_⟩⟩
  · refine ⟨minpoly ℤ a, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [Field.primitive_element_iff_minpoly_natDegree_eq] at ha₂
          rw [h_minpoly] at ha₂
          rw [Monic.natDegree_map] at ha₂
          · rw [ha₂]
            refine aux30 _ hF₂
          · exact minpoly.monic ha
        · intro i
          rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
          have : ∀ φ : F →+* ℂ, ‖φ a‖ ≤ B := by
            intro φ
            exact ha₁ (InfinitePlace.mk φ)
          refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le this i).trans ?_
          · rw [h_minpoly, coeff_map, eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
          · refine le_trans ?_ (Nat.le_ceil _)
            simp_rw [toNNReal_mul, toNNReal_coe, toNNReal_pow, NNReal.coe_mul, Real.coe_sqrt,
              NNReal.coe_nat_cast, NNReal.coe_pow, val_eq_coe]
            simp_rw [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_max]
            simp_rw [NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_nat_cast, NNReal.coe_pow,
              NNReal.coe_one]
            gcongr
            · exact le_max_right _ _
            · exact aux30 N hF₂
            · refine (Nat.choose_le_choose _ (aux30 N hF₂)).trans ?_
              exact Nat.choose_le_middle _ _
      · refine mem_rootSet.mpr ⟨minpoly.ne_zero ha, ?_⟩
        rw [show (a:A) = algebraMap F A a by rfl]
        rw [aeval_algebraMap_eq_zero_iff]
        exact minpoly.aeval ℤ a
  · convert congr_arg (IntermediateField.map (IntermediateField.val F)) ha₂.symm
    · rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
    · rw [IntermediateField.adjoin_map, IntermediateField.coe_val, Set.image_singleton]
  · sorry
  · sorry
/-     rw [minkowskiBound, convexBodyLTFactor]
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]
    rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one]
    rw [ENNReal.ofReal_one, one_mul, mixedEmbedding.volume_fundamentalDomain_latticeBasis]
    simp_rw [finrank_prod, finrank_fintype_fun_eq_card, toNNReal_mul, toNNReal_coe, toNNReal_pow,
      coe_mul, ENNReal.coe_pow]
    simp only [ne_eq, two_ne_top, not_false_eq_true, coe_toNNReal, Real.coe_sqrt]
    sorry -/

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
