/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Number field discriminant
This file defines the discriminant of a number field.

## Main definitions
 - `discr` the absolute discriminant of a number field.

## Tags
number field, discriminant
-/

-- TODO. Rewrite some of the FLT results on the disciminant using the definitions and results of
-- this file

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

namespace NumberField

open Classical NumberField Matrix NumberField.InfinitePlace FiniteDimensional

open scoped Real

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
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.coe_reindex, Function.comp, Equiv.symm_symm,
    latticeBasis_apply, ← commMap_canonical_eq_mixed, Complex.ofReal_eq_coe,
    stdBasis_repr_eq_matrixToStdBasis_mul K _ (fun _ => rfl)]
  rfl

theorem toto :
    ∃ (a : 𝓞 K), a ≠ 0 ∧
      |Algebra.norm ℚ (a:K)| ≤ (2:ℝ) ^ (finrank ℚ K - NrRealPlaces K : ℤ)
        * π⁻¹ ^ NrComplexPlaces K *
          (finrank ℚ K).factorial * Real.sqrt |discr K| / (finrank ℚ K) ^ (finrank ℚ K)  := by

  let B := ((minkowskiBound K).toReal * (convexBodySumFactor K).toReal⁻¹) ^ (1 / (finrank ℚ K : ℝ))
  have : (minkowskiBound K) ≤ volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBodySum_volume, ← ENNReal.ofReal_pow, ← Real.rpow_nat_cast, ← Real.rpow_mul,
      div_mul_cancel, Real.rpow_one, ← toReal_inv, ← toReal_mul, ofReal_toReal]
    rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel, mul_one]

  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le K this
  refine ⟨x, h_nz, ?_⟩
  convert h_bd
  rw [div_pow B, ← Real.rpow_nat_cast B, ← Real.rpow_mul (by positivity), div_mul_cancel _
    (Nat.cast_ne_zero.mpr <| ne_of_gt finrank_pos), Real.rpow_one, Nat.cast_pow]
  congr 1
  rw [eq_comm]
  calc
    _ = (2:ℝ)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ * (2:ℝ) ^ finrank ℚ K *
          ((2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K /
          (Nat.factorial (finrank ℚ K)))⁻¹ := ?_
    _ = (2:ℝ) ^ (finrank ℚ K - NrComplexPlaces K - NrRealPlaces K + NrComplexPlaces K : ℤ) *
          Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) * π⁻¹ ^ (NrComplexPlaces K) := ?_
    _ = (2:ℝ) ^ (finrank ℚ K - NrRealPlaces K : ℤ) * π⁻¹ ^ NrComplexPlaces K *
        (Nat.factorial (finrank ℚ K)) * Real.sqrt |discr K| := ?_
  · simp_rw [minkowskiBound, convexBodySumFactor, volume_fundamentalDomain_latticeBasis, toReal_div,
      toReal_mul, mixedEmbedding.finrank, toReal_pow, toReal_inv, coe_toReal, NNReal.coe_pow,
      NNReal.coe_div, coe_real_pi, NNReal.coe_ofNat, toReal_ofNat, toReal_nat]
  · simp_rw [inv_div, div_eq_mul_inv, mul_inv, ← zpow_neg_one, ← zpow_coe_nat, mul_zpow, ← zpow_mul,
      neg_one_mul, mul_neg_one, neg_neg, Real.coe_sqrt, coe_nnnorm, sub_eq_add_neg, zpow_add₀ sorry]
    ring
  · rw [show (finrank ℚ K - NrComplexPlaces K - NrRealPlaces K + NrComplexPlaces K : ℤ) = finrank ℚ K -
     NrRealPlaces K by ring, show ‖discr K‖ = |(discr K : ℝ)| by rfl]
    ring



#exit

 2 ^ (finrank ℚ K - NrComplexPlaces K - NrRealPlaces K + NrComplexPlaces K : ℤ) *
  Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) * π⁻¹ ^ (NrComplexPlaces K)


#exit
  simp_rw [minkowskiBound, volume_fundamentalDomain_latticeBasis, convexBodySumFactor,
    mixedEmbedding.finrank, div_pow, toReal_div, toReal_mul, toReal_pow, toReal_inv, toReal_ofNat,
    coe_toReal, Real.coe_sqrt, coe_nnnorm, NNReal.coe_div, NNReal.coe_pow, coe_real_pi,
    NNReal.coe_ofNat, toReal_nat, ← Real.rpow_nat_cast, ← Real.rpow_mul sorry,
    div_mul_cancel _ sorry, Real.rpow_one]





#exit


  simp only [div_pow, Nat.cast_pow, int_cast_abs, coe_toReal, Real.coe_sqrt, coe_nnnorm,
    toReal_ofNat, ne_eq, one_div]
  simp_rw [← Real.rpow_nat_cast, Real.div_rpow sorry sorry, ← Real.rpow_mul sorry, div_mul_cancel
    _ sorry, Real.rpow_one, minkowskiBound, volume_fundamentalDomain_latticeBasis,
    convexBodySumFactor, mixedEmbedding.finrank, toReal_mul]
  ring_nf

example :
    ∃ (a : 𝓞 K), a ≠ 0 ∧
    |Algebra.norm ℚ (a:K)| ≤
      Real.sqrt |discr K| * (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) /
        (2 ^ NrRealPlaces K * π ^ NrComplexPlaces K) := by
  let C :=

    sorry
  sorry

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
