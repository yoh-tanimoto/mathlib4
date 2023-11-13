/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Decomposition.SignedLebesgue

#align_import measure_theory.decomposition.radon_nikodym from "leanprover-community/mathlib"@"fc75855907eaa8ff39791039710f567f37d4556f"

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rnDeriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`MeasureTheory/Function/ConditionalExpectation`).

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq` :
  the Radon-Nikodym theorem
* `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` :
  the Radon-Nikodym theorem for signed measures

## Tags

Radon-Nikodym theorem
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

theorem withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) :
    ν.withDensity (rnDeriv μ ν) = μ := by
  obtain ⟨_, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩ := haveLebesgueDecomposition_spec μ ν
  have : singularPart μ ν = 0 := by
    refine' le_antisymm (fun A (_ : MeasurableSet A) => _) (Measure.zero_le _)
    suffices singularPart μ ν Set.univ = 0 by
      rw [Measure.coe_zero, Pi.zero_apply, ← this]
      exact measure_mono (Set.subset_univ _)
    rw [← measure_add_measure_compl hE₁, hE₂, zero_add]
    have : (singularPart μ ν + ν.withDensity (rnDeriv μ ν)) Eᶜ = μ Eᶜ := by rw [← hadd]
    rw [Measure.coe_add, Pi.add_apply, h hE₃] at this
    exact (add_eq_zero_iff.1 this).1
  rw [this, zero_add] at hadd
  exact hadd.symm
#align measure_theory.measure.with_density_rn_deriv_eq MeasureTheory.Measure.withDensity_rnDeriv_eq

variable {μ ν : Measure α}

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.withDensity (rnDeriv μ ν) = μ`. -/
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq
    [HaveLebesgueDecomposition μ ν] : μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ :=
  ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩
#align measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq

lemma rnDeriv_pos [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := by
  rw [← Measure.withDensity_rnDeriv_eq _ _  hμν,
    ae_withDensity_iff (Measure.measurable_rnDeriv _ _), Measure.withDensity_rnDeriv_eq _ _  hμν]
  exact ae_of_all _ (fun x hx ↦ lt_of_le_of_ne (zero_le _) hx.symm)

lemma inv_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (rnDeriv_withDensity _ (measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.rnDeriv μ := rnDeriv_withDensity _ (measurable_rnDeriv _ _)
  rw [withDensity_rnDeriv_eq _ _ hνμ, ← withDensity_rnDeriv_eq _ _ hμν]
  conv in ((ν.withDensity (μ.rnDeriv ν)).rnDeriv ν)⁻¹ => rw [withDensity_rnDeriv_eq _ _ hμν]
  change (ν.withDensity (μ.rnDeriv ν)).withDensity (fun x ↦ (μ.rnDeriv ν x)⁻¹) = ν
  rw [withDensity_inv_same (measurable_rnDeriv _ _)
    (by filter_upwards [hνμ.ae_le (rnDeriv_pos hμν)] with x hx using hx.ne')
    (rnDeriv_ne_top _ _)]

lemma set_lintegral_rnDeriv_le (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν ≤ μ s := by
  let t := toMeasurable μ s
  calc ∫⁻ x in s, μ.rnDeriv ν x ∂ν
    ≤ ∫⁻ x in t, μ.rnDeriv ν x ∂ν := lintegral_mono_set (subset_toMeasurable μ s)
  _ ≤ μ t := by
        rw [← withDensity_apply _ (measurableSet_toMeasurable μ s)]
        exact withDensity_rnDeriv_le _ _ _ (measurableSet_toMeasurable μ s)
  _ = μ s := by rw [← measure_toMeasurable s]

lemma set_lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply _ hs, Measure.withDensity_rnDeriv_eq _ _ hμν]

lemma lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  rw [← set_lintegral_univ, set_lintegral_rnDeriv hμν MeasurableSet.univ]

lemma integrableOn_toReal_rnDeriv {s : Set α} (hμs : μ s ≠ ∞) :
    IntegrableOn (fun x ↦ (μ.rnDeriv ν x).toReal) s ν := by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((set_lintegral_rnDeriv_le _).trans_lt hμs.lt_top).ne

lemma set_integral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν) s).toReal := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

lemma set_integral_toReal_rnDeriv_le [SigmaFinite μ] {s : Set α} (hμs : μ s ≠ ∞) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν ≤ (μ s).toReal := by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t ≠ ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    ≤ ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine set_integral_mono_set ?_ ?_ (HasSubset.Subset.eventuallyLE (subset_toMeasurable _ _))
        · exact integrableOn_toReal_rnDeriv hμt
        · exact ae_of_all _ (by simp)
  _ ≤ (μ t).toReal := by
        rw [set_integral_toReal_rnDeriv_eq_withDensity ht_m, ENNReal.toReal_le_toReal _ hμt]
        · exact withDensity_rnDeriv_le _ _ _ ht_m
        · exact ((withDensity_rnDeriv_le _ _ _ ht_m).trans_lt hμt.lt_top).ne
  _ = (μ s).toReal := by rw [← measure_toMeasurable s]

lemma set_integral_toReal_rnDeriv [SigmaFinite μ] [HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (μ s).toReal := by
  rw [set_integral_toReal_rnDeriv_eq_withDensity hs, Measure.withDensity_rnDeriv_eq _ _ hμν]
#align measure_theory.measure.with_density_rn_deriv_to_real_eq MeasureTheory.Measure.set_integral_toReal_rnDeriv

lemma integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = (μ Set.univ).toReal := by
  rw [← integral_univ, set_integral_toReal_rnDeriv hμν MeasurableSet.univ]

end Measure

namespace SignedMeasure

open Measure VectorMeasure

theorem withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutelyContinuous_ennreal_iff, (_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ),
    totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi, rnDeriv, integral_sub,
      set_integral_toReal_rnDeriv h.1 hi, set_integral_toReal_rnDeriv h.2 hi]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      erw [VectorMeasure.sub_apply]
      rw [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi]
    all_goals
      rw [← integrableOn_univ]
      refine' IntegrableOn.restrict _ MeasurableSet.univ
      refine' ⟨_, hasFiniteIntegral_toReal_of_lintegral_ne_top _⟩
      · apply Measurable.aestronglyMeasurable
        measurability
      · rw [set_lintegral_univ]
        exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ
#align measure_theory.signed_measure.with_densityᵥ_rn_deriv_eq MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α)
    [SigmaFinite μ] : s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩
#align measure_theory.signed_measure.absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq

end SignedMeasure

end MeasureTheory
