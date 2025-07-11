/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ`
(defined in `Mathlib/MeasureTheory/Function/LpSpace.lean`)
is also an inner product space, with inner product defined as `inner f g := ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `fun x ↦ ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product
  `fun x ↦ ⟪f x, g x⟫` is integrable.
* `L2.innerProductSpace` : `Lp E 2 μ` is an inner product space.
-/

noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter

open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

section

variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

#check NormMulClass

#check Lp F ⊤ μ

#synth TopologicalSpace F
#synth Add (Lp F ⊤ μ)

#synth NormedRing ℂ

variable (x y : F) (f g : (α →ₘ[μ] F)) (z : α)
#check f * g

theorem MeasureTheory.ae_le_trans {α : Type*} {β : Type*} {F : Type*} [Preorder β]
    [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F} {f g h : α → β} (h₁ : f ≤ᶠ[ae μ] g)
    (h₂ : g ≤ᶠ[ae μ] h) : f ≤ᶠ[ae μ] h := by
  exact h₁.trans h₂

-- theorem MeasureTheory.ae_lt_trans {α : Type*} {β : Type*} {F : Type*} [Preorder β]
--     [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F} {f g h : α → β} (h₁ : f <ᶠ[ae μ] g)
--     (h₂ : g <ᶠ[ae μ] h) : f <ᶠ[ae μ] h := by
--   exact h₁.trans h₂

@[simp]
theorem EventuallyLE.of_forall {α : Type*} {β : Type*} [Preorder β] (l : Filter α) (f g : α → β)
    (h : f ≤ g) : f ≤ᶠ[l] g := Eventually.of_forall fun x => h x

protected theorem EventuallyLE.of_forall' {α : Type*} {β : Type*} [Preorder β] {l : Filter α} {f g : α → β}
  (h : f ≤ g) : f ≤ᶠ[l] g := EventuallyLE.of_forall l f g h


lemma linfty_mul_norm (f g : (α →ₘ[μ] F)) : eLpNormEssSup (f * g) μ ≤ eLpNormEssSup f μ * eLpNormEssSup g μ := by
  unfold eLpNormEssSup
  apply le_trans _ (ENNReal.essSup_mul_le _ _)
  apply essSup_mono_ae
  have : (fun x ↦ ‖f x‖ₑ) * (fun x ↦ ‖g x‖ₑ) = (fun x ↦ ‖f x‖ₑ * ‖g x‖ₑ) := by
    rfl
  rw [this]
  have : (fun x ↦ ‖f x * g x‖ₑ) ≤ (fun x ↦ ‖f x‖ₑ * ‖g x‖ₑ) := by
    intro x
    simp only
    by_cases hf : ‖f x‖ₑ = ⊤
    · rw [hf]
      by_cases hg : g x = 0
      · rw [hg]
        simp
      · push_neg at hg
        rw [← ofReal_norm, ← ofReal_norm]
        rw [ENNReal.top_mul]
        · exact OrderTop.le_top (ENNReal.ofReal ‖f x * g x‖)
        rw [ENNReal.ofReal_ne_zero_iff]
        exact norm_pos_iff.mpr hg
    · push_neg at hf
      by_cases hg : ‖g x‖ₑ = ⊤
      · rw [hg, mul_comm]
        by_cases hf0 : f x = 0
        · rw [hf0]
          simp
        · push_neg at hf0
          rw [← ofReal_norm, ← ofReal_norm]
          rw [ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hf0))]
          exact le_top
      · push_neg at hg
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact norm_mul_le _ _
  have aaa : (fun x ↦ ‖(f * g) x‖ₑ) ≤ᶠ[ae μ] fun x ↦ ‖f x * g x‖ₑ := by
    apply EventuallyEq.le
    apply Filter.EventuallyEq.fun_comp
    apply Filter.EventuallyEq.trans (MeasureTheory.AEEqFun.coeFn_mul f g)
    rfl
  exact MeasureTheory.ae_le_trans aaa (EventuallyLE.of_forall' this)

lemma mul_Linfty (f g : (Lp F ⊤ μ)) : f.1 * g.1 ∈ (Lp F ⊤ μ) := by
  refine mem_Lp_iff_eLpNorm_lt_top.mpr ?_
  simp only [eLpNorm_exponent_top]
  apply lt_of_le_of_lt (linfty_mul_norm f.1 g.1)
  exact ENNReal.mul_lt_top f.2 g.2



instance : Mul (Lp F ⊤ μ) where
  mul f g := ⟨f * g, mul_Linfty f g⟩

variable [c : StarAddMonoid F] [p : NormedStarGroup F]

#check p.to_continuousStar.continuous_star

variable (f : (Lp F ⊤ μ))

lemma norm_star (f : (Lp F ⊤ μ)) : eLpNorm (MeasureTheory.AEEqFun.mk (fun x => c.star (f x))
    (Continuous.comp_aestronglyMeasurable
    p.to_continuousStar.continuous_star (MeasureTheory.AEEqFun.aestronglyMeasurable f.1))) ⊤ μ
    = eLpNorm f ⊤ μ := by
  simp only [eLpNorm_exponent_top]
  unfold eLpNormEssSup
  apply essSup_congr_ae
  have : (fun (z : α) => ‖f z‖ₑ) = (fun z => ‖star (f z)‖ₑ) := by
    ext _
    rw [enorm_eq_iff_norm_eq]
    simp
  rw [this]
  apply Filter.EventuallyEq.fun_comp
  exact MeasureTheory.AEEqFun.coeFn_mk _ _

lemma norm_star_lt_top (f : (Lp F ⊤ μ)) : eLpNorm (MeasureTheory.AEEqFun.mk (fun x => c.star (f x))
    (Continuous.comp_aestronglyMeasurable
    p.to_continuousStar.continuous_star (MeasureTheory.AEEqFun.aestronglyMeasurable f.1))) ⊤ μ < ⊤
    := by
  rw [norm_star f]
  exact f.2

instance [c : StarAddMonoid F] [p : NormedStarGroup F] : Star (Lp F ⊤ μ) where
  star f := ⟨MeasureTheory.AEEqFun.mk (fun x => c.star (f x))
    (Continuous.comp_aestronglyMeasurable p.to_continuousStar.continuous_star
    (MeasureTheory.AEEqFun.aestronglyMeasurable f.1)), norm_star_lt_top f⟩

-- #synth NormedRing (Lp ℂ ⊤ μ)
-- #synth NormedAlgebra (Lp ℂ ⊤ μ)
-- #synth NormedAddCommGroup (Lp ℂ ⊤ μ)
-- #synth StarModule (Lp ℂ ⊤ μ)
-- #synth NonUnitalStarAlgebra (Lp ℂ ⊤ μ)
-- #synth StarRing (Lp ℂ ⊤ μ)
-- #synth StarModule (Lp ℂ ⊤ μ)


instance : NormedRing (Lp F ⊤ μ) where
  left_distrib := sorry

end

end MeasureTheory
