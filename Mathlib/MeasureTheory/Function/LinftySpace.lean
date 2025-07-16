/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Order.Filter.Ring

/-! # `L^∞` space

If `F` carries some algebraic structures which are continuous in norm, then `Lp F ⊤ μ`
(defined in `Mathlib/MeasureTheory/Function/LpSpace.lean`)
carries the corresponding structures.



### Main definitions

* Description

### Main results

* Description

-/

noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter AEEqFun

open scoped NNReal ENNReal MeasureTheory

section General

variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α}

theorem MeasureTheory.ae_le_trans {α : Type*} {β : Type*} {F : Type*} [Preorder β]
    [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F} {f g h : α → β} (h₁ : f ≤ᶠ[ae μ] g)
    (h₂ : g ≤ᶠ[ae μ] h) : f ≤ᶠ[ae μ] h := by
  exact h₁.trans h₂

theorem MeasureTheory.ae_rpow_mono {α : Type*} [FunLike F (Set α) ENNReal] [OuterMeasureClass F α]
    {μ : F} {f g : α → ℝ}
    (h : ∀ᵐ (a : α) ∂μ, (ENNReal.ofReal (f a)) ≤ (ENNReal.ofReal (g a))) {p : ℝ}
    (hp : 0 < p) :
    ∀ᵐ (a : α) ∂μ, (ENNReal.ofReal (f a)) ^ p ≤ (ENNReal.ofReal (g a)) ^ p := by
  rw [MeasureTheory.ae_iff] at h
  rw [MeasureTheory.ae_iff]
  rw [← h]
  congr
  ext x
  simp only [not_le, Set.mem_setOf_eq]
  exact ENNReal.rpow_lt_rpow_iff hp

theorem MeasureTheory.ae_rpow_mono' {α : Type*} [FunLike F (Set α) ENNReal] [OuterMeasureClass F α]
    {μ : F} {f g : α → ℝ≥0∞}
    (h : ∀ᵐ (a : α) ∂μ, f a ≤ g a) {p : ℝ}
    (hp : 0 < p) :
    ∀ᵐ (a : α) ∂μ, (f a) ^ p ≤ (g a) ^ p := by
  rw [MeasureTheory.ae_iff] at h
  rw [MeasureTheory.ae_iff]
  rw [← h]
  congr
  ext x
  simp only [not_le, Set.mem_setOf_eq]
  exact ENNReal.rpow_lt_rpow_iff hp


theorem MeasureTheory.ae_congr {α : Type*} {G : Type*} {F : Type*} [FunLike G (Set α) ENNReal]
    [OuterMeasureClass G α] {μ : G} {f g : α → F} {p : F → Prop}
    (hfg : ∀ᵐ (a : α) ∂μ, f a = g a) (hf : (∀ᵐ (a : α) ∂μ, p (f a))) :
    (∀ᵐ (a : α) ∂μ, p (g a)) := by
  rw [MeasureTheory.ae_iff] at hf
  rw [MeasureTheory.ae_iff] at hfg
  rw [MeasureTheory.ae_iff]
  suffices hle : μ {a | ¬p (g a)} ≤ 0 by
    exact nonpos_iff_eq_zero.mp hle
  calc
    μ {a | ¬p (g a)} ≤ μ {a | ¬f a = g a ∨ ¬p (f a)} := ?_
    _ ≤ μ {a | ¬f a = g a} + μ {a | ¬p (f a)} := MeasureTheory.measure_union_le _ _
    _ = 0 + 0 := by rw [hfg, hf]
    _ = 0 := AddZeroClass.zero_add 0
  apply MeasureTheory.measure_mono
  simp only [Set.setOf_subset_setOf]
  intro a hng
  rw [← not_and_or]
  by_contra!
  rw [← this.1] at hng
  exact hng this.2


theorem Filter.EventuallyLE.comp_le_of_monotone {α : Type*} {l : Filter α} {f₁ f₂ : α → ℝ≥0}
    {g : ℝ≥0 → ℝ≥0} (H : f₁ ≤ᶠ[l] f₂) (h : Monotone g) : g ∘ f₁ ≤ᶠ[l] g ∘ f₂ := by
  rw [eventuallyLE_iff_all_subsets]
  rw [eventuallyLE_iff_all_subsets] at H
  intro s
  refine eventually_iff_exists_mem.mpr ?_
  obtain ⟨v, hv⟩ := (eventually_iff_exists_mem.mp (H s))
  use v
  constructor
  · exact hv.1
  · intro y hy hys
    simp only [Function.comp_apply]
    exact (h (hv.2 y hy hys))

theorem Filter.EventuallyLE.rpow {α : Type*} {l : Filter α} {f₁ f₂ : α → ℝ≥0}
    {p : ℝ≥0∞} (H : f₁ ≤ᶠ[l] f₂) : f₁ ^ p.toReal ≤ᶠ[l] f₂ ^ p.toReal := by
  exact Filter.EventuallyLE.comp_le_of_monotone H
    (NNReal.monotone_rpow_of_nonneg ENNReal.toReal_nonneg)

theorem Filter.EventuallyLE.comp_le_of_monotone' {α : Type*} {l : Filter α} {f₁ f₂ : α → ℝ≥0∞}
    {g : ℝ≥0∞ → ℝ≥0∞} (H : f₁ ≤ᶠ[l] f₂) (h : Monotone g) : g ∘ f₁ ≤ᶠ[l] g ∘ f₂ := by
  rw [eventuallyLE_iff_all_subsets]
  rw [eventuallyLE_iff_all_subsets] at H
  intro s
  refine eventually_iff_exists_mem.mpr ?_
  obtain ⟨v, hv⟩ := (eventually_iff_exists_mem.mp (H s))
  use v
  constructor
  · exact hv.1
  · intro y hy hys
    simp only [Function.comp_apply]
    exact (h (hv.2 y hy hys))

theorem Filter.EventuallyLE.rpow' {α : Type*} {l : Filter α} {f₁ f₂ : α → ℝ≥0∞}
    {p : ℝ≥0∞} (H : f₁ ≤ᶠ[l] f₂) : f₁ ^ p.toReal ≤ᶠ[l] f₂ ^ p.toReal := by
  exact Filter.EventuallyLE.comp_le_of_monotone' H
    (ENNReal.monotone_rpow_of_nonneg ENNReal.toReal_nonneg)


theorem MeasureTheory.ae_congr' {α : Type*} {G : Type*} {F : Type*} [FunLike G (Set α) ENNReal]
    [OuterMeasureClass G α] {μ : G} {f1 f2 g : α → F} {p : (α → F) → F → α → Prop}
    (hf : ∀ᵐ (a : α) ∂μ, f1 a = f2 a) (hp : (∀ᵐ (a : α) ∂μ, p g (f1 a) a)) :
    (∀ᵐ (a : α) ∂μ, p g (f2 a) a) := by
  rw [MeasureTheory.ae_iff] at hp
  rw [MeasureTheory.ae_iff] at hf
  rw [MeasureTheory.ae_iff]
  suffices hle : μ {a | ¬p g (f2 a) a} ≤ 0 by
    exact nonpos_iff_eq_zero.mp hle
  calc
    μ {a | ¬p g (f2 a) a} ≤ μ {a | ¬f1 a = f2 a ∨ ¬p g (f1 a) a} := ?_
    _ ≤ μ {a | ¬f1 a = f2 a} + μ {a | ¬p g (f1 a) a} := MeasureTheory.measure_union_le _ _
    _ = 0 + 0 := by rw [hp, hf]
    _ = 0 := AddZeroClass.zero_add 0
  apply MeasureTheory.measure_mono
  simp only [Set.setOf_subset_setOf]
  intro a hng
  rw [← not_and_or]
  by_contra!
  rw [← this.1] at hng
  exact hng this.2

theorem MeasureTheory.ae_congr'' {α : Type*} {F : Type*} [TopologicalSpace F] [MeasurableSpace α]
    {μ : Measure α} {f1 f2 : α → F} {g : α →ₘ[μ] F} {p : (α → F) → F → α → Prop}
    (hf : ∀ᵐ (a : α) ∂μ, f1 a = f2 a) (hp : (∀ᵐ (a : α) ∂μ, p g (f1 a) a)) :
    (∀ᵐ (a : α) ∂μ, p g (f2 a) a) := by
  rw [MeasureTheory.ae_iff] at hp
  rw [MeasureTheory.ae_iff] at hf
  rw [MeasureTheory.ae_iff]
  suffices hle : μ {a | ¬p g (f2 a) a} ≤ 0 by
    exact nonpos_iff_eq_zero.mp hle
  calc
    μ {a | ¬p g (f2 a) a} ≤ μ {a | ¬f1 a = f2 a ∨ ¬p g (f1 a) a} := ?_
    _ ≤ μ {a | ¬f1 a = f2 a} + μ {a | ¬p g (f1 a) a} := MeasureTheory.measure_union_le _ _
    _ = 0 + 0 := by rw [hp, hf]
    _ = 0 := AddZeroClass.zero_add 0
  apply MeasureTheory.measure_mono
  simp only [Set.setOf_subset_setOf]
  intro a hng
  rw [← not_and_or]
  by_contra!
  rw [← this.1] at hng
  exact hng this.2

end General


section Mul

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

#check NormMulClass

#check Lp F ⊤ μ

#synth TopologicalSpace F
#synth Add (Lp F ⊤ μ)

#synth NormedRing ℂ

variable (x y : F) (f g : (α →ₘ[μ] F)) (z : α)
#check f * g

-- theorem MeasureTheory.ae_lt_trans {α : Type*} {β : Type*} {F : Type*} [Preorder β]
--     [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F} {f g h : α → β} (h₁ : f <ᶠ[ae μ] g)
--     (h₂ : g <ᶠ[ae μ] h) : f <ᶠ[ae μ] h := by
--   exact h₁.trans h₂

@[simp]
theorem EventuallyLE.of_forall {α : Type*} {β : Type*} [Preorder β] (l : Filter α) (f g : α → β)
    (h : f ≤ g) : f ≤ᶠ[l] g := Eventually.of_forall fun x => h x

protected theorem EventuallyLE.of_forall' {α : Type*} {β : Type*} [Preorder β] {l : Filter α}
    {f g : α → β} (h : f ≤ g) : f ≤ᶠ[l] g := EventuallyLE.of_forall l f g h

lemma enorm_mul_le_mul_enorm (x y : F) : ‖x * y‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact norm_mul_le _ _

example (c : ℝ≥0∞) (h : ∀ᵐ (x : α) ∂μ, g x = f x) (hg : ∀ᵐ (x : α) ∂μ, ‖g x‖ₑ ≤ c) :
    ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ c := by
  exact @MeasureTheory.ae_congr α (Measure α) F _ _ μ g f (fun (x : F) => ‖x‖ₑ ≤ c) h hg

lemma XXX : ∀ᵐ (x : α) ∂μ, (f * g) x = (f x) * (g x) := by
  apply MeasureTheory.AEEqFun.coeFn_mul

lemma XXX' : f.cast * g.cast =ᶠ[ae μ] (f * g : α →ₘ[μ] F) := by
  apply MeasureTheory.ae_eq_comm.mpr
  exact AEEqFun.coeFn_mul f g

lemma pXXX' : (fun x => ‖(f.cast x) * (g.cast x)‖ₑ) =ᶠ[ae μ] (fun x => ‖(f * g) x‖ₑ) := by
  apply Filter.EventuallyEq.fun_comp
  apply XXX'

lemma YYY : ∀ᵐ (x : α) ∂μ, (f x) * (g x) = (f.cast * g.cast) x := by
  apply MeasureTheory.ae_eq_comm.mpr
  apply MeasureTheory.ae_of_all
  intro x
  rfl

example : ∀ᵐ (x : α) ∂μ, ‖(f * g) x‖ₑ = ‖(f x) * (g x)‖ₑ  := by
  apply MeasureTheory.ae_eq_comm.mpr
  apply @MeasureTheory.ae_congr'' α F _ _ μ (f * g) (fun x => (f x) * (g x)) (f * g) (fun FF => (fun GG => fun x => ‖GG‖ₑ = ‖FF x‖ₑ)) (YYY f g)
  apply pXXX'

lemma linfty_mul_norm (f g : (α →ₘ[μ] F)) :
    eLpNormEssSup (f * g) μ ≤ eLpNormEssSup f μ * eLpNormEssSup g μ := by
  unfold eLpNormEssSup
  apply le_trans _ (ENNReal.essSup_mul_le _ _)
  apply essSup_mono_ae
  have : (fun x ↦ ‖f x‖ₑ) * (fun x ↦ ‖g x‖ₑ) = (fun x ↦ ‖f x‖ₑ * ‖g x‖ₑ) := by
    rfl
  rw [this]
  have : (fun x ↦ ‖f x * g x‖ₑ) ≤ (fun x ↦ ‖f x‖ₑ * ‖g x‖ₑ) := by
    intro x
    simp only
    exact enorm_mul_le_mul_enorm (f x) (g x)
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

instance : One (Lp F ⊤ μ) where
  one := ⟨1, by
    rw [Lp.mem_Lp_iff_memLp, AEEqFun.one_def]
    apply (memLp_congr_ae (AEEqFun.coeFn_mk (fun x => 1) aestronglyMeasurable_one)).mpr
    exact memLp_top_const 1⟩

@[simp]
lemma MeasureTheory.Linfty.one_coe : (1 : (Lp F ⊤ μ)).1 = 1 := by
  rfl

@[simp]
lemma MeasureTheory.Lp.mul_eq_mul_iff (f g : (Lp F ⊤ μ)) : (f * g).1 = f.1 * g.1 := rfl


lemma MeasureTheory.ae_mul_apply_eq (f g : α →ₘ[μ] F) : ∀ᵐ (a : α) ∂μ, (f * g) a = f a * g a :=
  MeasureTheory.AEEqFun.coeFn_mul f g

lemma MeasureTheory.ae_mul_apply_eq_refl (f g : α →ₘ[μ] F) : ∀ᵐ (a : α) ∂μ, f a * g a = (f * g) a:=
  MeasureTheory.ae_eq_comm.mp (MeasureTheory.AEEqFun.coeFn_mul f g)

end Mul

section SMul

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

lemma smul_Linfty {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ⊤) (f : (Lp F ⊤ μ))
    (g : (Lp F p μ)) : f.1 * g.1 ∈ (Lp F p μ) := by
  refine mem_Lp_iff_eLpNorm_lt_top.mpr ?_
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ⊤)]
  rw [ENNReal.rpow_lt_top_iff_of_pos
    (by simp only [one_div, inv_pos]; exact ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
  calc
    ∫⁻ (x : α), ‖(f.1 * g.1) x‖ₑ ^ p.toReal ∂μ ≤ ∫⁻ (x : α), (‖f x‖ₑ * ‖g x‖ₑ) ^ p.toReal ∂μ := ?_
    _ = ∫⁻ (x : α), ‖f x‖ₑ ^ p.toReal * ‖g x‖ₑ ^ p.toReal ∂μ := ?_
    _ ≤ ∫⁻ (x : α), (eLpNorm f ⊤ μ) ^ p.toReal * ‖g x‖ₑ ^ p.toReal ∂μ := ?_
    _ = (eLpNorm f ⊤ μ) ^ p.toReal * ∫⁻ (x : α), ‖g x‖ₑ ^ p.toReal ∂μ := ?_
    _ = (eLpNorm f ⊤ μ) ^ p.toReal * (eLpNorm g p μ) ^ p.toReal := ?_
    _ < ⊤ := ?_
  · apply MeasureTheory.lintegral_mono_ae
    suffices henorm : ∀ᵐ (a : α) ∂μ, ‖(f.1 * g.1) a‖ₑ ^ p.toReal = ‖f.1 a * g.1 a‖ₑ ^ p.toReal by
      apply MeasureTheory.ae_rpow_mono' _ (ENNReal.toReal_pos hp_ne_zero hp_ne_top)
      apply EventuallyEq.rw (ae_eq_symm (coeFn_mul f.1 g.1))
        (fun x => fun X => ‖X‖ₑ ≤ ‖f.1 x‖ₑ * ‖g.1 x‖ₑ)
      simp only [Pi.mul_apply]
      apply ae_of_all
      intro x
      exact enorm_mul_le_mul_enorm (f.1 x) (g.1 x)
    apply @Filter.EventuallyEq.fun_comp _ _ _ _ _ (ae μ) _ (fun x => x ^ p.toReal)
    apply Filter.EventuallyEq.fun_comp
    exact AEEqFun.coeFn_mul _ _
  · congr
    ext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ p.toReal_nonneg]
  · apply MeasureTheory.lintegral_mono_ae
    apply EventuallyLE.mul_le_mul
    · apply Filter.EventuallyLE.rpow' _
      simp only [eLpNorm_exponent_top]
      exact ae_le_eLpNormEssSup
    · exact EventuallyLE.refl _ _
    · apply ae_of_all
      intro x
      simp
    · apply ae_of_all
      simp
  · rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.rpow_ne_top_of_nonneg p.toReal_nonneg (eLpNorm_ne_top f)
  · congr
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
    simp only [one_div]
    rw [ENNReal.rpow_inv_rpow]
    exact ENNReal.toReal_ne_zero.mpr ⟨hp_ne_zero, hp_ne_top⟩
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg p.toReal_nonneg (eLpNorm_ne_top f))
      (ENNReal.rpow_lt_top_of_nonneg p.toReal_nonneg (eLpNorm_ne_top g))

instance {p : ℝ≥0∞} [nz : Fact (p ≠ 0)] [nt : Fact (p ≠ ⊤)] : SMul (Lp F ⊤ μ) (Lp F p μ) where
  smul f g := ⟨f * g, smul_Linfty nz.out nt.out f g⟩

end SMul

section Star

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

variable [c : StarAddMonoid F] [p : NormedStarGroup F]

#check p.to_continuousStar.continuous_star

variable (f : (Lp F ⊤ μ))

lemma norm_star_eq (f : (Lp F ⊤ μ)) : eLpNorm (MeasureTheory.AEEqFun.mk (fun x => c.star (f x))
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
  rw [norm_star_eq f]
  exact f.2

instance [c : StarAddMonoid F] [p : NormedStarGroup F] : Star (Lp F ⊤ μ) where
  star f := ⟨MeasureTheory.AEEqFun.mk (fun x => c.star (f x))
    (Continuous.comp_aestronglyMeasurable p.to_continuousStar.continuous_star
    (MeasureTheory.AEEqFun.aestronglyMeasurable f.1)), norm_star_lt_top f⟩

-- #synth NormedRing (Lp ℂ ⊤ μ)
-- #synth NormedAlgebra (Lp ℂ ⊤ μ)
#synth NormedAddCommGroup (Lp ℂ ⊤ μ)
-- #synth StarModule (Lp ℂ ⊤ μ)
-- #synth NonUnitalStarAlgebra (Lp ℂ ⊤ μ)
-- #synth InvolutiveStar
-- #synth StarAddMonoid
-- #synth StarRing (Lp ℂ ⊤ μ)
-- #synth StarModule (Lp ℂ ⊤ μ)
-- #synth NormedStarGroup



theorem MeasureTheory.AEEqFun.zero_mul {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [MulZeroClass γ] [ContinuousMul γ] (f : α →ₘ[μ] γ) :
    (0 : α →ₘ[μ] γ) * f = (0 : α →ₘ[μ] γ) := by
  rw [MeasureTheory.AEEqFun.zero_def, ← AEEqFun.mk_coeFn f, AEEqFun.mk_mul_mk _ f]
  suffices h : (fun x => 0) * f.cast = 0 by
    simp_rw [h]
    rfl
  ext x
  simp

theorem MeasureTheory.AEEqFun.mul_zero {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [MulZeroClass γ] [ContinuousMul γ] (f : α →ₘ[μ] γ) :
    f * (0 : α →ₘ[μ] γ) = (0 : α →ₘ[μ] γ) := by
  rw [MeasureTheory.AEEqFun.zero_def, ← AEEqFun.mk_coeFn f, AEEqFun.mk_mul_mk f _]
  suffices h : f.cast * (fun x => 0) = 0 by
    simp_rw [h]
    rfl
  ext x
  simp

theorem MeasureTheory.AEEqFun.mul_one {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ] (f : α →ₘ[μ] γ) :
    f * (1 : α →ₘ[μ] γ) = (f : α →ₘ[μ] γ) := by
  rw [MeasureTheory.AEEqFun.one_def, ← AEEqFun.mk_coeFn f, AEEqFun.mk_mul_mk f _ ]
  suffices h : f.cast * (fun x => 1) = f.cast by
    simp_rw [h]
  ext x
  simp

theorem MeasureTheory.AEEqFun.one_mul {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ] (f : α →ₘ[μ] γ) :
    (1 : α →ₘ[μ] γ) * f = f := by
  rw [MeasureTheory.AEEqFun.one_def, ← AEEqFun.mk_coeFn f, AEEqFun.mk_mul_mk _ f]
  suffices h : (fun x => 1) * f.cast = f.cast by
    simp_rw [h]
  ext x
  simp


theorem MeasureTheory.AEEqFun.right_distrib {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [NonUnitalNonAssocSemiring γ] [IsTopologicalSemiring γ] (a b c : α →ₘ[μ] γ) :
    (a + b) * c = a * c + b * c := by
  ext
  apply ae_eq_trans (coeFn_mul _ _)
  apply ae_eq_trans _ (ae_eq_symm (coeFn_add (a * c) (b * c)))
  have : (a + b).cast * c.cast =ᶠ[ae μ] (a.cast + b.cast) * c.cast := by
    apply EventuallyEq.rw (ae_eq_symm (coeFn_add a b)) (fun x => fun X => X * (c.cast x) = ((a.cast + b.cast) * c.cast ) x)
    apply ae_of_all
    exact fun x => rfl
  apply ae_eq_trans this
  rw [add_mul]
  apply EventuallyEq.rw (ae_eq_symm (coeFn_mul a c))
    (fun (x : α) => (fun (X : γ) => ((a.cast * c.cast) x + (b.cast * c.cast) x = X + (b * c).cast x)))
  apply EventuallyEq.rw (ae_eq_symm (coeFn_mul b c))
    (fun (x : α) => (fun (X : γ) => ((a.cast * c.cast) x + (b.cast * c.cast) x = (a.cast * c.cast) x + X)))
  apply ae_of_all
  exact fun x => rfl

theorem MeasureTheory.AEEqFun.left_distrib {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [NonUnitalNonAssocSemiring γ] [IsTopologicalSemiring γ] (a b c : α →ₘ[μ] γ) :
    a * (b + c) = a * b + a * c := by
  ext
  apply ae_eq_trans (coeFn_mul _ _)
  apply ae_eq_trans _ (ae_eq_symm (coeFn_add (a * b) (a * c)))
  have : a.cast * (b + c).cast =ᶠ[ae μ] a.cast * (b.cast + c.cast) := by
    apply EventuallyEq.rw (ae_eq_symm (coeFn_add b c)) (fun x => fun X => (a.cast x) * X = (a.cast x) * (b.cast + c.cast) x)
    apply ae_of_all
    exact fun x => rfl
  apply ae_eq_trans this
  rw [mul_add]
  apply EventuallyEq.rw (ae_eq_symm (coeFn_mul a b))
    (fun (x : α) => (fun (X : γ) => ((a.cast * b.cast) x + (a.cast * c.cast) x = X + (a * c).cast x)))
  apply EventuallyEq.rw (ae_eq_symm (coeFn_mul a c))
    (fun (x : α) => (fun (X : γ) => ((a.cast * b.cast) x + (a.cast * c.cast) x = (a.cast * b.cast) x + X)))
  apply ae_of_all
  exact fun x => rfl






instance : MulZeroClass (α →ₘ[μ] F) where
  zero_mul := AEEqFun.zero_mul
  mul_zero := AEEqFun.mul_zero

instance : MulOneClass (α →ₘ[μ] F) where
  one_mul := AEEqFun.one_mul
  mul_one := AEEqFun.mul_one

instance : Semiring (α →ₘ[μ] F) where
  left_distrib := AEEqFun.left_distrib
  right_distrib := AEEqFun.right_distrib

instance : Ring (α →ₘ[μ] F) where

end Star

section

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

variable {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace γ] [MulZeroClass γ] [ContinuousMul γ]

theorem MeasureTheory.Lp.eq_iff (f g : (Lp F ⊤ μ)) : f = g ↔ f.1 = g.1 := Subtype.eq_iff

theorem MeasureTheory.Linfty.zero_mul (f : (Lp F ⊤ μ)) : (0 : (Lp F ⊤ μ)) * f = (0 : (Lp F ⊤ μ)) := by
  rw [Subtype.eq_iff]
  simp

theorem MeasureTheory.Linfty.mul_zero (f : (Lp F ⊤ μ)) : f * (0 : (Lp F ⊤ μ)) = (0 : (Lp F ⊤ μ)) := by
  rw [Subtype.eq_iff]
  simp

instance : MulZeroClass (Lp F ⊤ μ) where
  zero_mul := MeasureTheory.Linfty.zero_mul
  mul_zero := MeasureTheory.Linfty.mul_zero

end

section

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

variable {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]

theorem MeasureTheory.Linfty.one_mul (f : (Lp F ⊤ μ)) : (1 : (Lp F ⊤ μ)) * f = f := by
  rw [Subtype.eq_iff]
  simp

theorem MeasureTheory.Linfty.mul_one (f : (Lp F ⊤ μ)) : f * (1 : (Lp F ⊤ μ)) = f := by
  rw [Subtype.eq_iff]
  simp

instance : MulOneClass (Lp F ⊤ μ) where
  one_mul := MeasureTheory.Linfty.one_mul
  mul_one := MeasureTheory.Linfty.mul_one

end

section

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

variable {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [NonUnitalNonAssocSemiring γ] [IsTopologicalSemiring γ]

theorem MeasureTheory.Linfty.right_distrib (a b c : (Lp F ⊤ μ)) :
    (a + b) * c = a * c + b * c := by
  rw [Subtype.eq_iff]
  simp only [mul_eq_mul_iff, AddSubgroup.coe_add]
  exact AEEqFun.right_distrib a.1 b.1 c.1

theorem MeasureTheory.Linfty.left_distrib (a b c : (Lp F ⊤ μ)) :
    a * (b + c) = a * b + a * c := by
  rw [Subtype.eq_iff]
  simp only [mul_eq_mul_iff, AddSubgroup.coe_add]
  exact AEEqFun.left_distrib a.1 b.1 c.1


instance : NonUnitalNonAssocSemiring (Lp F ⊤ μ) where
  left_distrib := Linfty.left_distrib
  right_distrib := Linfty.right_distrib

end

section

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing F]
  [Fact (1 ≤ (⊤ : ℝ≥0∞))]

variable {α : Type*} {γ : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace γ] [NonUnitalSemiring γ] [IsTopologicalSemiring γ]

instance : NonUnitalSemiring (Lp F ⊤ μ) where
  mul_assoc a b c := by
    rw [Subtype.eq_iff]
    simp only [mul_eq_mul_iff]
    exact mul_assoc a.1 b.1 c.1


instance : NormedRing (Lp F ⊤ μ) where
  dist_eq := fun x y => rfl

end
