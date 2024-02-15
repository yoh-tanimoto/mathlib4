/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.ZetaFunctions.AbstractFuncEq
import Mathlib.NumberTheory.ZetaFunctions.KernelBounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`completedHurwitzZetaEven a s = 1 / 2 * □ * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`completedCosZeta a s = □ * ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`

where `□` denotes a Gamma factor. Note that the term for `n = -a` in the first sum is omitted
if `a` is an integer, and the term for `n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function. We also define modified versions with a subscript `0`
which are entire functions differing from the above by multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems

* `completedHurwitzZetaEven`: the completed Hurwitz zeta function
* `completedCosZeta`: the completed cosine zeta function
* `differentiableAt_completedHurwitzZetaEven` and `differentiableAt_completedCosZeta`:
  differentiability away from `s = 0` and `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `completedHurwitzZetaEven_eq_tsum_int` and `completedCosZeta_eq_tsum_nat`: relation between the
  zeta functions and corresponding Dirichlet series for `1 < re s`
-/
noncomputable section

open Complex Filter Topology Asymptotics Real Set Classical MeasureTheory

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Even Hurwitz zeta kernel (function whose Mellin transform will be the even part of the
completed Hurwit zeta function). See `evenKernel_def` for the defining formula, and
`hasSum_int_evenKernel` for an expression as a sum over `ℤ`. -/
@[irreducible] def evenKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic
    (fun ξ : ℝ ↦ rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp_rw [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) =
        rexp (π * (x + 2 * ξ * x))
      · simp_rw [ofReal_exp, push_cast]
        ring_nf
        rw [I_sq]
        ring_nf
      rw [this, re_ofReal_mul, ← mul_assoc, ← Real.exp_add]
      ring_nf).lift a

lemma evenKernel_def (a x : ℝ) :
    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
  rw [evenKernel, Function.Periodic.lift_coe]
  simp_rw [push_cast, Complex.re_eq_add_conj, jacobiTheta₂_conj, map_mul, conj_I, conj_ofReal,
    mul_neg, neg_mul, jacobiTheta₂_neg_left, neg_neg, ← mul_two, mul_div_cancel _ (two_ne_zero' ℂ)]

/-- For `x ≤ 0` the defining sum diverges, so the kernel is 0. -/
lemma evenKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : evenKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef, mul_zero, ofReal_zero]
  rwa [I_mul_im, ofReal_re]

/-- Cosine Hurwitz zeta kernel. See `cosKernel_def` for the defining formula, and
`hasSum_int_cosKernel` for expression as a sum. -/
@[irreducible] def cosKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp_rw [ofReal_add, ofReal_one, jacobiTheta₂_add_left]).lift a

lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
  rw [cosKernel, Function.Periodic.lift_coe]
  simp_rw [Complex.re_eq_add_conj, jacobiTheta₂_conj, map_mul, conj_ofReal, conj_I, neg_mul,
    neg_neg, ← mul_two, mul_div_cancel _ (two_ne_zero' ℂ)]

lemma cosKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : cosKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef, ofReal_zero]
  rwa [I_mul_im, ofReal_re]

/-- For `a = 0`, both kernels agree. -/
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
  ext1 x
  rw [← ofReal_inj, ← QuotientAddGroup.mk_zero, cosKernel_def, evenKernel_def]
  simp

lemma evenKernel_neg (a : UnitAddCircle) (x : ℝ) : evenKernel (-a) x = evenKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj]
  simp_rw [← QuotientAddGroup.mk_neg, evenKernel_def, ofReal_neg, neg_mul,
    jacobiTheta₂_neg_left, neg_sq]

lemma cosKernel_neg (a : UnitAddCircle) (x : ℝ) : cosKernel (-a) x = cosKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj]
  simp_rw [← QuotientAddGroup.mk_neg, cosKernel_def, ofReal_neg, jacobiTheta₂_neg_left]

lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  change ContinuousOn (fun x ↦ re (evenKernel a' x : ℂ)) (Ioi 0)
  apply Complex.continuous_re.comp_continuousOn
  simp_rw [evenKernel_def a']
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · exact Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)
  · have h := continuousAt_jacobiTheta₂ (a' * I * x) (?_ : 0 < im (I * x))
    · refine h.comp (f := fun u : ℝ ↦ (a' * I * u, I * u)) (Continuous.continuousAt ?_)
      continuity
    · rwa [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_re]

lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  change ContinuousOn (fun x ↦ re (cosKernel a' x : ℂ)) (Ioi 0)
  apply Complex.continuous_re.comp_continuousOn
  simp_rw [cosKernel_def]
  apply ContinuousAt.continuousOn (fun x hx ↦ ?_)
  have h := continuousAt_jacobiTheta₂ a' (?_ : 0 < im (I * x))
  · refine h.comp (f := fun u : ℝ ↦ ((a' : ℂ), I * u)) (Continuous.continuousAt ?_)
    continuity
  · rwa [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_re]

lemma evenKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    evenKernel a x = 1 / x ^ (1 / 2 : ℝ) * cosKernel a (1 / x) := by
  rcases le_or_lt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, ofReal_mul, evenKernel_def, cosKernel_def,
    jacobiTheta₂_functional_equation]
  have : I * ↑(1 / x) = -1 / (I * ↑x)
  · push_cast; field_simp [hx.ne']; ring_nf; rw [I_sq]; ring_nf
  rw [this]
  have : (a' * I * x / (I * x)) = a' := by { field_simp [hx.ne']; ring_nf }
  rw [this]
  have : 1 / (-I * (I * x)) ^ (1 / 2 : ℂ) = 1 / ↑(x  ^ (1 / 2 : ℝ))
  · rw [neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg,
      ofReal_cpow hx.le, ofReal_div, ofReal_one, ofReal_ofNat]
  rw [this]
  have : -↑π * I * (↑a' * I * ↑x) ^ 2 / (I * ↑x) = - (-π * a' ^ 2 * x)
  · rw [mul_pow, mul_pow, I_sq]; field_simp [hx.ne']; ring_nf
  rw [this, ← mul_assoc, mul_comm (cexp _), mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add,
    neg_add_self, Complex.exp_zero, mul_one, ofReal_div, ofReal_one]

end kernel_defs

section asymp

/-!
## Formulae for the kernels as sums
-/

lemma hasSum_int_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t) := by
  rw [← hasSum_ofReal, evenKernel_def]
  convert (hasSum_jacobiTheta₂_term _ (by rwa [I_mul_im, ofReal_re])).mul_left _
    using 2 with n
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  push_cast
  ring_nf
  rw [I_sq]
  ring_nf

lemma hasSum_int_cosKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t) := by
  rw [cosKernel_def a t]
  convert hasSum_jacobiTheta₂_term a (by rwa [I_mul_im, ofReal_re] : 0 < im (I * t)) using 2 with n
  rw [jacobiTheta₂_term, ofReal_exp, ← Complex.exp_add]
  push_cast
  ring_nf
  rw [I_sq]
  ring_nf

/-- Modified version of `hasSum_int_evenKernel` omitting the constant term at `∞`. -/
lemma hasSum_int_evenKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n = -a then 0 else rexp (-π * (n + a) ^ 2 * t))
    (evenKernel a t - if (a : UnitAddCircle) = 0 then 1 else 0) := by
  simp_rw [AddCircle.coe_eq_zero_iff]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simp_rw [zsmul_eq_mul, mul_one, ← Int.cast_neg, Int.cast_inj]
    simpa using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : ℝ) ht) (-k)
  · suffices : ∀ (n : ℤ), ↑n ≠ -a; simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by rwa [zsmul_one, Int.cast_neg, neg_eq_iff_eq_neg]⟩

lemma hasSum_int_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t))
    (↑(cosKernel a t) - 1) := by simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

lemma hasSum_nat_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.cos (2 * π * a * (n + 1)) * rexp (-π * (n + 1) ^ 2 * t))
    (cosKernel a t - 1) := by
  rw [← hasSum_ofReal, ofReal_sub, ofReal_one]
  have := (hasSum_int_cosKernel a ht).sum_nat_of_sum_int
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_ofNat, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  convert this with n
  push_cast
  rw [Complex.cos, mul_div_cancel' _ two_ne_zero]
  ring_nf

-- do we need a `nat` version for evenKernel?

/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `cosKernel a - 1` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (cosKernel a · - 1) (fun x ↦ Real.exp (-p * x)) := by
  induction' a using QuotientAddGroup.induction_on with a
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, .trans ?_ (hp'.const_mul_left 2)⟩
  simp_rw [eq_false_intro one_ne_zero, if_false, sub_zero]
  apply Eventually.isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded (g := fun n ↦ 2 * HurwitzKernelBounds.f_nat 0 1 t n)
  · exact (HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left _
  · intro n
    rw [norm_mul, norm_mul, norm_two, mul_assoc, mul_le_mul_iff_of_pos_left two_pos,
      norm_of_nonneg (exp_pos _).le, HurwitzKernelBounds.f_nat, pow_zero, one_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

/-- The function `evenKernel a - L` has exponential decay at `+∞`, where `L = 1` if
`a = 0` and `L = 0` otherwise. -/
lemma isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : ∃ r : ℝ, 0 < r ∧
    (evenKernel a · - (if a = 0 then 1 else 0)) =O[atTop] (rexp <| -r * ·) := by
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℝ, b ∈ Ico 0 1 ∧ ↑b = a
  · let b := (QuotientAddGroup.equivIcoMod (zero_lt_one' ℝ) 0) a
    have hb : ↑b = a := (QuotientAddGroup.equivIcoMod (zero_lt_one' ℝ) 0).symm_apply_apply a
    refine ⟨b.1, ⟨b.2.1, by simpa only [zero_add] using b.2.2⟩, hb⟩
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub hb
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp_rw [← (hasSum_int_evenKernel b ht).tsum_eq, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, pow_zero, one_mul]
  congr 2
  rw [← QuotientAddGroup.mk_zero, AddCircle.coe_eq_coe_iff_of_mem_Ico (hp := ⟨one_pos⟩) (a := 0)]
  · simpa only [zero_add, mem_Ico] using hb
  · simp only [zero_add, mem_Ico, le_refl, zero_lt_one, and_self]

end asymp

section FEPair
/-!
## Construction of a FE-pair
-/

/-- A `WeakFEPair` structure with `f = evenKernel a` and `g = cosKernel a`. -/
def hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal' ∘ evenKernel a
  g := ofReal' ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := by norm_num
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : ℝ → ℂ), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
    rw [← isBigO_norm_left] at hp' ⊢
    convert hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp _).isBigO
    rw [← norm_real, ofReal_sub, ofReal_one, Function.comp_apply]
  h_feq x hx := by
    simp_rw [Function.comp_apply, one_mul, smul_eq_mul, ← ofReal_mul,
      evenKernel_functional_equation, one_div x, one_div x⁻¹, inv_rpow (le_of_lt hx),
      one_div, inv_inv]

lemma hurwitzEvenFEPair_zero_symm :
    (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp only [evenKernel_eq_cosKernel_of_zero, inv_one, if_true]

lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp only [Function.comp_def, evenKernel_neg, cosKernel_neg, neg_eq_zero]

/-!
## Definition of the even Hurwitz zeta function
-/

/--
The meromorphic function of `s` which agrees with
`1 / 2 * Gamma (s / 2) * π ^ (-s / 2) * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s`.
-/
def completedHurwitzZetaEven (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ (s / 2)) / 2

/-- The entire function differing from `completedHurwitzZetaEven a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
def completedHurwitzZetaEven₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2

lemma completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a s =
    completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s - 1 / (1 - s) := by
  rw [completedHurwitzZetaEven, WeakFEPair.Λ, sub_div, sub_div]
  congr 1
  · change completedHurwitzZetaEven₀ a s - (1 / (s / 2)) • (if a = 0 then 1 else 0) / 2 =
      completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s
    rw [smul_eq_mul, mul_comm, mul_div_assoc, div_div, div_mul_cancel _ two_ne_zero, mul_one_div]
  · change (1 / (↑(1 / 2 : ℝ) - s / 2)) • 1 / 2 = 1 / (1 - s)
    push_cast
    rw [smul_eq_mul, mul_one, ← sub_div, div_div, div_mul_cancel _ two_ne_zero]

/--
The meromorphic function of `s` which agrees with
`Gamma (s / 2) * π ^ (-s / 2) * ∑' n : ℕ, cos (2 * π * a * n) / n ^ s` for `1 < re s`.
-/
def completedCosZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ (s / 2)) / 2

/-- The entire function differing from `completedCosZeta a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
def completedCosZeta₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2

lemma completedCosZeta_eq (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta a s =
    completedCosZeta₀ a s - 1 / s - (if a = 0 then 1 else 0) / (1 - s) := by
  rw [completedCosZeta, WeakFEPair.Λ, sub_div, sub_div]
  congr 1
  · rw [ completedCosZeta₀, WeakFEPair.symm, hurwitzEvenFEPair, smul_eq_mul, mul_one, div_div,
      div_mul_cancel _ (two_ne_zero' ℂ)]
  · simp_rw [WeakFEPair.symm, hurwitzEvenFEPair, push_cast, inv_one, smul_eq_mul,
      mul_comm _ (if _ then _ else _), mul_div_assoc, div_div, ← sub_div,
      div_mul_cancel _ (two_ne_zero' ℂ), mul_one_div]

/-!
## Parity and functional equations
-/

lemma completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven (-a) s = completedHurwitzZetaEven a s := by
  simp only [completedHurwitzZetaEven, hurwitzEvenFEPair_neg]

lemma completedHurwitzZetaEven₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ (-a) s = completedHurwitzZetaEven₀ a s := by
  simp only [completedHurwitzZetaEven₀, hurwitzEvenFEPair_neg]

lemma completedCosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta (-a) s = completedCosZeta a s := by
  simp only [completedCosZeta, hurwitzEvenFEPair_neg]

lemma completedCosZeta₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ (-a) s = completedCosZeta₀ a s := by
  simp only [completedCosZeta₀, hurwitzEvenFEPair_neg]

/-- Functional equation for the even Hurwitz zeta function. -/
lemma completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a (1 - s) = completedCosZeta a s := by
  rw [completedHurwitzZetaEven, completedCosZeta, sub_div,
    (by norm_num : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function with poles removed. -/
lemma completedHurwitzZetaEven₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a (1 - s) = completedCosZeta₀ a s := by
  rw [completedHurwitzZetaEven₀, completedCosZeta₀, sub_div,
    (by norm_num : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation₀ (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function (alternative form). -/
lemma completedCosZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta a (1 - s) = completedHurwitzZetaEven a s := by
  rw [← completedHurwitzZetaEven_one_sub, sub_sub_cancel]

/-- Functional equation for the even Hurwitz zeta function with poles removed (alternative form). -/
lemma completedCosZeta₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ a (1 - s) = completedHurwitzZetaEven₀ a s := by
  rw [← completedHurwitzZetaEven₀_one_sub, sub_sub_cancel]

/-!
## Differentiability and residues
-/

/--
The even Hurwitz completed zeta is differentiable away from `s = 0` and `s = 1` (and also at
`s = 0` if `a ≠ 0`)
-/
lemma differentiableAt_completedHurwitzZetaEven
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0 ∨ a ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (completedHurwitzZetaEven a) s := by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
    (differentiableAt_id.div_const _)).div_const _
  · rw [div_ne_zero_iff, eq_true_intro two_ne_zero, and_true]
    refine Or.imp (by tauto) (fun ha ↦ ?_) hs
    simp only [hurwitzEvenFEPair, eq_false_intro ha, if_false]
  · change s / 2 ≠ ↑(1 / 2 : ℝ)
    rw [ofReal_div, ofReal_one, ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp

lemma differentiable_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaEven₀ a) :=
  ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

lemma differentiableAt_completedCosZeta
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (completedCosZeta a) s := by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rwa [div_ne_zero_iff, eq_true_intro two_ne_zero, and_true]
  · change s / 2 ≠ ↑(1 / 2 : ℝ) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h ↦ ?_) (fun ha ↦ ?_) hs'
    · simpa only [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simp_rw [eq_false_intro ha, if_false]

lemma differentiable_completedCosZeta₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedCosZeta₀ a) :=
  ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- The residue of `completedHurwitzZetaEven a s` at `s = 1` is equal to `1`. -/
lemma completedHurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have h1 : Tendsto (fun s : ℂ ↦ (s - ↑(1  / 2 : ℝ)) * _) (𝓝[≠] ↑(1  / 2 : ℝ))
    (𝓝 ((1 : ℂ) * (1 : ℂ))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  have h2 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] (1 / 2)) :=
    le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq 1)
  refine (h1.comp h2).congr (fun s ↦ ?_)
  rw [completedHurwitzZetaEven, Function.comp_apply]
  ring_nf

/-- The residue of `completedHurwitzZetaEven a s` at `s = 0` is equal to `-1` if `a = 0`, and `0`
otherwise. -/
lemma completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedHurwitzZetaEven a s) (𝓝[≠] 0) (𝓝 (if a = 0 then -1 else 0)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : ℂ) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast, one_mul] at h1
  have h2 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] (0 / 2)) :=
    le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq 0)
  rw [zero_div] at h2
  refine (h1.comp h2).congr (fun s ↦ ?_)
  rw [completedHurwitzZetaEven, Function.comp_apply]
  ring_nf

end FEPair

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- Auxiliary lemma for `completedHurwitzZetaEven_eq_tsum_int`, computing the Mellin transform of an
individual term in the series. -/
theorem mellin_exp_neg_pi_mul_sq {s : ℂ} (hs : 0 < s.re) {n : ℝ} (hn : n ≠ 0) :
    mellin (fun t ↦ rexp (-π * n ^ 2 * t) : ℝ → ℂ) (s / 2) =
      Gamma (s / 2) * π ^ (-s / 2) / |n| ^ s := by
  have : 0 < (s / 2).re
  · simpa only [← ofReal_ofNat, div_ofReal_re] using div_pos hs two_pos
  rw [Complex.Gamma_eq_integral this, GammaIntegral_eq_mellin]
  have : 0 < π * n ^ 2 := by positivity
  have := mellin_comp_mul_left (fun t ↦ ↑(rexp (-t)) : ℝ → ℂ) (s / 2) this
  simp_rw [← neg_mul, smul_eq_mul] at this
  rw [this, mul_div_assoc, mul_comm (mellin _ _), ofReal_mul,
    mul_cpow_ofReal_nonneg pi_pos.le (sq_nonneg _), neg_div]
  congr 2
  rw [cpow_neg, ← _root_.sq_abs, pow_two, ofReal_mul, mul_cpow_ofReal_nonneg (abs_nonneg _)
    (abs_nonneg _), ← cpow_add, add_halves']
  rwa [ofReal_ne_zero, abs_ne_zero]
#align integral_cpow_mul_exp_neg_pi_mul_sq mellin_exp_neg_pi_mul_sq

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ - {0}`). -/
lemma hasSum_int_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else
    Gamma (s / 2) * π ^ (-s / 2) * cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2)
    (completedCosZeta a s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (n : ℤ) (t : ℝ) : ℂ :=
    t ^ (s / 2 - 1) * (if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) / 2
  let f (t : ℝ) : ℂ := (t : ℂ) ^ (s / 2 - 1) * (cosKernel a t - 1) / 2
  let bound (n : ℤ) (t : ℝ) : ℝ :=
    if n = 0 then 0 else t ^ (s.re / 2 - 1) * rexp (-π * n ^ 2 * t) / 2
  have hF_meas (n : ℤ) : AEStronglyMeasurable (F n) μ
  · by_cases hn : n = 0
    · simp_rw [hn, if_true, mul_zero, zero_div]
      exact aestronglyMeasurable_const
    · simp_rw [hn, if_false]
      refine ((ContinuousOn.mul ?_ ?_).div_const _).aestronglyMeasurable measurableSet_Ioi
      · exact ContinuousAt.continuousOn
          fun t ht ↦ continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
      · apply Continuous.continuousOn
        continuity
  have h_lim : ∀ᵐ (t : ℝ) ∂μ, HasSum (fun n ↦ F n t) (f t)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact ((hasSum_int_cosKernel₀ a ht).mul_left _).div_const _
  have h_bound (n : ℤ) : ∀ᵐ (t : ℝ) ∂μ, ‖F n t‖ ≤ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    by_cases hn : n = 0
    · simp_rw [hn, if_true, mul_zero, zero_div, norm_zero, le_refl]
    · simp_rw [hn, if_false]
      rw [norm_div, ← ofReal_ofNat, norm_real, ofReal_ofNat, norm_two,
        div_le_div_right two_pos, norm_mul, norm_mul, norm_real, norm_of_nonneg (exp_pos _).le,
        ← mul_assoc, mul_le_mul_iff_of_pos_right (exp_pos _), Complex.norm_eq_abs,
        abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ← ofReal_ofNat, div_ofReal_re,
        (by { push_cast; ring } : (2 : ℝ) * π * I * a * n = ↑(2 * π * a * n : ℝ) * I),
        Complex.norm_eq_abs, Complex.abs_exp, mul_I_re, ofReal_im, neg_zero, Real.exp_zero,
        mul_one]
  have bound_hasSum (t : ℝ) (ht : 0 < t) :
      HasSum (bound · t) (t ^ (s.re / 2 - 1) * (cosKernel 0 t - 1) / 2)
  · have := hasSum_int_evenKernel₀ 0 ht
    simp_rw [add_zero, QuotientAddGroup.mk_zero, neg_zero, if_true,
      evenKernel_eq_cosKernel_of_zero, Int.cast_eq_zero] at this
    convert (this.mul_left (t ^ (s.re / 2 - 1))).div_const (2 : ℝ) using 2 with n
    split_ifs with hn
    · simp_rw [hn, if_true, mul_zero, zero_div]
    · simp_rw [hn, if_false]
  have bound_summable : ∀ᵐ (t : ℝ) ∂μ, Summable fun (n : ℤ) ↦ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact (bound_hasSum t ht).summable
  have bound_integrable : Integrable (fun (t : ℝ) ↦ ∑' (n : ℤ), bound n t) μ
  · erw [← IntegrableOn,
      integrableOn_congr_fun (fun t ht ↦ (bound_hasSum t ht).tsum_eq) measurableSet_Ioi]
    apply Integrable.div_const
    have : 1 / 2 < ((s.re : ℂ) / 2).re
    · rwa [← ofReal_ofNat, div_ofReal_re, ofReal_re, div_lt_div_right two_pos]
    have := ((hurwitzEvenFEPair 0).symm.hasMellin this).1.re
    refine IntegrableOn.congr_fun this (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
    rw [smul_eq_mul, (by push_cast; rfl : (s.re : ℂ) / 2 - 1 = ↑(s.re / 2 - 1)),
      ← ofReal_cpow ht.le, IsROrC.re_eq_complex_re, re_ofReal_mul]
    rfl
  convert (hasSum_integral_of_dominated_convergence
      bound hF_meas h_bound bound_summable bound_integrable h_lim) using 2 with n
  · -- show the individual terms match up
    by_cases hn : n = 0
    · simp_rw [hn, if_true, mul_zero, zero_div]
      rw [integral_zero]
    simp_rw [hn, if_false, integral_div]
    congr 1
    simp_rw [← mul_assoc _ (cexp _), mul_comm _ (cexp _), mul_assoc (cexp _),
        integral_mul_left, mul_div_assoc _ (_ * _)]
    congr 1
    simpa only [← Int.cast_abs, ofReal_int_cast]
      using (mellin_exp_neg_pi_mul_sq (zero_lt_one.trans hs) (Int.cast_ne_zero.mpr hn)).symm
  · -- show ∫ f = Hurwitz zeta
    rw [completedCosZeta]
    have : 1 / 2 < re (s / 2) := by rwa [← ofReal_ofNat, div_ofReal_re, div_lt_div_right two_pos]
    convert congr_arg (· / 2) ((hurwitzEvenFEPair a).symm.hasMellin this).2.symm
    simp only [f, mellin, integral_div]
    rfl

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
lemma hasSum_nat_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Gamma (s / 2) * π ^ (-s / 2) * Real.cos (2 * π * a * n) / (n : ℂ) ^ s)
    (completedCosZeta a s) := by
  have := (hasSum_int_completedCosZeta a hs).sum_nat_of_sum_int
  simp_rw [if_true, add_zero, neg_eq_zero, Nat.cast_eq_zero, abs_neg, Nat.abs_cast] at this
  convert this using 2 with n
  split_ifs with h
  · have : s ≠ 0 := fun p ↦ (not_lt.mpr zero_le_one) (zero_re ▸ p ▸ hs)
    simp_rw [h, Nat.cast_zero, zero_cpow this, div_zero, add_zero]
  simp only [ofReal_cos, Complex.cos, push_cast]
  ring_nf

/-- Formula for `completedHurwitzZetaEven` as a Dirichlet series in the convergence range. -/
lemma hasSum_int_completedHurwitzZetaEven (a : ℝ) (s : ℂ) (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ if n = -a then 0 else
    Gamma (s / 2) * π ^ (-s / 2) / (↑|n + a| : ℂ) ^ s / 2)
    (completedHurwitzZetaEven a s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (n : ℤ) (t : ℝ) : ℂ :=
    if n = -a then 0 else t ^ (s / 2 - 1) * rexp (-π * (n + a) ^ 2 * t) / 2
  let f (t : ℝ) : ℂ := (t : ℂ) ^ (s / 2 - 1) *
    (evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0)) / 2
  have hF_meas (n : ℤ) : AEStronglyMeasurable (F n) μ
  · simp only [F]
    split_ifs with h
    · measurability
    · refine ((ContinuousOn.mul ?_ ?_).div_const _).aestronglyMeasurable measurableSet_Ioi
      · apply ContinuousAt.continuousOn
        exact fun t ht ↦ continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
      · exact Continuous.continuousOn (by continuity)
  have h_lim : ∀ᵐ (t : ℝ) ∂μ, HasSum (fun n ↦ F n t) (f t)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have := hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)
    convert (this.mul_left ((t : ℂ) ^ (s / 2 - 1))).div_const 2 with n
    · simp only [F]
      split_ifs <;> simp only [ofReal_zero, mul_zero, zero_div]
    · split_ifs <;> simp only [ofReal_sub, ofReal_one, sub_zero]
  let bound (n : ℤ) (t : ℝ) : ℝ :=
    if n = -a then 0 else t ^ (s.re / 2 - 1) * rexp (-π * (n + a) ^ 2 * t) / 2
  have h_bound (n : ℤ) : ∀ᵐ (t : ℝ) ∂μ, ‖F n t‖ ≤ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    simp only [F, bound]
    split_ifs
    · rw [norm_zero]
    · rw [norm_div, ← ofReal_ofNat, norm_real 2, ofReal_ofNat, norm_two,
        div_le_div_right two_pos, norm_mul, norm_real, norm_of_nonneg (exp_pos _).le,
        mul_le_mul_iff_of_pos_right (exp_pos _), Complex.norm_eq_abs,
        abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ← ofReal_ofNat, div_ofReal_re]
  have bound_hasSum (t : ℝ) (ht : 0 < t) : HasSum (bound · t)
      (t ^ (s.re / 2 - 1) * (evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0)) / 2)
  · convert ((hasSum_int_evenKernel₀ a ht).mul_left _).div_const 2 using 2 with n
    simp only [mul_ite, bound]
    split_ifs with h <;> simp only [mul_zero, zero_div]
  have bound_summable : ∀ᵐ (t : ℝ) ∂μ, Summable fun (n : ℤ) ↦ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact (bound_hasSum t ht).summable
  have bound_integrable : Integrable (fun (t : ℝ) ↦ ∑' (n : ℤ), bound n t) μ
  · erw [← IntegrableOn,
      integrableOn_congr_fun (fun t ht ↦ (bound_hasSum t ht).tsum_eq) measurableSet_Ioi]
    apply Integrable.div_const
    have : 1 / 2 < ((s.re : ℂ) / 2).re
    · rwa [← ofReal_ofNat, div_ofReal_re, ofReal_re, div_lt_div_right two_pos]
    have := ((hurwitzEvenFEPair a).hasMellin this).1.re
    refine IntegrableOn.congr_fun this (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
    simp_rw [smul_eq_mul, (by push_cast; rfl : (s.re : ℂ) / 2 - 1 = ↑(s.re / 2 - 1)),
      ← ofReal_cpow ht.le, IsROrC.re_eq_complex_re, re_ofReal_mul, sub_re]
    simp only [hurwitzEvenFEPair, apply_ite re, one_re, zero_re, ofReal_re, Function.comp_apply]
  convert MeasureTheory.hasSum_integral_of_dominated_convergence
      bound hF_meas h_bound bound_summable bound_integrable h_lim using 2 with n
  · -- show the individual terms match up
    simp only [F]
    split_ifs with h
    · simp only [integral_zero]
    · rw [integral_div]
      exact congr_arg (· / 2) (mellin_exp_neg_pi_mul_sq (zero_lt_one.trans hs)
        (h ∘ add_eq_zero_iff_eq_neg.mp)).symm
  · -- show ∫ f = Hurwitz zeta
    rw [completedHurwitzZetaEven]
    have : 1 / 2 < re (s / 2) := by rwa [← ofReal_ofNat, div_ofReal_re, div_lt_div_right two_pos]
    convert congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin this).2.symm
    simp only [integral_div]
    rfl
