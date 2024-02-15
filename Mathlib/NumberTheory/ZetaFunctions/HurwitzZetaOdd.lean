/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.ZetaFunctions.HurwitzZetaEven
import Mathlib.Data.Real.Sign
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`completedHurwitzZetaOdd a s = 1 / 2 * □ * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`completedSinZeta a s = □ * ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`

where `□` denotes a Gamma factor. The term for `n = -a` in the first sum is understood as 0
if `a` is an integer, as is the term for `n = 0` is omitted in the second sum (for all `a`). Note
that these are differentiable everywhere, unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed cosine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* [TODO] `completedHurwitzZetaOdd_eq_tsum_int` and `completedSinZeta_eq_tsum_nat`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/

noncomputable section

open Complex hiding abs_of_nonneg
open Filter Topology Asymptotics Real Set MeasureTheory

section defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Odd Hurwitz zeta kernel (function whose Mellin transform will be the odd part of the completed
Hurwitz zeta function). See `oddKernel_def` for the defining formula, and `hasSum_int_oddKernel`
for an expression as a sum over `ℤ`.
-/
@[irreducible] def oddKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun a : ℝ ↦ re (cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)))) 1 by
      intro a
      dsimp only
      rw [ofReal_add, ofReal_one, add_mul, one_mul, add_mul, jacobiTheta₂'_add_left',
        jacobiTheta₂_add_left']
      field_simp [pi_pos.ne']
      simp_rw [mul_add, mul_comm ((a : ℂ) + 1) _, ← mul_assoc, ← Complex.exp_add]
      ring_nf
      rw [I_sq]
      ring_nf).lift a

lemma oddKernel_def (a x : ℝ) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
  rw [oddKernel, Function.Periodic.lift_coe]
  simp only [neg_mul, re_eq_add_conj, map_mul, ← exp_conj, map_neg,
    conj_ofReal, map_pow, map_add, map_div₀, jacobiTheta₂'_conj, conj_I, mul_neg, neg_neg,
    jacobiTheta₂'_neg_left, map_ofNat, jacobiTheta₂_conj, jacobiTheta₂_neg_left]
  ring_nf

lemma hasSum_int_oddKernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x) := by
  rw [← hasSum_ofReal, oddKernel_def a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re] : 0 < im (I * x))
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re] : 0 < im (I * x))
  convert ((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left _ using 2 with n
  rw [jacobiTheta₂'_term, mul_assoc (2 * π * I), mul_div_cancel_left, ← add_mul,
    ← mul_assoc, mul_comm _ (n + a : ℂ), mul_assoc (n + a : ℂ), jacobiTheta₂_term,
    ← Complex.exp_add]
  · push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · simpa only [mul_ne_zero_iff, ofReal_ne_zero] using ⟨⟨two_ne_zero, pi_pos.ne'⟩, I_ne_zero⟩

lemma oddKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : oddKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_eq_zero, oddKernel_def, jacobiTheta₂_undef, jacobiTheta₂'_undef, zero_div, zero_add,
    mul_zero, mul_zero] <;>
  rwa [I_mul_im, ofReal_re]

/-- Auxiliary function appearing in the functional equation for the odd Hurwitz zeta kernel, equal
to `∑ (n : ℕ), 2 * n * sin (2 * π * n * a) * exp (-π * n ^ 2 * x)`. See `hasSum_nat_sinKernel`
for the defining sum. -/
@[irreducible] def sinKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    intro ξ; simp_rw [ofReal_add, ofReal_one, jacobiTheta₂'_add_left]).lift a

lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
  rw [sinKernel, Function.Periodic.lift_coe, re_eq_add_conj, map_div₀, jacobiTheta₂'_conj]
  simp_rw [map_mul, conj_I, conj_ofReal, map_neg, map_ofNat, neg_mul, neg_neg]
  ring

lemma hasSum_int_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℤ ↦ -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a t) := by
  rw [sinKernel_def]
  have := hasSum_jacobiTheta₂'_term a (by rwa [I_mul_im, ofReal_re])
  convert this.div_const _ using 2 with n
  rw [jacobiTheta₂'_term, jacobiTheta₂_term, ofReal_exp, mul_assoc (-I * n), ← Complex.exp_add]
  field_simp [pi_pos.ne']
  ring_nf
  rw [I_sq]
  ring_nf

lemma hasSum_nat_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℕ ↦ 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
    (sinKernel ↑a t) := by
  rw [← hasSum_ofReal]
  convert (hasSum_int_sinKernel a ht).sum_nat_of_sum_int using 2 with n
  · simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_ofNat, ofReal_nat_cast,
      ofReal_ofNat, ← add_mul, ofReal_sin, Complex.sin]
    push_cast
    ring_nf
  · simp

lemma sinKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : sinKernel a x = 0 := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef, zero_div]
  rwa [I_mul_im, ofReal_re]

lemma oddKernel_neg (a : UnitAddCircle) (x : ℝ) :
    oddKernel (-a) x = -oddKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, ofReal_neg, ofReal_neg,
    oddKernel_def, neg_mul (a' : ℂ), neg_mul (a' : ℂ), neg_mul (a' * I),
    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left]
  ring_nf

lemma oddKernel_zero (x : ℝ) : oddKernel 0 x = 0 := by
  have := oddKernel_neg 0 x
  rwa [neg_zero, ← add_eq_zero_iff_eq_neg, ← two_mul, mul_eq_zero, eq_false_intro two_ne_zero,
    false_or] at this

lemma sinKernel_neg (a : UnitAddCircle) (x : ℝ) :
    sinKernel (-a) x = -sinKernel a x := by
  induction' a using QuotientAddGroup.induction_on' with a'
  rw [← ofReal_inj, ← QuotientAddGroup.mk_neg, ofReal_neg, sinKernel_def, sinKernel_def, ofReal_neg,
    jacobiTheta₂'_neg_left, neg_div]

lemma sinKernel_zero (x : ℝ) : sinKernel 0 x = 0 := by
  have := sinKernel_neg 0 x
  rwa [neg_zero, ← add_eq_zero_iff_eq_neg, ← two_mul, mul_eq_zero, eq_false_intro two_ne_zero,
    false_or] at this

/-- The odd kernel is continuous on `Ioi 0`. -/
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  change ContinuousOn (fun x ↦ re (oddKernel a' x : ℂ)) (Ioi 0)
  apply Complex.continuous_re.comp_continuousOn
  simp_rw [oddKernel_def a']
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · exact Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)
  · have hx' : 0 < im (I * x) := by rwa [I_mul_im, ofReal_re]
    have hf : Continuous fun u : ℝ ↦ (a' * I * u, I * u) := by continuity
    apply ContinuousAt.add
    · exact ((continuousAt_jacobiTheta₂' (a' * I * x) hx').comp
        (f := fun u : ℝ ↦ (a' * I * u, I * u)) hf.continuousAt).div_const _
    · exact continuousAt_const.mul <| (continuousAt_jacobiTheta₂ (a' * I * x) hx').comp
        (f := fun u : ℝ ↦ (a' * I * u, I * u)) hf.continuousAt

lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
  induction' a using QuotientAddGroup.induction_on' with a'
  change ContinuousOn (fun x ↦ re (sinKernel a' x : ℂ)) (Ioi 0)
  apply Complex.continuous_re.comp_continuousOn
  simp_rw [sinKernel_def]
  apply (ContinuousAt.continuousOn (fun x hx ↦ ?_)).div_const
  have h := continuousAt_jacobiTheta₂' a' (by rwa [I_mul_im, ofReal_re] : 0 < im (I * x))
  exact h.comp (f := fun u : ℝ ↦ ((a' : ℂ), I * u)) (continuous_prod_mk.mpr ⟨continuous_const,
    continuous_const.mul continuous_ofReal⟩).continuousAt

lemma oddKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    oddKernel a x = 1 / x ^ (3 / 2 : ℝ) * sinKernel a (1 / x) := by
  -- first reduce to `0 < x`
  rcases le_or_lt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction' a using QuotientAddGroup.induction_on' with a
  rw [← ofReal_inj, ofReal_mul, oddKernel_def, sinKernel_def, jacobiTheta₂'_functional_equation a]
  -- What remains is an annoyingly fiddly rearrangement. We use `generalize` to replace complicated
  -- subexpressions with abstract variables that `field_simp` and `ring_nf` can work with. The
  -- sticky point is that we need to be careful about branches of complex powers.
  --
  -- *First step*: get rid of the theta-functions themselves.
  have : -1 / (I * ↑(1 / x)) = I * x := by { push_cast; field_simp; ring_nf }
  rw [this]
  have : a / (I * ↑(1 / x)) = -(a * I * x) := by { push_cast; field_simp; ring_nf }
  rw [this, jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left]
  generalize jacobiTheta₂ (↑a * I * ↑x) (I * ↑x) = J
  generalize jacobiTheta₂' (↑a * I * ↑x) (I * ↑x) = J'
  -- *Second step*: get rid of the complex exponential.
  have : -π * I * a ^ 2 / (I * ↑(1 / x)) = -π * a ^ 2 * x
  · push_cast; field_simp; ring_nf; rw [I_sq]; ring_nf
  rw [this]
  generalize cexp (-π * a ^ 2 * x) = C
  -- *Third step*: rewrite all the powers in terms of `y = ↑(x ^ (1 / 2))`.
  generalize hy : (↑(x ^ (1 / 2 : ℝ)) : ℂ) = y
  have : ↑(1 / x ^ (3 / 2 : ℝ)) = 1 / y ^ 3
  · rw [← hy, ← ofReal_pow, ← rpow_mul_natCast hx.le]; norm_num
  rw [this]
  have : 1 / (-I * (I * ↑(1 / x))) ^ (1 / 2 : ℂ) = y
  · rw [← hy]
    push_cast; field_simp; rw [one_div, one_div, inv_cpow, inv_inv, ofReal_cpow hx.le]; norm_num
    rw [arg_ofReal_of_nonneg hx.le]
    exact pi_pos.ne
  rw [this]
  have : ↑(1 / x) = 1 / y ^ 2
  · rw [← hy, one_div, one_div, ofReal_inv, inv_inj, ← ofReal_pow, ofReal_inj,
      ← rpow_mul_natCast hx.le]; norm_num
  rw [this]
  -- *Fourth step*: use `field_simp` and `ring_nf` (twice, because we first need to bring the
  -- powers of `I` together)
  have hy' : y ≠ 0
  · rw [← hy]; exact ofReal_ne_zero.mpr (rpow_pos_of_pos hx _).ne'
  field_simp [pi_pos.ne']
  ring_nf
  rw [(by norm_num : I ^ 3 = I ^ (2 + 1)), pow_add, I_sq]
  ring_nf
  -- *Fifth step*: breathe a sigh of relief and go to bed.

/-!
## Asymptotics as `t → ∞`
-/

/-- The function `sinKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (sinKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction' a using QuotientAddGroup.induction_on with a
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat, ← (hasSum_nat_sinKernel a ht).tsum_eq]
  apply tsum_of_norm_bounded (g := fun n ↦ 2 * HurwitzKernelBounds.f_nat 1 0 t n)
  · exact (HurwitzKernelBounds.summable_f_nat 1 0 ht).hasSum.mul_left _
  · intro n
    rw [norm_mul, norm_mul, norm_mul, norm_two, mul_assoc, mul_assoc,
      mul_le_mul_iff_of_pos_left two_pos, HurwitzKernelBounds.f_nat, pow_one, add_zero,
      norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, Nat.abs_cast, ← mul_assoc,
      mul_le_mul_iff_of_pos_right (exp_pos _)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_sin_le_one _)

/-- The function `oddKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (oddKernel a) (fun x ↦ Real.exp (-p * x)) := by
  obtain ⟨b, _, rfl⟩ := a.eq_coe_Ico
  let ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa only [← (hasSum_int_oddKernel b ht).tsum_eq, Real.norm_eq_abs, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, pow_one, norm_mul, abs_of_nonneg (exp_pos _).le] using
    (norm_tsum_le_tsum_norm (hasSum_int_oddKernel b ht).summable.norm)

section FEPair
/-!
## Construction of a FE-pair
-/

/-- A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`. -/
def hurwitzOddFEPair (a : UnitAddCircle) : StrongFEPair ℂ where
  f := ofReal' ∘ oddKernel a
  g := ofReal' ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2
  hk := by norm_num
  hε := one_ne_zero
  f₀ := 0
  hf₀ := by rfl
  g₀ := 0
  hg₀ := by rfl
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_oddKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simp_rw [Function.comp_def, sub_zero, norm_real]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_sinKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simp_rw [Function.comp_def, sub_zero, norm_real]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by simp_rw [Function.comp_apply, one_mul, smul_eq_mul, ← ofReal_mul,
    oddKernel_functional_equation a, one_div x, one_div x⁻¹, inv_rpow (le_of_lt hx), one_div,
    inv_inv]

/-- The entire function of `s` which agrees with
`1 / 2 * Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℤ), sgn (n + a) / |n + a| ^ s`
for `1 < re s`.
-/
def completedHurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).Λ ((s + 1) / 2)) / 2

lemma differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaOdd a) :=
  ((hurwitzOddFEPair a).differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-- The entire function of `s` which agrees with
` Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℕ), sin (2 * π * a * n) / n ^ s`
for `1 < re s`.
-/
def completedSinZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).symm.Λ ((s + 1) / 2)) / 2

lemma differentiable_completedSinZeta (a : UnitAddCircle) :
    Differentiable ℂ (completedSinZeta a) :=
  ((hurwitzOddFEPair a).symm.differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-!
## Parity and functional equations
-/

lemma completedHurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd (-a) s = -completedHurwitzZetaOdd a s := by
  simp only [completedHurwitzZetaOdd, StrongFEPair.Λ, hurwitzOddFEPair, mellin, Function.comp_def,
    oddKernel_neg, ofReal_neg, smul_neg]
  rw [integral_neg, neg_div]

lemma completedSinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta (-a) s = -completedSinZeta a s := by
  simp only [completedSinZeta, StrongFEPair.Λ, mellin, StrongFEPair.symm, WeakFEPair.symm,
    hurwitzOddFEPair, Function.comp_def, sinKernel_neg, ofReal_neg, smul_neg]
  rw [integral_neg, neg_div]

/-- Functional equation for the odd Hurwitz zeta function. -/
lemma completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s := by
  erw [completedHurwitzZetaOdd, completedSinZeta,
    (by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : ℝ) - (s + 1) / 2),
    (hurwitzOddFEPair a).functional_equation ((s + 1) / 2), one_smul]

/-- Functional equation for the odd Hurwitz zeta function (alternative form). -/
lemma completedSinZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta a (1 - s) = completedHurwitzZetaOdd a s := by
  rw [← completedHurwitzZetaOdd_one_sub, sub_sub_cancel]

/-!
## Relation to the Dirichlet series for `0 ≪ re s`
-/

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`).

We need to assume a non-optimal bound on `re s` here (it should work for `1 < re s`) because our
bounds on the norms of zeta kernels as `t → 0` are non-optimal. -/
lemma hasSum_int_completedSinZeta (a : ℝ) {s : ℂ} (hs : 3 < re s) :
    HasSum (fun n : ℤ ↦ Gamma ((s + 1)/ 2) * π ^ (-(s + 1) / 2) *
    (-I) * n.sign * cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2)
    (completedSinZeta a s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (n : ℤ) (t : ℝ) : ℂ :=
    t ^ ((s + 1) / 2 - 1) * (-I * n) * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t) / 2
  let f (t : ℝ) : ℂ := (t : ℂ) ^ ((s + 1) / 2 - 1) * sinKernel a t / 2
  let bound (n : ℤ) (t : ℝ) : ℝ := t ^ ((s + 1).re / 2 - 1) * |n| * rexp (-π * n ^ 2 * t) / 2
  have hF_meas (n : ℤ) : AEStronglyMeasurable (F n) μ
  · refine (((ContinuousOn.mul ?_ ?_).mul ?_).div_const _).aestronglyMeasurable measurableSet_Ioi
    · refine (ContinuousAt.continuousOn (fun x hx ↦ ?_)).mul continuousOn_const
      exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt hx)
    all_goals { apply Continuous.continuousOn; continuity }
  have h_lim : ∀ᵐ (t : ℝ) ∂μ, HasSum (fun n ↦ F n t) (f t)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    simpa only [mul_assoc] using ((hasSum_int_sinKernel a ht).mul_left _).div_const _
  have h_bound (n : ℤ) : ∀ᵐ (t : ℝ) ∂μ, ‖F n t‖ ≤ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    rw [norm_div, ← ofReal_ofNat, norm_real, ofReal_ofNat, norm_two, div_le_div_right two_pos,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_real, norm_of_nonneg (exp_pos _).le,
      mul_le_mul_iff_of_pos_right (exp_pos _), norm_I, one_mul, Complex.norm_eq_abs,
      abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ← ofReal_ofNat, div_ofReal_re,
      (by { push_cast; ring } : (2 : ℝ) * π * I * a * n = ↑(2 * π * a * n : ℝ) * I),
      Complex.norm_eq_abs, Complex.norm_eq_abs, Complex.abs_exp, mul_I_re, ofReal_im, neg_zero,
      Real.exp_zero, mul_one, ← ofReal_int_cast, abs_ofReal, Int.cast_abs]
  have bound_hasSum (t : ℝ) (ht : 0 < t) :
      HasSum (bound · t) (t ^ ((s + 1).re / 2 - 1) * HurwitzKernelBounds.F_int 1 0 t / 2)
  · simp only [F, bound, HurwitzKernelBounds.F_int]
    simp_rw [mul_assoc (t ^ (_ : ℝ))]
    apply HasSum.div_const
    apply HasSum.mul_left
    convert (HurwitzKernelBounds.summable_f_int 1 0 ht).hasSum using 2 with n
    simp only [HurwitzKernelBounds.f_int, add_zero, pow_one, Int.cast_abs]
  have bound_summable : ∀ᵐ (t : ℝ) ∂μ, Summable fun (n : ℤ) ↦ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact (bound_hasSum t ht).summable
  have bound_integrable : Integrable (fun (t : ℝ) ↦ ∑' (n : ℤ), bound n t) μ
  · erw [← IntegrableOn,
      integrableOn_congr_fun (fun t ht ↦ (bound_hasSum t ht).tsum_eq) measurableSet_Ioi]
    apply Integrable.div_const
    let ⟨R, hR⟩ := exists_gt ((s + 1).re / 2)
    apply mellin_convergent_of_isBigO_scalar (hs_top := hR) (b := 2)
    · apply ContinuousOn.locallyIntegrableOn
      exact HurwitzKernelBounds.continuousOn_F_int 1 0
      exact measurableSet_Ioi
    · let ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one 0
      exact hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp _).isBigO
    · refine (HurwitzKernelBounds.isBigO_nhds_zero_F_int_one 0).trans (EventuallyEq.isBigO ?_)
      rw [EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards with t (ht : 0 < t)
      rw [rpow_neg ht.le, one_div, (by simp : (2 : ℝ) = ↑(2 : ℕ)), rpow_nat_cast]
    · rw [add_re, one_re]
      linarith
  have step1 : HasSum (fun n : ℤ ↦ Gamma ((s + 1)/ 2) * π ^ (-(s + 1) / 2) *
      (-I * n) * cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ (s + 1) / 2)
      (completedSinZeta a s)
  · convert (hasSum_integral_of_dominated_convergence
      bound hF_meas h_bound bound_summable bound_integrable h_lim) using 2 with n
    · simp_rw [integral_div]
      congr 1
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [Int.cast_zero, mul_zero, zero_mul, zero_div]
        rw [integral_zero] -- why doesn't this work as `simp`?
      · simp_rw [mul_assoc _ (-I * n), mul_comm _ (-I * n * _),
          mul_assoc (-I * n * _), integral_mul_left, mul_div_assoc (-I * n * _)]
        congr 1
        have : 0 < (s + 1).re := by { rw [add_re, one_re]; linarith }
        simpa only [← Int.cast_abs, ofReal_int_cast]
          using (mellin_exp_neg_pi_mul_sq this (Int.cast_ne_zero.mpr hn)).symm
    · rw [completedSinZeta]
      convert congr_arg (· / 2) ((hurwitzOddFEPair a).symm.hasMellin ((s + 1) / 2)).2.symm
      simp only [f, mellin, integral_div]
      rfl
  convert step1 using 3 with n
  simp_rw [mul_comm _ (cexp _), mul_assoc, mul_div_assoc]
  congr 4
  rcases n with m | m
  rcases m with rfl | m
  · simp
  · simp only [Int.ofNat_eq_coe, Nat.cast_succ, Int.sign_of_add_one, Int.cast_one]
    rw [abs_of_nonneg (by positivity), cpow_add _ _ (Int.cast_ne_zero.mpr (by positivity)),
      cpow_one, mul_comm, ← div_div,
      div_self (Int.cast_ne_zero.mpr (by positivity : (m : ℤ) + 1 ≠ 0))]
  · rw [Int.negSucc_eq, Int.sign_neg, Int.cast_neg, neg_div, Int.cast_neg, neg_div, abs_neg]
    simp only [Int.ofNat_eq_coe, Nat.cast_succ, Int.sign_of_add_one, Int.cast_one]
    rw [abs_of_nonneg (by positivity), cpow_add _ _ (Int.cast_ne_zero.mpr (by positivity)),
      cpow_one, mul_comm, ← div_div,
      div_self (Int.cast_ne_zero.mpr (by positivity : (m : ℤ) + 1 ≠ 0))]

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
lemma hasSum_nat_completedSinZeta (a : ℝ) {s : ℂ} (hs : 3 < re s) :
    HasSum (fun n : ℕ ↦ Gamma ((s + 1)/ 2) * π ^ (-(s + 1) / 2) *
    Real.sin (2 * π * a * n) / (n : ℂ) ^ s) (completedSinZeta a s) := by
  have := (hasSum_int_completedSinZeta a hs).sum_nat_of_sum_int
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_ofNat, ← add_div] at this
  convert this using 2 with n
  rw [div_right_comm]
  rcases eq_or_ne n 0 with rfl | h
  · simp
  simp_rw [Int.sign_coe_nat_of_nonzero h, Int.cast_one]
  rw [ofReal_sin, Complex.sin]
  cancel_denoms
  ring_nf

/-- Formula for `completedHurwitzZetaOdd` as a Dirichlet series in the convergence range.

We need to assume a non-optimal bound on `re s` here (it should work for `1 < re s`) because our
bounds on the norms of zeta kernels as `t → 0` are non-optimal. -/
lemma hasSum_int_completedHurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 3 < re s) :
    HasSum (fun n : ℤ ↦ Gamma ((s + 1)/ 2) * π ^ (-(s + 1) / 2) *
    Real.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2) (completedHurwitzZetaOdd a s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (n : ℤ) (t : ℝ) : ℂ :=
    t ^ ((s + 1) / 2 - 1) * (n + a) * rexp (-π * (n + a) ^ 2 * t) / 2
  let f (t : ℝ) : ℂ := (t : ℂ) ^ ((s + 1) / 2 - 1) * oddKernel a t / 2
  let bound (n : ℤ) (t : ℝ) : ℝ :=
    t ^ ((s + 1).re / 2 - 1) * |n + a| * rexp (-π * (n + a) ^ 2 * t) / 2
  have hF_meas (n : ℤ) : AEStronglyMeasurable (F n) μ
  · refine (((ContinuousOn.mul ?_ ?_).mul ?_).div_const _).aestronglyMeasurable measurableSet_Ioi
    · refine ContinuousAt.continuousOn (fun x hx ↦ ?_)
      exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt hx)
    all_goals { apply Continuous.continuousOn; continuity }
  have h_lim : ∀ᵐ (t : ℝ) ∂μ, HasSum (fun n ↦ F n t) (f t)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    simpa only [ofReal_mul, ofReal_add, ← mul_assoc] using
      ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).mul_left _).div_const _
  have h_bound (n : ℤ) : ∀ᵐ (t : ℝ) ∂μ, ‖F n t‖ ≤ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    simp_rw [norm_div, norm_mul, ← ofReal_ofNat, norm_real, ofReal_ofNat, norm_two,
      div_le_div_right (α := ℝ) two_pos, norm_of_nonneg (exp_pos _).le,
      mul_le_mul_iff_of_pos_right (exp_pos _), Complex.norm_eq_abs,
      abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ← ofReal_ofNat, div_ofReal_re,
      ← ofReal_int_cast, ← ofReal_add, abs_ofReal]
    rfl
  have bound_hasSum (t : ℝ) (ht : 0 < t) :
      HasSum (bound · t) (t ^ ((s + 1).re / 2 - 1) * HurwitzKernelBounds.F_int 1 a t / 2)
  · simp only [F, bound, HurwitzKernelBounds.F_int, mul_assoc (t ^ (_ : ℝ))]
    refine (HasSum.mul_left _ ?_).div_const _
    convert (HurwitzKernelBounds.summable_f_int 1 a ht).hasSum using 2 with n
    simp only [HurwitzKernelBounds.f_int, add_zero, pow_one, Int.cast_abs]
  have bound_summable : ∀ᵐ (t : ℝ) ∂μ, Summable fun (n : ℤ) ↦ bound n t
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun t ht ↦ (bound_hasSum t ht).summable)
  have bound_integrable : Integrable (fun (t : ℝ) ↦ ∑' (n : ℤ), bound n t) μ
  · erw [← IntegrableOn,
      integrableOn_congr_fun (fun t ht ↦ (bound_hasSum t ht).tsum_eq) measurableSet_Ioi]
    apply Integrable.div_const
    let ⟨R, hR⟩ := exists_gt ((s + 1).re / 2)
    apply mellin_convergent_of_isBigO_scalar (hs_top := hR) (b := 2)
    · exact (HurwitzKernelBounds.continuousOn_F_int 1 a).locallyIntegrableOn measurableSet_Ioi
    · let ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one a
      exact hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp _).isBigO
    · refine (HurwitzKernelBounds.isBigO_nhds_zero_F_int_one a).trans (EventuallyEq.isBigO ?_)
      rw [EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards with t (ht : 0 < t)
      rw [rpow_neg ht.le, one_div, (by simp : (2 : ℝ) = ↑(2 : ℕ)), rpow_nat_cast]
    · rw [add_re, one_re]
      linarith
  have step1 : HasSum (fun n : ℤ ↦ Gamma ((s + 1)/ 2) * π ^ (-(s + 1) / 2) *
      (n + a) / (↑|n + a| : ℂ) ^ (s + 1) / 2) (completedHurwitzZetaOdd a s)
  · convert (hasSum_integral_of_dominated_convergence
      bound hF_meas h_bound bound_summable bound_integrable h_lim) using 2 with n
    · simp_rw [integral_div]
      congr 1
      rcases eq_or_ne ↑n (-a) with hn | hn
      · simp_rw [← ofReal_int_cast, hn, ofReal_neg, neg_add_self, mul_zero, zero_mul, zero_div]
        rw [integral_zero] -- why doesn't this work as `simp`?
      · simp_rw [mul_comm _ ((n : ℂ) + a), mul_assoc ((n : ℂ) + a), integral_mul_left,
          mul_div_assoc ((n : ℂ) + a)]
        congr 1
        have hs' : 0 < (s + 1).re := by { rw [add_re, one_re]; linarith }
        refine (mellin_exp_neg_pi_mul_sq hs' (hn ∘ add_eq_zero_iff_eq_neg.mp)).symm
    · rw [completedHurwitzZetaOdd]
      convert congr_arg (· / 2) ((hurwitzOddFEPair a).hasMellin ((s + 1) / 2)).2.symm
      simp only [f, mellin, integral_div]
      rfl
  convert step1 using 3 with n
  simp_rw [mul_assoc, mul_div_assoc, ← ofReal_int_cast, ← ofReal_add]
  generalize n + a = R
  rcases lt_trichotomy R 0 with h | rfl | h
  · rw [sign_of_neg h, ← abs_neg, abs_of_pos (neg_pos.mpr h),
      cpow_add _ _ (ofReal_ne_zero.mpr (neg_ne_zero.mpr h.ne)), cpow_one, mul_comm _ (↑(-R) : ℂ),
      ← div_div, ofReal_neg, ofReal_neg, ofReal_one, div_neg, div_self (ofReal_ne_zero.mpr h.ne)]
  · simp
  · rw [sign_of_pos h, ofReal_one, abs_of_pos h, cpow_add _ _ (ofReal_ne_zero.mpr h.ne'),
      cpow_one, mul_comm _ (R : ℂ), ← div_div, div_self (ofReal_ne_zero.mpr h.ne')]
