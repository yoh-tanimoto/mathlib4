/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Asymptotic bounds for Jacobi theta functions

The goal of this file is to establish some technical lemmas about the asymptotics of the sums

`∑' (n : ℕ), (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)`

and

`∑' (n : ℤ), |n + a| ^ k * exp (-π * (n + a) ^ 2 * t).`

Here `k : ℕ` and `a : ℝ` are fixed, and we are interested in asymptotics as
`t → 0` and as `t → ∞`. Note that the sum over `ℤ` for `k` even has some arithmetic significance,
but the other sums are only useful as upper bounds.
-/

open Set Filter Topology Asymptotics Real Classical

noncomputable section

/-- to be re-homed -/
lemma tendsto_div_one_sub_exp (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun x ↦ x / (1 - exp (a * x))) (𝓝[≠] 0) (𝓝 (-a⁻¹)) := by
  have : Tendsto (fun x ↦ log (x + 1) / x) (𝓝[≠] 0) (𝓝 1)
  · convert (hasDerivAt_log one_ne_zero).tendsto_slope_zero using 2 with x
    · rw [log_one, sub_zero, smul_eq_mul, div_eq_inv_mul, add_comm]
    · rw [inv_one]
  convert (this.mul_const (-a⁻¹)).comp (f := fun x ↦ (exp (a * x) - 1)) ?_ using 2 with x
  · simp only [Function.comp_apply, sub_add_cancel, log_exp]
    rw [mul_neg, ← neg_mul, ← div_neg, neg_sub, mul_comm _ a⁻¹, ← mul_div_assoc, ← mul_assoc,
      inv_mul_cancel ha, one_mul]
  · rw [one_mul]
  · rw [tendsto_nhdsWithin_iff]
    constructor
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      simpa using (by continuity : Continuous fun x ↦ (exp (a * x) - 1)).tendsto 0
    · rw [eventually_nhdsWithin_iff]
      filter_upwards with x hx
      contrapose! hx
      simpa only [not_mem_compl_iff, mem_singleton_iff, sub_eq_zero, exp_eq_one_iff, mul_eq_zero,
        eq_false_intro ha, false_or] using hx

namespace HurwitzKernelBounds

section nat

def f_nat (k : ℕ) (a t : ℝ) (n : ℕ) : ℝ := (n + a) ^ k * exp (-π * (n + a) ^ 2 * t)

def g_nat (k : ℕ) (a t : ℝ) (n : ℕ) : ℝ := (n + a) ^ k * exp (-π * (n + a ^ 2) * t)

lemma f_le_g_nat (k : ℕ) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (n : ℕ) :
    ‖f_nat k a t n‖ ≤ g_nat k a t n := by
  rw [f_nat, norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_exp, mul_le_mul_right ht,
    mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos), ← sub_nonneg]
  have u : (n : ℝ) ≤ (n : ℝ) ^ 2
  · simpa only [← Nat.cast_pow, Nat.cast_le] using Nat.le_self_pow two_ne_zero _
  convert add_nonneg (sub_nonneg.mpr u) (by positivity : 0 ≤ 2 * n * a) using 1
  ring

def F_nat (k : ℕ) (a t : ℝ) : ℝ := ∑' n, f_nat k a t n

lemma summable_f_nat (k : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) : Summable (f_nat k a t) := by
  have : Summable fun n : ℕ ↦ n ^ k * exp (-π * (n + a) ^ 2 * t)
  · refine (((summable_pow_mul_jacobiTheta₂_term_bound (|a| * t) ht k).mul_right
      (rexp (-π * a ^ 2 * t))).comp_injective Nat.cast_injective).of_norm_bounded _ (fun n ↦ ?_)
    simp_rw [mul_assoc, Function.comp_apply, ← Real.exp_add, norm_mul, norm_pow, Int.cast_abs,
      Int.cast_ofNat, norm_eq_abs, Nat.abs_cast, abs_exp]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg _) _)
    rw [exp_le_exp, ← sub_nonneg]
    ring_nf
    rw [← add_mul, ← mul_add (π * t * n)]
    refine mul_nonneg (mul_nonneg (by positivity) ?_) two_pos.le
    rw [← neg_le_iff_add_nonneg]
    apply neg_le_abs
  apply (this.mul_left (2 ^ k)).of_norm_bounded_eventually_nat
  simp_rw [← mul_assoc, f_nat, norm_mul, norm_eq_abs, abs_exp,
    mul_le_mul_iff_of_pos_right (exp_pos _), ← mul_pow, abs_pow, two_mul]
  filter_upwards [eventually_ge_atTop (Nat.ceil |a|)] with n hn
  apply pow_le_pow_left (abs_nonneg _) ((abs_add_le _ _).trans
    (add_le_add (le_of_eq (Nat.abs_cast _)) (Nat.ceil_le.mp hn)))

lemma continuousOn_F_nat (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (F_nat k a) (Ioi 0) := by
  refine ContinuousAt.continuousOn (fun t (ht : 0 < t) ↦ ?_)
  obtain ⟨S, hS⟩ := exists_between ht
  refine ContinuousOn.continuousAt ?_ (Ioi_mem_nhds hS.2)
  refine continuousOn_tsum (fun n ↦ ?_) (summable_f_nat k a hS.1) (fun n x hx ↦ ?_)
  · apply Continuous.continuousOn
    continuity
  · rw [f_nat, f_nat, norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) _)
    rw [exp_le_exp]
    apply mul_le_mul_of_nonpos_left
    exact le_of_lt hx
    rw [neg_mul, neg_nonpos]
    exact mul_nonneg pi_pos.le (sq_nonneg _)

section k_eq_zero

/-!
## Sum over `ℕ` with `k = 0`

Here we use direct comparison with a geometric series.
-/

lemma F_nat_zero_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    ‖F_nat 0 a t‖ ≤ rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 0 ha ht)
  have h0 : rexp (-π * t) < 1
  · simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos ht
  convert (hasSum_geometric_of_lt_one (exp_pos _).le h0).mul_left _ using 1
  ext1 n
  simp only [g_nat]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  ring_nf

lemma F_nat_zero_zero_sub_le {t : ℝ} (ht : 0 < t) :
    ‖F_nat 0 0 t - 1‖ ≤ rexp (-π * t) / (1 - rexp (-π * t)) := by
  convert F_nat_zero_le zero_le_one ht using 2
  · rw [F_nat, tsum_eq_zero_add (summable_f_nat 0 0 ht), f_nat, Nat.cast_zero, add_zero, pow_zero,
      one_mul, pow_two, mul_zero, mul_zero, zero_mul, exp_zero, add_comm, add_sub_cancel]
    simp_rw [F_nat, f_nat, Nat.cast_add, Nat.cast_one, add_zero]
  · rw [one_pow, mul_one]

lemma isBigO_atTop_F_nat_zero_sub {a : ℝ} (ha : 0 ≤ a) : ∃ p, 0 < p ∧
    (fun t ↦ F_nat 0 a t - (if a = 0 then 1 else 0)) =O[atTop] fun t ↦ exp (-p * t) := by
  have aux : IsBigO atTop (fun t : ℝ ↦ (1 - rexp (-π * t))⁻¹) (fun _ ↦ (1 : ℝ))
  · refine ((Tendsto.const_sub _ ?_).inv₀ (by norm_num)).isBigO_one ℝ (c := ((1 - 0)⁻¹ : ℝ))
    simpa only [neg_mul, tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
      using tendsto_id.const_mul_atTop pi_pos
  split_ifs with h
  · rw [h]
    have : (fun t ↦ F_nat 0 0 t - 1) =O[atTop] fun t ↦ rexp (-π * t) / (1 - rexp (-π * t))
    · apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_zero_sub_le ht
    refine ⟨_, pi_pos, this.trans ?_⟩
    simpa using (isBigO_refl (fun t ↦ rexp (-π * t)) _).mul aux
  · simp_rw [sub_zero]
    have : (fun t ↦ F_nat 0 a t) =O[atTop] fun t ↦ rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))
    · apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact F_nat_zero_le ha ht
    refine ⟨π * a ^ 2, mul_pos pi_pos (sq_pos_of_ne_zero _ h), this.trans ?_⟩
    simp_rw [neg_mul π (a ^ 2)]
    simpa only [mul_one] using (isBigO_refl (fun t ↦ rexp (-(π * a ^ 2) * t)) _).mul aux

end k_eq_zero

section k_eq_one
/-!
## Sum over `ℕ` with `k = 1`

Here we use comparison with the series `∑ n r ^ n`, where `r = exp (-π * t)`.
-/

lemma F_nat_one_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    ‖F_nat 1 a t‖ ≤ rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  refine tsum_of_norm_bounded ?_ (f_le_g_nat 1 ha ht)
  have h0 : rexp (-π * t) < 1
  · simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos ht
  simp_rw [g_nat, pow_one, add_mul]
  apply HasSum.add
  · have h0' : ‖rexp (-π * t)‖ < 1 := by rwa [norm_eq_abs, abs_exp]
    convert (hasSum_coe_mul_geometric_of_norm_lt_one h0').mul_left (exp (-π * a ^ 2 * t)) using 1
    · ext1 n
      rw [mul_comm (exp _), ← Real.exp_nat_mul, mul_assoc (n : ℝ), ← Real.exp_add]
      ring_nf
    · rw [mul_add, add_mul, mul_one, exp_add, mul_div_assoc]
  · convert (hasSum_geometric_of_lt_one (exp_pos _).le h0).mul_left _ using 1
    ext1 n
    rw [← Real.exp_nat_mul, mul_assoc _ (exp _), ← Real.exp_add]
    ring_nf

lemma isBigO_atTop_F_nat_one {a : ℝ} (ha : 0 ≤ a) : ∃ p, 0 < p ∧
    F_nat 1 a =O[atTop] fun t ↦ exp (-p * t) := by
  suffices : ∃ p, 0 < p ∧ (fun t ↦ rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))) =O[atTop] fun t ↦ exp (-p * t)
  · let ⟨p, hp, hp'⟩ := this
    refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact F_nat_one_le ha ht
  have aux : IsBigO atTop (fun t : ℝ ↦ (1 - rexp (-π * t))⁻¹) (fun _ ↦ (1 : ℝ))
  · refine ((Tendsto.const_sub _ ?_).inv₀ (by norm_num)).isBigO_one ℝ (c := ((1 - 0)⁻¹ : ℝ))
    simpa only [neg_mul, tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
      using tendsto_id.const_mul_atTop pi_pos
  have aux' : IsBigO atTop (fun t : ℝ ↦ ((1 - rexp (-π * t)) ^ 2)⁻¹) (fun _ ↦ (1 : ℝ))
  · simpa only [inv_pow, one_pow] using aux.pow 2
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact ⟨_, pi_pos, by simpa only [zero_pow two_ne_zero, zero_add, mul_one, zero_mul, zero_div,
      add_zero] using (isBigO_refl _ _).mul aux'⟩
  · refine ⟨π * a ^ 2, mul_pos pi_pos <| pow_pos ha' _, IsBigO.add ?_ ?_⟩
    · conv_rhs => enter [t]; rw [← mul_one (rexp _)]
      refine (Eventually.isBigO ?_).mul aux'
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_of_nonneg (exp_pos _).le, exp_le_exp]
      nlinarith [pi_pos]
    · simp_rw [mul_div_assoc, ← neg_mul]
      apply IsBigO.const_mul_left
      simpa only [mul_one] using (isBigO_refl _ _).mul aux

/-- Estimate for `F_nat 1 a` as `t → 0`. This is annoying, first because the proof is messy, and
secondly because the result is not sharp: the true asymptotic is `1 / t`, not `1 / t ^ 2`. -/
lemma isBigO_nhds_zero_F_nat_one {a : ℝ} (ha : 0 ≤ a) :
    F_nat 1 a =O[𝓝[>] 0] fun t ↦ 1 / t ^ 2 := by
  suffices h : (fun t ↦ rexp (-π * (a ^ 2 + 1) * t) / (1 - rexp (-π * t)) ^ 2
      + a * rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t))) =O[𝓝[≠] 0] fun t ↦ 1 / t ^ 2
  · refine (eventually_nhdsWithin_iff.mpr ?_).isBigO.trans (h.mono (nhdsWithin_mono 0 (by simp)))
    exact eventually_of_forall (fun _ ht ↦ F_nat_one_le ha ht)
  refine ((IsBigO.mul ?_ ?_).add (IsBigO.mul ?_ ?_))
  · exact (((Continuous.tendsto (by continuity) _).mono_left nhdsWithin_le_nhds)).isBigO_one _
  · refine ((isBigO_of_div_tendsto_nhds ?_ (π⁻¹) ?_).pow _).inv_rev ?_
    · filter_upwards with x hx
      rwa [sub_eq_zero, eq_comm, exp_eq_one_iff, mul_eq_zero,
        eq_false_intro (neg_ne_zero.mpr pi_pos.ne'), false_or] at hx
    · simpa only [neg_inv, neg_neg] using tendsto_div_one_sub_exp (-π) (neg_ne_zero.mpr pi_pos.ne')
    · filter_upwards with x hx
      rw [(pow_eq_zero_iff two_ne_zero).mp hx, mul_zero, exp_zero, sub_self, zero_pow two_ne_zero]
  · exact (((Continuous.tendsto (by continuity) _).mono_left nhdsWithin_le_nhds)).isBigO_one _
  · refine ((?_ : IsBigO _ _ (fun x ↦ x)).trans
        ((isBigO_of_div_tendsto_nhds ?_ π⁻¹ ?_))).inv_rev ?_
    · refine isBigO_norm_right.mp (eventually_nhdsWithin_iff.mpr ?_).isBigO
      filter_upwards [eventually_ge_nhds neg_one_lt_zero, eventually_le_nhds zero_lt_one]
        with x hx hx' _
      rw [norm_pow, pow_two, norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr ⟨hx, hx'⟩)
    · filter_upwards with x hx
      rwa [sub_eq_zero, eq_comm, exp_eq_one_iff, mul_eq_zero,
        eq_false_intro (neg_ne_zero.mpr pi_pos.ne'), false_or] at hx
    · simpa only [neg_inv, neg_neg] using tendsto_div_one_sub_exp (-π) (neg_ne_zero.mpr pi_pos.ne')
    · filter_upwards with x hx
      rw [(pow_eq_zero_iff two_ne_zero).mp hx, mul_zero, exp_zero, sub_self]

end k_eq_one

end nat

section int

def f_int (k : ℕ) (a t : ℝ) (n : ℤ) : ℝ := |n + a| ^ k * exp (-π * (n + a) ^ 2 * t)

lemma f_int_ofNat (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (n : ℕ) :
    f_int k a t (Int.ofNat n) = f_nat k a t n := by
  rw [f_int, f_nat, Int.ofNat_eq_coe, Int.cast_ofNat, abs_of_nonneg (by positivity)]

lemma f_int_negSucc (k : ℕ) {a : ℝ} (ha : a ≤ 1) (t : ℝ) (n : ℕ) :
    f_int k a t (Int.negSucc n) = f_nat k (1 - a) t n := by
  have : (Int.negSucc n) + a = -(n + (1 - a)) := by { push_cast; ring }
  rw [f_int, f_nat, this, abs_neg, neg_sq, abs_of_nonneg (by linarith)]

lemma summable_f_int (k : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) : Summable (f_int k a t) := by
  apply Summable.of_norm
  have := (HasSum.int_rec (summable_f_nat k a ht).hasSum
    (summable_f_nat k (1 - a) ht).hasSum).summable.norm
  convert this using 2 with n
  rcases n with m | m
  · simp only [f_int, f_nat, Int.ofNat_eq_coe, Int.cast_ofNat, norm_mul, norm_eq_abs, abs_pow,
      abs_abs]
  · simp only [f_int, f_nat, Int.cast_negSucc, norm_mul, norm_eq_abs, abs_pow, abs_abs,
      (by { push_cast; ring } : -↑(m + 1) + a = -(m + (1 - a))), abs_neg, neg_sq]

def F_int (k : ℕ) (a t : ℝ) : ℝ := ∑' (n : ℤ), f_int k a t n

lemma F_int_eq (k : ℕ) {a : ℝ} (ha : a ∈ Icc 0 1) {t : ℝ} (ht : 0 < t) :
    F_int k a t = (F_nat k a t) + (F_nat k (1 - a) t) := by
  simp only [F_int, F_nat]
  convert ((summable_f_nat k a ht).hasSum.int_rec (summable_f_nat k (1 - a) ht).hasSum).tsum_eq
    using 3 with n
  rcases n with m | m
  · rw [f_int_ofNat _ ha.1]
  · rw [f_int_negSucc _ ha.2]

lemma continuousOn_F_int (k : ℕ) {a : ℝ} (ha : a ∈ Icc 0 1) :
    ContinuousOn (F_int k a) (Ioi 0) := by
  refine (ContinuousOn.add ?_ ?_).congr (fun t ht ↦ F_int_eq k ha ht) <;>
  exact continuousOn_F_nat k (by linarith [ha.1, ha.2])

lemma isBigO_atTop_F_int_zero_sub {a : ℝ} (ha : a ∈ Ico 0 1) : ∃ p, 0 < p ∧
    (fun t ↦ F_int 0 a t - (if a = 0 then 1 else 0)) =O[atTop] fun t ↦ exp (-p * t) := by
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_zero_sub ha.1
  obtain ⟨n, hn, hn'⟩ := isBigO_atTop_F_nat_zero_sub (sub_nonneg.mpr ha.2.le)
  have : 1 - a ≠ 0 := by linarith [ha.2]
  simp_rw [eq_false_intro this, if_false, sub_zero] at hn'
  refine ⟨min p n, lt_min hp hn, ?_⟩
  have : (fun t ↦ F_int 0 a t - (if a = 0 then 1 else 0)) =ᶠ[atTop]
      fun t ↦ (F_nat 0 a t - (if a = 0 then 1 else 0)) + F_nat 0 (1 - a) t
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [F_int_eq 0 (Ico_subset_Icc_self ha) ht]
    ring
  have aux1 {c d : ℝ} (hcd : c ≤ d) : (rexp <| -d * ·) =O[atTop] (rexp <| -c * ·)
  · apply Eventually.isBigO
    filter_upwards [eventually_gt_atTop 0] with t ht
    rwa [norm_of_nonneg (exp_pos _).le, exp_le_exp, mul_le_mul_right ht, neg_le_neg_iff]
  refine this.isBigO.trans ((hp'.trans ?_).add (hn'.trans ?_))
  · exact aux1 (min_le_left _ _)
  · exact aux1 (min_le_right _ _)

lemma isBigO_atTop_F_int_one {a : ℝ} (ha : a ∈ Icc 0 1) : ∃ p, 0 < p ∧
    F_int 1 a =O[atTop] fun t ↦ exp (-p * t) := by
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_F_nat_one ha.1
  obtain ⟨n, hn, hn'⟩ := isBigO_atTop_F_nat_one (sub_nonneg.mpr ha.2)
  refine ⟨min p n, lt_min hp hn, ?_⟩
  have : F_int 1 a =ᶠ[atTop] fun t ↦ F_nat 1 a t + F_nat 1 (1 - a) t
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact F_int_eq 1 ha ht
  have aux1 {c d : ℝ} (hcd : c ≤ d) : (rexp <| -d * ·) =O[atTop] (rexp <| -c * ·)
  · apply Eventually.isBigO
    filter_upwards [eventually_gt_atTop 0] with t ht
    rwa [norm_of_nonneg (exp_pos _).le, exp_le_exp, mul_le_mul_right ht, neg_le_neg_iff]
  refine this.isBigO.trans ((hp'.trans ?_).add (hn'.trans ?_))
  · exact aux1 (min_le_left _ _)
  · exact aux1 (min_le_right _ _)

lemma isBigO_nhds_zero_F_int_one {a : ℝ} (ha : a ∈ Icc 0 1) :
    F_int 1 a =O[𝓝[>] 0] fun t ↦ 1 / t ^ 2 := by
  have hp := isBigO_nhds_zero_F_nat_one ha.1
  have hn := isBigO_nhds_zero_F_nat_one (sub_nonneg.mpr ha.2)
  refine (EventuallyEq.isBigO ?_).trans (hp.add hn)
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards with t ht
  exact F_int_eq 1 ha ht

end int

end HurwitzKernelBounds
