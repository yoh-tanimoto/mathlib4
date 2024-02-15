/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.ZetaFunctions.HurwitzZetaEven
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Complex.RemovableSingularity

#align_import number_theory.zeta_function from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points (which are not arbitrary, but
I haven't checked exactly what they are).

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`
* `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
* `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## Outline of proofs:

We define a function `zetaKernel` on the reals, given by `t ↦ Θ (t * I)` where `θ` is Jacobi's
theta function. This satisfies a functional equation relating its values at `t` and `1 / t`, and
has the form `1 + O(t ^ (-r))` for every `r` as `t → ∞`. Thus its Mellin transform has meromorphic
continuation and satisfies a functional equation, by general theory.

On the other hand, since `zetaKernel` can be expanded in powers of `exp (-π * t)` and the Mellin
transform integrated term-by-term for `1 < Re s`, we obtain the relation to the naive Dirichlet
series `∑' (n : ℕ), 1 / (n + 1) ^ s`.
-/


open MeasureTheory Set Filter Asymptotics TopologicalSpace Real Asymptotics Classical

open Complex hiding exp norm_eq_abs abs_of_nonneg abs_two continuous_exp

open scoped Topology Real Nat

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s
#align riemann_completed_zeta₀ completedRiemannZeta₀

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s
#align riemann_completed_zeta completedRiemannZeta

lemma completedHurwitzZetaEven_zero (s : ℂ) :
    completedHurwitzZetaEven 0 s = completedRiemannZeta s := by rfl

lemma completedHurwitzZetaEven₀_zero (s : ℂ) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := by rfl

lemma completedCosZeta_zero (s : ℂ) :
    completedCosZeta 0 s = completedRiemannZeta s := by
  rw [completedRiemannZeta, completedHurwitzZetaEven, completedCosZeta, hurwitzEvenFEPair_zero_symm]

lemma completedCosZeta₀_zero (s : ℂ) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀,
    completedHurwitzZetaEven₀, completedCosZeta₀, hurwitzEvenFEPair_zero_symm]

lemma completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s + 1 / (1 - s)` is entire. -/
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0
#align differentiable_completed_zeta₀ differentiable_completedZeta₀

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`. -/
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]
#align riemann_completed_zeta₀_one_sub completedRiemannZeta₀_one_sub

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]
#align riemann_completed_zeta_one_sub completedRiemannZeta_one_sub

/-- The residue of `Λ(s)` at `s = 1` is equal to `1`. -/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. We set this to be irreducible to hide messy implementation
details. -/
irreducible_def riemannZeta :=
  Function.update (fun s ↦ (π : ℂ) ^ (s / 2) * completedRiemannZeta s / Gamma (s / 2)) 0 (-1 / 2)
#align riemann_zeta riemannZeta

/- Note the next lemma is true by definition; what's hard is to show that with this definition, `ζ`
is continuous (and indeed analytic) at 0, see `differentiableAt_riemannZeta` below. -/
/-- We have `ζ(0) = -1 / 2`. -/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  rw [riemannZeta]
  exact Function.update_same _ _ _
#align riemann_zeta_zero riemannZeta_zero

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s := by
  /- First claim: the result holds at `t` for `t ≠ 0`. Note we will need to use this for the case
    `s = 0` also, as a hypothesis for the removable-singularity criterion. -/
  have c1 (t : ℂ) (ht : t ≠ 0) (ht' : t ≠ 1) : DifferentiableAt ℂ
        (fun u : ℂ ↦ (π : ℂ) ^ (u / 2) * completedRiemannZeta u / Gamma (u / 2)) t := by
    apply DifferentiableAt.mul
    · refine (DifferentiableAt.const_cpow ?_ ?_).mul (differentiableAt_completedZeta ht ht')
      · exact differentiableAt_id.div_const  _
      · exact Or.inl (ofReal_ne_zero.mpr pi_pos.ne')
    · exact differentiable_one_div_Gamma.differentiableAt.comp t (differentiableAt_id.div_const  _)
  -- Second claim: the limit at `s = 0` exists and is equal to `-1 / 2`.
  have c2 : Tendsto (fun s : ℂ ↦ (π : ℂ) ^ (s / 2) * completedRiemannZeta s / Gamma (s / 2))
      (𝓝[≠] 0) (𝓝 <| -1 / 2) := by
    have h1 : Tendsto (fun z : ℂ ↦ (π : ℂ) ^ (z / 2)) (𝓝 0) (𝓝 1) := by
      convert (ContinuousAt.comp (f := fun z ↦ z/2)
        (continuousAt_const_cpow (ofReal_ne_zero.mpr pi_pos.ne')) ?_).tendsto using 2
      · simp_rw [Function.comp_apply, zero_div, cpow_zero]
      · exact continuousAt_id.div continuousAt_const two_ne_zero
    suffices h2 : Tendsto (fun z ↦ completedRiemannZeta z / Gamma (z / 2)) (𝓝[≠] 0) (𝓝 <| -1 / 2)
    · convert (h1.mono_left nhdsWithin_le_nhds).mul h2 using 1
      · ext1 x; rw [mul_div]
      · simp only [one_mul]
    suffices h3 :
      Tendsto (fun z ↦ completedRiemannZeta z * (z / 2) / (z / 2 * Gamma (z / 2))) (𝓝[≠] 0)
        (𝓝 <| -1 / 2)
    · refine Tendsto.congr' (eventuallyEq_of_mem self_mem_nhdsWithin fun z hz ↦ ?_) h3
      rw [← div_div, mul_div_cancel _ (div_ne_zero hz two_ne_zero)]
    have h4 : Tendsto (fun z : ℂ ↦ z / 2 * Gamma (z / 2)) (𝓝[≠] 0) (𝓝 1) := by
      refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
      rw [tendsto_nhdsWithin_iff, (by simp : 𝓝 (0 : ℂ) = 𝓝 (0 / 2))]
      exact ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
        eventually_of_mem self_mem_nhdsWithin fun x hx ↦ div_ne_zero hx two_ne_zero⟩
    suffices Tendsto (fun z ↦ completedRiemannZeta z * z / 2) (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)) by
      have := this.div h4 one_ne_zero
      simp_rw [div_one, mul_div_assoc] at this
      exact this
    refine Tendsto.div_const ?_ _
    simp_rw [mul_comm (completedRiemannZeta _)]
    simpa using completedHurwitzZetaEven_residue_zero 0
  -- Now the main proof.
  rcases ne_or_eq s 0 with (hs | rfl)
  · -- The easy case: `s ≠ 0`
    have : {(0 : ℂ)}ᶜ ∈ 𝓝 s := isOpen_compl_singleton.mem_nhds hs
    refine (c1 s hs hs').congr_of_eventuallyEq (eventuallyEq_of_mem this fun x hx ↦ ?_)
    rw [riemannZeta]
    apply Function.update_noteq hx
  · -- The hard case: `s = 0`.
    rw [riemannZeta, ← (lim_eq_iff ⟨-1 / 2, c2⟩).mpr c2]
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
        (fun t ht ↦ (c1 t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [zero_div, div_zero, Complex.Gamma_zero, mul_zero, cpow_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto c2 <| one_ne_zero' ℂ).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x ↦ by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' ↦ (hx <| inv_eq_zero.mp hx').elim
#align differentiable_at_riemann_zeta differentiableAt_riemannZeta

/-- The trivial zeroes of the zeta function. -/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [riemannZeta, Function.update_noteq this,
    show -2 * ((n : ℂ) + 1) / 2 = -↑(n + 1) by push_cast; ring, Complex.Gamma_neg_nat_eq_zero,
    div_zero]
#align riemann_zeta_neg_two_mul_nat_add_one riemannZeta_neg_two_mul_nat_add_one

/-- Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we have
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`. -/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) =
      (2 : ℂ) ^ (1 - s) * (π : ℂ) ^ (-s) * Gamma s * sin (π * (1 - s) / 2) * riemannZeta s := by
  -- Deducing this from the previous formulations is quite involved. The proof uses two
  -- nontrivial facts (the doubling formula and reflection formula for Gamma) and a lot of careful
  -- rearrangement, requiring several non-vanishing statements as input to `field_simp`.
  have hs_ne : s ≠ 0 := by contrapose! hs; rw [hs]; exact ⟨0, by rw [Nat.cast_zero, neg_zero]⟩
  have h_sqrt : (sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sqrt_ne_zero'.mpr pi_pos)
  have h_pow : (2 : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne.def, cpow_eq_zero_iff, not_and_or]
    exact Or.inl two_ne_zero
  have h_Ga_ne1 : Gamma (s / 2) ≠ 0 := by
    rw [Ne.def, Complex.Gamma_eq_zero_iff]
    contrapose! hs
    obtain ⟨m, hm⟩ := hs
    rw [div_eq_iff (two_ne_zero' ℂ), ← Nat.cast_two, neg_mul, ← Nat.cast_mul] at hm
    exact ⟨m * 2, by rw [hm]⟩
  have h_Ga_eq : Gamma s = Gamma (s / 2) * Gamma ((s + 1) / 2) * (2 : ℂ) ^ (s - 1) / sqrt π := by
    rw [add_div, Complex.Gamma_mul_Gamma_add_half, mul_div_cancel' _ (two_ne_zero' ℂ),
      (by ring : 1 - s = -(s - 1)), cpow_neg, ← div_eq_mul_inv, eq_div_iff h_sqrt,
      div_mul_eq_mul_div₀, div_mul_cancel _ h_pow]
  have h_Ga_ne3 : Gamma ((s + 1) / 2) ≠ 0 := by
    have h_Ga_aux : Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    contrapose! h_Ga_aux
    rw [h_Ga_eq, h_Ga_aux, mul_zero, zero_mul, zero_div]
  rw [riemannZeta, Function.update_noteq (by rwa [sub_ne_zero, ne_comm] : 1 - s ≠ 0),
    Function.update_noteq hs_ne, completedRiemannZeta_one_sub, mul_div, eq_div_iff h_Ga_ne1,
    mul_comm, ← mul_div_assoc]
  -- Now rule out case of s = positive odd integer & deduce further non-vanishing statements
  by_cases hs_pos_odd : ∃ n : ℕ, s = 1 + 2 * n
  · -- Note the case n = 0 (i.e. s = 1) works OK here, but only because we have used
    -- `Function.update_noteq` to change the goal; the original goal is genuinely false for s = 1.
    obtain ⟨n, rfl⟩ := hs_pos_odd
    have : (1 - (1 + 2 * (n : ℂ))) / 2 = -↑n := by
      rw [← sub_sub, sub_self, zero_sub, neg_div, mul_div_cancel_left _ (two_ne_zero' ℂ)]
    rw [this, Complex.Gamma_neg_nat_eq_zero, div_zero]
    have : (π : ℂ) * (1 - (1 + 2 * ↑n)) / 2 = ↑(-n : ℤ) * π := by push_cast; field_simp; ring
    rw [this, Complex.sin_int_mul_pi, mul_zero, zero_mul]
  have h_Ga_ne4 : Gamma ((1 - s) / 2) ≠ 0 := by
    rw [Ne.def, Complex.Gamma_eq_zero_iff]
    contrapose! hs_pos_odd
    obtain ⟨m, hm⟩ := hs_pos_odd
    rw [div_eq_iff (two_ne_zero' ℂ), sub_eq_iff_eq_add, neg_mul, ← sub_eq_neg_add,
      eq_sub_iff_add_eq] at hm
    exact ⟨m, by rw [← hm, mul_comm]⟩
  -- At last the main proof
  rw [show sin (↑π * (1 - s) / 2) = π * (Gamma ((1 - s) / 2) * Gamma (s / 2 + 1 / 2))⁻¹ by
      have := congr_arg Inv.inv (Complex.Gamma_mul_Gamma_one_sub ((1 - s) / 2)).symm
      rwa [(by ring : 1 - (1 - s) / 2 = s / 2 + 1 / 2), inv_div,
        div_eq_iff (ofReal_ne_zero.mpr pi_pos.ne'), mul_comm _ (π : ℂ), mul_div_assoc'] at this]
  rw [(by rw [← neg_sub] : (2 : ℂ) ^ (1 - s) = (2 : ℂ) ^ (-(s - 1))), cpow_neg, h_Ga_eq]
  suffices (π : ℂ) ^ ((1 - s) / 2) = (π : ℂ) ^ (-s) * sqrt π * (π : ℂ) ^ (s / 2) by
    rw [this]; field_simp;
    ring_nf; rw [← ofReal_pow, sq_sqrt pi_pos.le]; ring
  simp_rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ← cpow_add _ _ (ofReal_ne_zero.mpr pi_pos.ne')]
  congr 1
  push_cast
  field_simp
  ring
#align riemann_zeta_one_sub riemannZeta_one_sub

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
#align riemann_hypothesis RiemannHypothesis

/-!
## Relating the Mellin transform to the Dirichlet series
-/

theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta s = (π : ℂ) ^ (-s / 2) * Gamma (s / 2) *
    ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, completedCosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one, mul_div_assoc, tsum_mul_left, mul_comm (Gamma (s / 2))]
    using (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
#align completed_zeta_eq_tsum_of_one_lt_re completedZeta_eq_tsum_of_one_lt_re

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]; exact zero_le_one
  rw [riemannZeta, Function.update_noteq this, completedZeta_eq_tsum_of_one_lt_re hs, ← mul_assoc,
    neg_div, cpow_neg, mul_inv_cancel_left₀, mul_div_cancel_left]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_eq_mul_inv, mul_comm, show (2⁻¹ : ℂ) = (2⁻¹ : ℝ) by norm_num, re_ofReal_mul]
    exact mul_pos (inv_pos_of_pos two_pos) (zero_lt_one.trans hs)
  · rw [Ne.def, cpow_eq_zero_iff, not_and_or, ← Ne.def, ofReal_ne_zero]
    exact Or.inl pi_pos.ne'
#align zeta_eq_tsum_one_div_nat_cpow zeta_eq_tsum_one_div_nat_cpow

/-- Alternate formulation of `zeta_eq_tsum_one_div_nat_add_one_cpow` with a `+ 1` (to avoid relying
on mathlib's conventions for `0 ^ s`).  -/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  have hs' : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]; exact zero_le_one
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [tsum_eq_zero_add] at this
  · simpa [Nat.cast_zero, zero_cpow hs', div_zero, zero_add, Nat.cast_add, Nat.cast_one]
  · refine .of_norm ?_
    simp_rw [norm_div, norm_one, Complex.norm_eq_abs, ← ofReal_nat_cast,
      abs_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _) (zero_lt_one.trans hs).ne',
      summable_one_div_nat_rpow]
    assumption
#align zeta_eq_tsum_one_div_nat_add_one_cpow zeta_eq_tsum_one_div_nat_add_one_cpow

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_nat_cast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_nat_cast]
#align zeta_nat_eq_tsum_of_gt_one zeta_nat_eq_tsum_of_gt_one

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`: we have
`ζ (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)!`.
Compare `hasSum_zeta_nat` for a version formulated explicitly as a sum, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent to the above via
the functional equation). -/
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  convert congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one]
    · rw [ofReal_tsum]
      norm_num
    · refine one_lt_two.trans_le ?_
      conv_lhs => rw [← mul_one 2]
      rwa [mul_le_mul_left (zero_lt_two' ℕ), Nat.one_le_iff_ne_zero]
  · norm_num
#align riemann_zeta_two_mul_nat riemannZeta_two_mul_nat

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two, ofReal_tsum]
    norm_num
  · norm_num
#align riemann_zeta_two riemannZeta_two

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : ℂ) = (4 : ℕ) by norm_num,
      zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < 4), ofReal_tsum]
    norm_num
  · norm_num
#align riemann_zeta_four riemannZeta_four

theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · cases' m with m m
    ·-- k = 0 : evaluate explicitly
      rw [Nat.zero_eq, mul_zero, Nat.cast_zero, pow_zero, one_mul, zero_add, neg_zero, zero_add,
        div_one, bernoulli_one, riemannZeta_zero]
      norm_num
    · -- k = 2 * (m + 1) : both sides "trivially" zero
      rw [Nat.cast_mul, ← neg_mul, Nat.cast_two, Nat.cast_succ, riemannZeta_neg_two_mul_nat_add_one,
        bernoulli_eq_bernoulli'_of_ne_one]
      swap; · apply ne_of_gt; norm_num
      rw [bernoulli'_odd_eq_zero ⟨m + 1, rfl⟩ (by norm_num), Rat.cast_zero, mul_zero,
        zero_div]
  · -- k = 2 * m + 1 : the interesting case
    rw [Odd.neg_one_pow ⟨m, rfl⟩]
    rw [show -(↑(2 * m + 1) : ℂ) = 1 - (2 * m + 2) by push_cast; ring]
    rw [riemannZeta_one_sub]
    rotate_left
    · intro n
      rw [(by norm_cast : 2 * (m : ℂ) + 2 = ↑(2 * m + 2)), ← Int.cast_neg_natCast, ← Int.cast_ofNat,
        Ne.def, Int.cast_inj]
      apply ne_of_gt
      exact lt_of_le_of_lt (by norm_num : (-n : ℤ) ≤ 0) (by positivity)
    · rw [(by norm_cast : 2 * (m : ℂ) + 2 = ↑(2 * m + 2)), Ne.def, Nat.cast_eq_one]; norm_num
    -- get rid of sine term
    rw [show Complex.sin (↑π * (1 - (2 * ↑m + 2)) / 2) = -(-1 : ℂ) ^ m by
        rw [(by field_simp; ring : (π : ℂ) * (1 - (2 * ↑m + 2)) / 2 = π / 2 - (π * m + π))]
        rw [Complex.sin_pi_div_two_sub, Complex.cos_add_pi, neg_inj]
        rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
        · rw [pow_mul, neg_one_sq, one_pow]
          convert Complex.cos_nat_mul_two_pi t using 2
          push_cast; ring_nf
        · rw [pow_add, pow_one, pow_mul, neg_one_sq, one_pow, one_mul]
          convert Complex.cos_nat_mul_two_pi_add_pi t using 2
          push_cast; ring_nf]
    -- substitute in what we know about zeta values at positive integers
    have step1 := congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat (by norm_num : m + 1 ≠ 0)).tsum_eq
    have step2 := zeta_nat_eq_tsum_of_gt_one (by rw [mul_add]; norm_num : 1 < 2 * (m + 1))
    simp_rw [ofReal_tsum, ofReal_div, ofReal_one, ofReal_pow, ofReal_nat_cast] at step1
    rw [step1, (by norm_cast : (↑(2 * (m + 1)) : ℂ) = 2 * ↑m + 2)] at step2
    rw [step2, mul_div]
    -- now the rest is just a lengthy but elementary rearrangement
    rw [show ((2 * (m + 1))! : ℂ) = Complex.Gamma (2 * m + 2) * (↑(2 * m + 1) + 1) by
        rw [(by push_cast; ring : (2 * m + 2 : ℂ) = ↑(2 * m + 1) + 1),
          Complex.Gamma_nat_eq_factorial, (by ring : 2 * (m + 1) = 2 * m + 1 + 1),
          Nat.factorial_succ, Nat.cast_mul, mul_comm]
        norm_num]
    rw [← div_div, neg_one_mul]
    congr 1
    rw [div_eq_iff (Gamma_ne_zero_of_re_pos _)]
    swap; · rw [(by norm_num : 2 * (m : ℂ) + 2 = ↑(2 * (m : ℝ) + 2)), ofReal_re]; positivity
    simp_rw [ofReal_mul, ← mul_assoc, ofReal_rat_cast, mul_add, Nat.add_assoc, mul_one,
      one_add_one_eq_two, mul_neg, neg_mul, neg_inj]
    conv_rhs => rw [mul_comm]
    congr 1
    rw [ofReal_pow, ofReal_neg, ofReal_one, pow_add, neg_one_sq, mul_one]
    conv_lhs =>
      congr
      congr
      rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [show (2 : ℂ) ^ (1 - (2 * (m : ℂ) + 2)) = (↑((2 : ℝ) ^ (2 * m + 2 - 1)))⁻¹ by
        rw [ofReal_pow, ← cpow_nat_cast, ← cpow_neg, show (2 : ℝ) = (2 : ℂ) by norm_num]
        congr 1
        rw [Nat.add_sub_assoc one_le_two, Nat.cast_add, Nat.cast_mul, Nat.cast_two,
          (by norm_num : 2 - 1 = 1)]
        push_cast; ring]
    rw [show (π : ℂ) ^ (-(2 * (m : ℂ) + 2)) = (↑(π ^ (2 * m + 2)))⁻¹ by
        rw [ofReal_pow, ← cpow_nat_cast, ← cpow_neg, Nat.cast_add, Nat.cast_mul, Nat.cast_two]]
    rw [(by intros; ring : ∀ a b c d e : ℂ, a * b * c * d * e = a * d * (b * e) * c)]
    rw [inv_mul_cancel (ofReal_ne_zero.mpr <| pow_ne_zero _ pi_pos.ne'),
      inv_mul_cancel (ofReal_ne_zero.mpr <| pow_ne_zero _ two_ne_zero), one_mul, one_mul]
#align riemann_zeta_neg_nat_eq_bernoulli riemannZeta_neg_nat_eq_bernoulli

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  suffices : Tendsto (fun s ↦ (s - 1) *
      (π ^ (s / 2) * completedRiemannZeta s / Gamma (s / 2))) (𝓝[≠] 1) (𝓝 1)
  · refine this.congr' <| (eventually_ne_nhdsWithin one_ne_zero).mp (eventually_of_forall ?_)
    intro x hx
    simp [riemannZeta, Function.update_noteq hx]
  have h0 : Tendsto (fun s ↦ π ^ (s / 2) : ℂ → ℂ) (𝓝[≠] 1) (𝓝 (π ^ (1 / 2 : ℂ)))
  · refine ((continuousAt_id.div_const _).const_cpow ?_).tendsto.mono_left nhdsWithin_le_nhds
    exact Or.inl <| ofReal_ne_zero.mpr pi_ne_zero
  have h1 : Tendsto (fun s : ℂ ↦ 1 / Gamma (s / 2)) (𝓝[≠] 1) (𝓝 (1 / π ^ (1 / 2 : ℂ)))
  · rw [← Complex.Gamma_one_half_eq]
    refine (Continuous.tendsto ?_ _).mono_left nhdsWithin_le_nhds
    simpa using differentiable_one_div_Gamma.continuous.comp (continuous_id.div_const _)
  convert (completedRiemannZeta_residue_one.mul h0).mul h1 using 2 with s
  · ring
  · have := fun h ↦ ofReal_ne_zero.mpr pi_ne_zero ((cpow_eq_zero_iff _ (1 / 2)).mp h).1
    field_simp
