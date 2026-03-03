/-!
# Appendix A: Random Walk Expansions
## Dybalski–Stottmeister–Tanimoto (2024)

Formalization of Appendix A of:
  W. Dybalski, A. Stottmeister, Y. Tanimoto,
  "The Bałaban variational problem in the non-linear sigma model",
  Rev. Math. Phys. **36** (2024) 2461003.

### Sorry inventory (after this pass)

| # | Location                          | Status   | Explanation                                           |
|---|-----------------------------------|----------|-------------------------------------------------------|
| 1 | `one_add_rpow_mul_exp_bddAbove`   | PROVED   | Compactness + limit via composition + filter API      |
| 2 | `lemmaA2` (norm bound)            | sorry    | Lattice norm inequality ‖⌊M̃x/3⌋‖ ≥ ‖x‖ for M̃ ≥ 3  |
| 3 | `lemmaA2` (finiteness)            | sorry    | Finiteness of ℤᵈ balls; need `Metric.Finite`         |
| 4 | `lemmaA3 (iv)` (convolution)      | sorry    | n-fold convolution via telescoping + Young's ineq.    |
| 5 | `schurTest`                       | sorry    | Cauchy–Schwarz for ℓ²; standard but requires tsum API|
| 6 | `theoremA6`                       | sorry    | Full random walk expansion (research-level)           |
| 7 | `corollaryExpDecay` (conversion)  | sorry    | Algebraic bound: polynomial weight ≤ exp             |

Resolved sorrys vs. original:
  - `partOfUnity`: concrete definition given (was sorry) ✓
  - `lemmaA3 (ii)`: proved using `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` + helper ✓
  - `lemmaA3 (iii)`: fully proved via triangle ineq + exp monotonicity ✓
  - `lemmaA3 (v)`: proved by `antitoneOn_of_deriv_nonpos` + explicit derivative ✓
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Real BigOperators Filter

/-! ## Setup -/

abbrev Zd (d : ℕ) := Fin d → ℤ

namespace DST2024AppendixA

variable {d : ℕ} [NeZero d]

/-! ### Norms on the lattice -/

noncomputable def embed (x : Zd d) : EuclideanSpace ℝ (Fin d) := fun i => (x i : ℝ)

noncomputable def latNorm (x : Zd d) : ℝ := ‖embed x‖

lemma latNorm_nonneg (x : Zd d) : 0 ≤ latNorm x := norm_nonneg _

@[simp] lemma latNorm_zero : latNorm (0 : Zd d) = 0 := by simp [latNorm, embed]

lemma embed_add (x y : Zd d) : embed (x + y) = embed x + embed y := by
  ext i; simp [embed]

lemma latNorm_add (x y : Zd d) : latNorm (x + y) ≤ latNorm x + latNorm y := by
  simp only [latNorm]
  rw [show ‖embed (x + y)‖ = ‖embed x + embed y‖ by rw [embed_add]]
  exact norm_add_le _ _

@[simp] lemma latNorm_neg (x : Zd d) : latNorm (fun i => -(x i)) = latNorm x := by
  simp [latNorm, embed]; congr 1; ext i; simp

/-- Reverse triangle: `‖x‖ - ‖y‖ ≤ ‖x + y‖`. -/
lemma latNorm_sub_rev (x y : Zd d) : latNorm x - latNorm y ≤ latNorm (x + y) := by
  have h : latNorm ((x + y) + fun i => -(y i)) ≤
      latNorm (x + y) + latNorm (fun i => -(y i)) := latNorm_add _ _
  simp only [latNorm_neg] at h
  have : (fun i => (x + y) i + (-(y i))) = x := by ext; simp
  rw [this] at h; linarith

/-! ## Definition A.1 -/

noncomputable def weightFun (a : Zd d → ℝ) (δ : ℝ) (x : Zd d) : ℝ :=
  (1 + latNorm x) ^ ((d : ℝ) + δ) * a x

noncomputable def dConv (f g : Zd d → ℝ) (x : Zd d) : ℝ :=
  ∑' y : Zd d, f (fun i => x i - y i) * g y

noncomputable def nConv (f : Zd d → ℝ) : ℕ → Zd d → ℝ
  | 0       => fun x => if x = (fun _ => (0 : ℤ)) then 1 else 0
  | (n + 1) => dConv (nConv f n) f

structure IsShortRangeLocalizing (a : Zd d → ℝ) : Prop where
  pos         : ∀ x : Zd d, 0 < a x
  poly_decay  : ∃ (δ cδ : ℝ), 0 < δ ∧ 0 ≤ cδ ∧
    ∀ x : Zd d, a x ≤ cδ * (1 + latNorm x) ^ (-(2 * ((d : ℝ) + δ)))
  quasi_transl: ∀ (δ : ℝ), 0 < δ →
    ∃ K : ℝ, 0 < K ∧ ∀ x y : Zd d,
      latNorm y ≤ 2 * Real.sqrt d →
      weightFun a δ (fun i => x i + y i) ≤ K * weightFun a δ x
  conv_bound  : ∀ (δ : ℝ), 0 < δ → ∃ (c ε : ℝ), 0 < c ∧ 0 < ε ∧
    ∀ n : ℕ, ∀ x : Zd d,
      nConv (weightFun a δ) n x ≤ c ^ n * weightFun a δ (fun i => ⌊ε * (x i : ℝ)⌋)
  eventually_decr: ∀ (δ : ℝ), 0 < δ → ∃ M₀ : ℕ,
    ∀ x y : Zd d, M₀ ≤ ⌊latNorm x⌋₊ → latNorm x ≤ latNorm y →
      weightFun a δ y ≤ weightFun a δ x

/-! ## Analytic helper: (1 + t)^n * exp(-b*t) is bounded -/

/-- The function `t ↦ (1 + t)^n * exp(-b*t)` is bounded on `[0, ∞)`.
    Key tool: `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` from Mathlib. -/
lemma one_add_rpow_mul_exp_bddAbove (n b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ n * Real.exp (-b * t) ≤ C := by
  -- Step 1: t^n * exp(-b*t) → 0, hence eventually ≤ 1.
  have htend : Tendsto (fun t : ℝ => t ^ n * Real.exp (-b * t)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n b hb
  -- Step 2: (1 + t)^n * exp(-b*t) is continuous on [0, ∞) (need 1 + t > 0 for rpow).
  have hcont : ContinuousOn (fun t : ℝ => (1 + t) ^ n * Real.exp (-b * t))
      (Set.Ici 0) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const
      · exact continuousOn_const.add continuousOn_id
      · intro x hx; left; linarith [Set.mem_Ici.mp hx]
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  -- Step 3: (1 + t)^n * exp(-b*t) → 0 at infinity.
  -- Rewrite: exp(-bt) = exp(b) * exp(-b(1+t)), so f(t) = exp(b) * g(1+t)
  -- where g(s) = s^n * exp(-bs) → 0 by htend. Composition with (1+·) → ∞.
  have hlim : Tendsto (fun t : ℝ => (1 + t) ^ n * Real.exp (-b * t)) atTop (nhds 0) := by
    have hg : Tendsto (fun t : ℝ => (1 + t) ^ n * Real.exp (-b * (1 + t)))
        atTop (nhds 0) :=
      htend.comp (Filter.tendsto_atTop_add_const_left atTop (1 : ℝ) Filter.tendsto_id)
    have hfg : (fun t : ℝ => (1 + t) ^ n * Real.exp (-b * t)) =
        fun t => Real.exp b * ((1 + t) ^ n * Real.exp (-b * (1 + t))) := by
      ext t
      rw [show Real.exp (-b * t) = Real.exp b * Real.exp (-b * (1 + t)) from by
        rw [← Real.exp_add]; congr 1; ring]
      rw [mul_left_comm]
    rw [hfg, show (0 : ℝ) = Real.exp b * 0 from (mul_zero _).symm]
    exact tendsto_const_nhds.mul hg
  -- Step 4: Extract T such that f(t) ≤ 1 for all t ≥ T.
  have hev : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → (1 + t) ^ n * Real.exp (-b * t) ≤ 1 := by
    have h := hlim.eventually (Iio_mem_nhds one_pos)
    rw [Filter.eventually_atTop] at h
    obtain ⟨T, hT⟩ := h
    exact ⟨T, fun t ht => le_of_lt (hT t ht)⟩
  obtain ⟨T, hT⟩ := hev
  -- Step 5: Bound on [0, max T 0] by compactness + continuity.
  set T' := max T 0
  have hne : (Set.Icc (0 : ℝ) T').Nonempty :=
    ⟨0, Set.left_mem_Icc.mpr (le_max_right T 0)⟩
  obtain ⟨t₀, _, ht₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn hne (hcont.mono Set.Icc_subset_Ici_self)
  -- Step 6: C = max(f(t₀), 1) works for both regions.
  refine ⟨max ((1 + t₀) ^ n * Real.exp (-b * t₀)) 1,
    le_max_of_le_right zero_le_one, fun t ht => ?_⟩
  by_cases htT : t ≤ T'
  · exact le_max_of_le_left (ht₀_max (Set.mem_Icc.mpr ⟨ht, htT⟩))
  · push_neg at htT
    exact le_max_of_le_right (hT t ((le_max_left T 0).trans htT.le))

/-! ## Lemma A.2 -/

theorem lemmaA2 (a : Zd d → ℝ) (ha : IsShortRangeLocalizing a) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M̃₀ : ℕ, ∀ (M̃ : ℕ) (_ : M̃₀ ≤ M̃) (x : Zd d),
      weightFun a δ (fun i => ⌊(M̃ : ℝ) / 3 * (x i : ℝ)⌋) ≤ weightFun a δ x := by
  obtain ⟨M₀, hM₀⟩ := ha.eventually_decr δ hδ
  use max 3 M₀
  intro M̃ hM̃ x
  apply hM₀
  · -- Need: M₀ ≤ ⌊latNorm x⌋₊.
    -- Case 1: latNorm x ≥ M₀ — immediate.
    -- Case 2: latNorm x < M₀ — use that ‖⌊M̃x/3⌋‖ ≥ latNorm x ≥ 0 (for small x, M̃
    --   is large enough to push ⌊M̃x/3⌋ beyond M₀ since the lattice ball is finite).
    -- Requires Metric.finite_isBounded / finiteness of ℤᵈ balls — sorry.
    sorry
  · -- Need: latNorm x ≤ latNorm (⌊M̃x/3⌋).
    -- For M̃ ≥ 3: |(M̃/3) * xᵢ| ≥ |xᵢ|, so ‖⌊M̃x/3⌋‖ ≳ (M̃/3) ‖x‖ ≥ ‖x‖.
    -- Precise bound: |⌊M̃xᵢ/3⌋ - M̃xᵢ/3| ≤ 1, so ‖⌊M̃x/3⌋‖ ≥ (M̃/3)‖x‖ - √d.
    -- For M̃ ≥ 3 and ‖x‖ ≥ M₀ the RHS is ≥ ‖x‖ since M₀ ≥ 3√d/(M̃-3) — sorry.
    sorry

/-! ## Lemma A.3 -/

theorem lemmaA3 (c₁ : ℝ) (hc : 0 < c₁) :
    IsShortRangeLocalizing (fun x : Zd d => Real.exp (-c₁ * latNorm x)) := by
  constructor
  · -- ── (i) Positivity ─────────────────────────────────────────────────────────
    intro x; exact Real.exp_pos _
  · -- ── (ii) Polynomial decay with δ = c₁ ─────────────────────────────────────
    obtain ⟨C, hC_nn, hC⟩ := one_add_rpow_mul_exp_bddAbove (2 * ((d : ℝ) + c₁)) c₁ hc
    refine ⟨c₁, C, hc, hC_nn, fun x => ?_⟩
    -- Need: exp(-c₁|x|) ≤ C * (1 + |x|)^{-2(d+c₁)}
    -- Equivalently: C ≥ (1 + |x|)^{2(d+c₁)} * exp(-c₁|x|).
    rw [Real.rpow_neg (by linarith [latNorm_nonneg x])]
    rw [mul_inv_le_iff₀ (by positivity)]
    calc Real.exp (-c₁ * latNorm x) * (1 + latNorm x) ^ (2 * ((d : ℝ) + c₁))
        = (1 + latNorm x) ^ (2 * ((d : ℝ) + c₁)) * Real.exp (-c₁ * latNorm x) :=
          mul_comm _ _
      _ ≤ C := hC (latNorm x) (latNorm_nonneg x)
  · -- ── (iii) Quasi-translation with K = (1 + 2√d)^{d+δ} * exp(2c₁√d) ────────
    intro δ hδ
    use (1 + 2 * Real.sqrt d) ^ ((d : ℝ) + δ) * Real.exp (c₁ * 2 * Real.sqrt d)
    refine ⟨by positivity, fun x y hy => ?_⟩
    simp only [weightFun]
    set tx  := latNorm x
    set txy := latNorm (fun i => x i + y i)
    -- (a) txy ≤ tx + 2√d
    have hxy_le : txy ≤ tx + 2 * Real.sqrt d :=
      (latNorm_add x y).trans (by linarith)
    -- (b) 1 + txy ≤ (1 + 2√d)(1 + tx)
    have h1plus : 1 + txy ≤ (1 + 2 * Real.sqrt d) * (1 + tx) :=
      by nlinarith [latNorm_nonneg x, Real.sqrt_nonneg d]
    -- (c) txy ≥ tx - 2√d  (reverse triangle ineq)
    have hlower : tx - 2 * Real.sqrt d ≤ txy := by
      -- latNorm_sub_rev x y : tx - latNorm y ≤ latNorm (x + y) = txy
      -- and hy : latNorm y ≤ 2√d
      have h := latNorm_sub_rev x y
      -- Note: latNorm (x + y) = txy since (x+y) i = x i + y i definitionally
      linarith
    -- (d) exp(-c₁ * txy) ≤ exp(2c₁√d) * exp(-c₁ * tx)
    have hexp : Real.exp (-c₁ * txy) ≤
        Real.exp (c₁ * 2 * Real.sqrt d) * Real.exp (-c₁ * tx) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [latNorm_nonneg y])
    -- (e) (1 + txy)^{d+δ} ≤ ((1+2√d)(1+tx))^{d+δ}
    have hrpow : (1 + txy) ^ ((d : ℝ) + δ) ≤
        ((1 + 2 * Real.sqrt d) * (1 + tx)) ^ ((d : ℝ) + δ) :=
      Real.rpow_le_rpow (by linarith [latNorm_nonneg (fun i => x i + y i)])
        h1plus (by linarith [latNorm_nonneg x])
    -- (f) Split the rpow of a product
    have hsplit : ((1 + 2 * Real.sqrt d) * (1 + tx)) ^ ((d : ℝ) + δ) =
        (1 + 2 * Real.sqrt d) ^ ((d : ℝ) + δ) * (1 + tx) ^ ((d : ℝ) + δ) :=
      Real.mul_rpow (by positivity) (by linarith [latNorm_nonneg x])
    -- Combine all pieces
    calc (1 + txy) ^ ((d : ℝ) + δ) * Real.exp (-c₁ * txy)
        ≤ ((1 + 2 * Real.sqrt d) * (1 + tx)) ^ ((d : ℝ) + δ) * Real.exp (-c₁ * txy) :=
          mul_le_mul_of_nonneg_right hrpow (by positivity)
      _ ≤ ((1 + 2 * Real.sqrt d) * (1 + tx)) ^ ((d : ℝ) + δ) *
            (Real.exp (c₁ * 2 * Real.sqrt d) * Real.exp (-c₁ * tx)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (1 + 2 * Real.sqrt d) ^ ((d : ℝ) + δ) * Real.exp (c₁ * 2 * Real.sqrt d) *
            ((1 + tx) ^ ((d : ℝ) + δ) * Real.exp (-c₁ * tx)) := by
          rw [hsplit]; ring
  · -- ── (iv) Convolution bound with ε = 1/4 ────────────────────────────────────
    -- Proof strategy (A.9)–(A.12): write b(z) = α(z) * β(z) where
    --   α(z) = exp(-c₁|z|/4),  β(z) = (1+|z|)^{d+δ} * exp(-3c₁|z|/4).
    -- Telescoping: Π_i α(xᵢ-xᵢ₊₁) ≤ exp(-c₁|x₀-xₙ|/4) = α(x₀-xₙ).
    -- Young (ℓ¹): (Σ_z β(z))^n bounds the n-path sum of Π β-factors.
    -- Combined: (b^{*n})(x) ≤ (Σ_z β(z))^n * b(x/4).
    intro δ hδ
    set β_sum := ∑' z : Zd d, (1 + latNorm z) ^ ((d : ℝ) + δ) * Real.exp (-(3 * c₁ / 4) * latNorm z)
    refine ⟨β_sum, 1 / 4, by positivity, by norm_num, fun n x => ?_⟩
    sorry
    -- The sorry is (A.9)–(A.12): induction on n; see nodes 2-L3-04 and 2-RW-04
    -- in the alethfeld proof graph.
  · -- ── (v) Eventual decrease ──────────────────────────────────────────────────
    -- f(t) = (1+t)^{d+δ} * exp(-c₁*t) has f'(t) ≤ 0 iff t ≥ (d+δ)/c₁ - 1.
    intro δ hδ
    use ⌈((d : ℝ) + δ) / c₁⌉₊
    intro x y hM hle
    simp only [weightFun]
    set tx := latNorm x
    set ty := latNorm y
    -- Show f is antitone on [tx, ∞) ⊇ {latNorm x, latNorm y}
    have htx_lb : (d : ℝ) + δ ≤ c₁ * (1 + tx) := by
      -- M₀ := ⌈(d+δ)/c₁⌉₊ ≤ ⌊tx⌋₊, so tx ≥ M₀ - 1 ≥ (d+δ)/c₁ - 1
      have hM_cast : (⌈((d : ℝ) + δ) / c₁⌉₊ : ℝ) ≤ ⌊tx⌋₊ := Nat.cast_le.mpr hM
      have hceil : ((d : ℝ) + δ) / c₁ ≤ (⌈((d : ℝ) + δ) / c₁⌉₊ : ℝ) := by
        push_cast; exact Nat.le_ceil _
      have hfloor : (⌊tx⌋₊ : ℝ) ≤ tx + 1 := by
        have := Nat.lt_floor_add_one tx; push_cast at this ⊢; linarith
      nlinarith
    -- Apply antitoneOn_of_deriv_nonpos on the set [tx, ∞)
    have hanti : AntitoneOn (fun t => (1 + t) ^ ((d : ℝ) + δ) * Real.exp (-c₁ * t))
        (Set.Ici tx) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici tx)
      · -- Continuity on [tx, ∞)
        apply ContinuousOn.mul
        · exact ((continuous_const.add continuous_id).rpow_const
            (fun t ht => Or.inl (by linarith [ht]))).continuousOn
        · exact ((continuous_const.mul continuous_id).exp).continuousOn
      · -- Show: deriv f t ≤ 0 for t > tx
        intro t ht
        simp only [interior_Ici, Set.mem_Ioi] at ht
        -- Compute derivative via HasDerivAt
        have hderiv : HasDerivAt
            (fun t => (1 + t) ^ ((d : ℝ) + δ) * Real.exp (-c₁ * t))
            (((d : ℝ) + δ) * (1 + t) ^ ((d : ℝ) + δ - 1) * Real.exp (-c₁ * t) +
             (1 + t) ^ ((d : ℝ) + δ) * (-c₁ * Real.exp (-c₁ * t))) t := by
          apply HasDerivAt.mul
          · -- d/dt (1+t)^{d+δ} = (d+δ)(1+t)^{d+δ-1}
            have h1 : HasDerivAt (fun t => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
            have h2 := h1.rpow_const ((d : ℝ) + δ) (Or.inl (by linarith [ht, latNorm_nonneg x]))
            simpa [mul_one] using h2
          · -- d/dt exp(-c₁*t) = -c₁ * exp(-c₁*t)
            have h3 : HasDerivAt (fun t => -c₁ * t) (-c₁) t :=
              (hasDerivAt_id t).const_mul (-c₁)
            have h4 := (Real.hasDerivAt_exp (-c₁ * t)).comp t h3
            simp only [Function.comp] at h4
            convert h4 using 1; ring
        rw [hderiv.deriv]
        -- The derivative equals (1+t)^{d+δ-1} * exp(-c₁t) * ((d+δ) - c₁(1+t)) ≤ 0
        have hfactor :
            ((d : ℝ) + δ) * (1 + t) ^ ((d : ℝ) + δ - 1) * Real.exp (-c₁ * t) +
            (1 + t) ^ ((d : ℝ) + δ) * (-c₁ * Real.exp (-c₁ * t)) =
            (1 + t) ^ ((d : ℝ) + δ - 1) * Real.exp (-c₁ * t) *
            ((d + δ) - c₁ * (1 + t)) := by
          have hsub : (1 + t) ^ ((d : ℝ) + δ) =
              (1 + t) ^ ((d : ℝ) + δ - 1) * (1 + t) := by
            rw [← Real.rpow_natCast (1 + t) 1, ← Real.rpow_add (by linarith [ht])]
            norm_num
          rw [hsub]; ring
        rw [hfactor]
        -- Factor is ≤ 0: first part ≥ 0, second part = (d+δ) - c₁(1+t) ≤ 0
        have htx' : (d : ℝ) + δ ≤ c₁ * (1 + t) := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (Real.rpow_nonneg (by linarith [ht]) _) (Real.exp_pos _).le)
          (by linarith)
    exact hanti (Set.mem_Ici.mpr (le_refl _)) (Set.mem_Ici.mpr hle) hle

/-! ## Lemma A.8: Schur Test -/

/-- **Lemma A.8**: If `T` has row sums ≤ Sᵣ and column sums ≤ Sᶜ,
    then `‖Tf‖ ≤ √(Sᵣ·Sᶜ) · ‖f‖` for each `x`. -/
theorem schurTest
    (T : Zd d → Zd d → ℝ)
    (Sᵣ Sᶜ : ℝ)
    (hrow : ∀ x : Zd d, ∑' x' : Zd d, |T x x'| ≤ Sᵣ)
    (hcol : ∀ x' : Zd d, ∑' x : Zd d, |T x x'| ≤ Sᶜ)
    (hSr : 0 ≤ Sᵣ) (hSc : 0 ≤ Sᶜ)
    (f : Zd d → ℝ) :
    ∀ x : Zd d, |∑' x' : Zd d, T x x' * f x'| ≤ Real.sqrt (Sᵣ * Sᶜ) * ‖f‖ := by
  intro x
  -- Cauchy–Schwarz for ∑ |Txx'| |f(x')|:
  -- |∑_{x'} T(x,x') f(x')| ≤ (∑_{x'} |T|)^{1/2} · (∑_{x'} |T| |f|²)^{1/2}
  --                         ≤ Sᵣ^{1/2} · (Sᶜ ∑_{x'} |f|²)^{1/2}
  --                         = √(Sᵣ·Sᶜ) · ‖f‖.
  -- Requires: tsum Cauchy–Schwarz + tsum Fubini — sorry.
  sorry

/-! ## Main structures -/

structure StrictlyPositiveKernelOp where
  ker : Zd d → Zd d → ℝ
  m   : ℝ
  hm  : 0 < m
  pos : ∀ f : Zd d → ℝ,
    m ^ 2 * ∑' x : Zd d, f x ^ 2 ≤
      ∑' x : Zd d, f x * (∑' x' : Zd d, ker x x' * f x')

/-- Piecewise-linear bump: 1 for |t| ≤ 1/3, 0 for |t| ≥ 2/3. -/
noncomputable def bump1d (t : ℝ) : ℝ := max 0 (min 1 (2 - 3 * |t|))

/-- Partition of unity: `h_j(x) = Πₖ bump1d((xₖ/M̃) - jₖ)`.
    This is a piecewise-linear version of the smooth h in the paper. -/
noncomputable def partOfUnity (M̃ : ℕ) (j x : Zd d) : ℝ :=
  ∏ k : Fin d, bump1d ((x k : ℝ) / (M̃ : ℝ) - (j k : ℝ))

lemma partOfUnity_nonneg (M̃ : ℕ) (j x : Zd d) : 0 ≤ partOfUnity M̃ j x :=
  Finset.prod_nonneg (fun k _ => le_max_left _ _)

/-! ## Theorem A.6 -/

/-- **Theorem A.6 (Balaban–Jaffe)**: Strictly positive SRL-bounded operator → A⁻¹ has SRL bound.

    Proof (paper Sec. A.2):
    1. Cⱼ = (□ⱼ A □ⱼ)⁻¹, C = Σⱼ hⱼ Cⱼ hⱼ (approximate inverse).
    2. R = 1 - AC; ‖Rᵢⱼ‖ ≤ C·M̃^{-δ/2}·b(M̃(i-j)/3)  [Lemma A.10].
    3. ‖R‖_op ≤ 2^d·m⁻²·C·M̃^{-δ/2}·‖b‖₁ < 1  [Lemma A.9 + A.10].
    4. A⁻¹ = Σₙ CRⁿ (Neumann series).
    5. |(CRⁿ)(x,x')| ≤ Σ_{ω} m^{-2n-2} Πₖ ‖Rω_{2k+1},ω_{2k+2}‖.
    6. Sum over O(5^{dn}) adjacent odd indices.
    7. Even-index convolution sum = (b₃^{*n})(x-x') ≤ (b^{*n})(x-x') ≤ cⁿ b(εx).
    8. Geometric series Σₙ qⁿ < ∞ for M̃ ≥ M̃₀. -/
theorem theoremA6
    (a : Zd d → ℝ)
    (ha : IsShortRangeLocalizing a)
    (A : StrictlyPositiveKernelOp (d := d))
    (hA_bound : ∀ x x' : Zd d, |A.ker x x'| ≤ a (fun i => x i - x' i)) :
    ∃ (c ε : ℝ) (M̃₀ : ℕ), 0 < c ∧ 0 < ε ∧
      ∀ (M̃ : ℕ) (_ : M̃₀ ≤ M̃)
        (A_inv : Zd d → Zd d → ℝ)
        (_ : ∀ x z : Zd d,
          ∑' y : Zd d, A.ker x y * A_inv y z = if x = z then 1 else 0),
        ∀ x x' : Zd d,
          |A_inv x x'| ≤
            c * weightFun a ha.poly_decay.choose
              (fun i => ⌊ε * ((x i - x' i : ℤ) : ℝ) / (M̃ : ℝ)⌋) := by
  obtain ⟨δ, _, hδ, _, _⟩ := ha.poly_decay
  obtain ⟨c_conv, ε_conv, hc_conv, hε_conv, _⟩ := ha.conv_bound δ hδ
  -- The full random walk expansion requires the machinery of nodes 2-RW-01 through 2-RW-04.
  sorry

/-! ## Lemma A.9 (nonneg statement only) -/

theorem lemmaA9
    (m : ℝ) (hm : 0 < m)
    (Sr Sc : ℝ) (hSr : 0 ≤ Sr) (hSc : 0 ≤ Sc) :
    (2 : ℝ) ^ d * m⁻² * Real.sqrt (Sr * Sc) ≥ 0 := by positivity

/-! ## Lemma A.10 (decay rate) -/

/-- M̃^{-δ/2} → 0 (proved). -/
theorem lemmaA10_bound (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun M : ℝ => M ^ (-(δ / 2))) atTop (nhds 0) :=
  Real.tendsto_rpow_atTop_nhds_zero_of_neg (by linarith)

/-! ## Corollary: exponential decay -/

theorem corollaryExpDecay
    (c₁ : ℝ) (hc : 0 < c₁)
    (A : StrictlyPositiveKernelOp (d := d))
    (hA : ∀ x x' : Zd d, |A.ker x x'| ≤ Real.exp (-c₁ * latNorm (fun i => x i - x' i))) :
    ∃ c' c₁' : ℝ, 0 < c' ∧ 0 < c₁' ∧
      ∀ (A_inv : Zd d → Zd d → ℝ)
        (_ : ∀ x z : Zd d,
          ∑' y : Zd d, A.ker x y * A_inv y z = if x = z then 1 else 0),
        ∀ x x' : Zd d,
          |A_inv x x'| ≤ c' * Real.exp (-c₁' * latNorm (fun i => x i - x' i)) := by
  -- Step 1: a(x) = exp(-c₁|x|) is SRL (Lemma A.3)
  have hSRL : IsShortRangeLocalizing (fun x : Zd d => Real.exp (-c₁ * latNorm x)) :=
    lemmaA3 c₁ hc
  -- Step 2: Apply Theorem A.6 to get the weightFun bound
  obtain ⟨c, ε, M̃₀, hc', hε, hbound⟩ := theoremA6 _ hSRL A hA
  -- Step 3: Choose M̃ = max(M̃₀, 1) and c₁' = c₁ * ε / (4 * M̃)
  set M̃ := max M̃₀ 1 with hM̃_def
  have hM̃₀ : M̃₀ ≤ M̃ := le_max_left _ _
  have hM̃_pos : (0 : ℝ) < M̃ := by
    have : (1 : ℕ) ≤ M̃ := le_max_right _ _
    exact_mod_cast Nat.one_le_iff_ne_zero.mp this
  set c₁' := c₁ * ε / (4 * M̃)
  -- Step 4: For lemmaA3, poly_decay.choose = c₁ (or more precisely, some δ ≥ c₁/2)
  -- The weight function satisfies:
  --   weightFun exp c₁ (εz/M̃) = (1 + ε|z|/M̃)^{d+c₁} * exp(-c₁ * ε|z|/M̃)
  -- By one_add_rpow_mul_exp_bddAbove applied with b = c₁ε/(2M̃):
  --   (1 + t)^{d+c₁} * exp(-c₁ε/M̃ * t) ≤ C_poly * exp(-c₁ε/(2M̃) * t)
  -- Combined with exp(-c₁ε/(2M̃) * t) ≤ exp(-c₁ε/(4M̃) * t):
  --   weightFun ≤ C_poly * exp(-c₁' |z|)
  -- This sorry wraps the algebraic combination of the above bounds.
  sorry

end DST2024AppendixA
