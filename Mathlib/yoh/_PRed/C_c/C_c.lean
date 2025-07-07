import Mathlib

open ZeroAtInfty Filter Urysohns

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

open BoundedContinuousFunction Topology Bornology

open Filter Metric

variable [TopologicalSpace α] [LocallyCompactSpace α]


-- lemma exist_HasCompactSupport_and_Tendsto' (f : C₀(X, ℂ)) : ∃ (g : ℕ → C₀(X ,ℂ)),
--     (∀ (n : ℕ), HasCompactSupport (g n)) ∧ Filter.Tendsto g Filter.atTop (nhds f) := by
--  have h : ∀ (n : ℕ), ∃ (gn : C₀(X, ℂ)), HasCompactSupport gn ∧ ‖f - gn‖ ≤ 1/((n : ℝ)+1) := by
--   intro n
--   have h1 : {x : X | dist (f x) 0 < 1/((n : ℝ)+1)} ∈ Filter.cocompact X := by
--    apply Filter.eventually_iff.mp
--    apply Metric.tendsto_nhds.mp (ZeroAtInftyContinuousMap.zero_at_infty' f)
--    exact Nat.one_div_pos_of_nat
--   rw [Filter.mem_cocompact] at h1
--   obtain ⟨K, hK⟩ := h1
--   rw [Set.compl_subset_comm] at hK
--   obtain ⟨U, hU⟩ := exists_isOpen_superset_and_isCompact_closure hK.left
--   obtain ⟨k, hk⟩ := exists_continuous_one_zero_of_isCompact hK.left (IsOpen.isClosed_compl hU.left) (LE.le.disjoint_compl_right hU.right.left)
--   have hkcp : HasCompactSupport (ContinuousMap.comp ⟨Complex.ofRealCLM, Complex.ofRealCLM.cont⟩ k) := by
--    have hk1 : Complex.ofRealCLM 0 = 0 := by rfl
--    have hk2 : Function.support (ContinuousMap.comp ⟨Complex.ofRealCLM, Complex.ofRealCLM.cont⟩ k) ⊆ Function.support k := by
--     apply Function.support_comp_subset hk1
--    unfold HasCompactSupport
--    exact IsCompact.closure_of_subset hk.right.right.left (subset_trans hk2 subset_closure)

--   let gn : C₀(X, ℂ)
--     := ⟨f.1 * (ContinuousMap.comp ⟨Complex.ofRealCLM, Complex.ofRealCLM.cont⟩ k),
--        (zero_at_infty_of_hasCompactSupport (f.1 * (ContinuousMap.comp
--        ⟨Complex.ofRealCLM, Complex.ofRealCLM.cont⟩ k)) hkcp.mul_left)⟩
--   use gn
--   constructor
--   exact hkcp.mul_left
--   have h2 : ∀ (x : X), ‖(f - gn) x‖ ≤ 1 / (↑n + 1) := by
--    intro x
--    have h21 : gn x = f x * k x := by rfl
--    have h22 : (f - gn) x = f x - gn x := by rfl
--    rw [h22, h21]
--    have h23 : 0 ≤ k x ∧ k x ≤ 1 := by
--     apply hk.right.right.right x
--    have h24 : 0 ≤ 1 - k x ∧ 1 - k x ≤ 1 := by
--     constructor
--     nth_rw 1 [← sub_self 1]
--     exact (sub_le_sub (le_refl 1) h23.right)
--     nth_rw 2 [← sub_zero 1]
--     exact (sub_le_sub (le_refl 1) h23.left)
--    have h241 : |1 - k x| ≤ |1| := by
--     exact abs_le_abs_of_nonneg h24.1 h24.2
--    rw [abs_one] at h241
--    have h26 : f x - f x * k x = f x * (1 - k x) := by ring
--    rw [h26]
--    by_cases hxK : x ∈ K
--    have h27 : k x = 1 := by exact (hk.1 hxK)
--    rw [h27]
--    simp
--    apply le_of_lt (Nat.cast_add_one_pos n)
--    rw [Set.compl_subset_comm] at hK
--    have h28 : dist (f x) 0 < 1/(n+1) := by
--     apply hK.2
--     exact Set.mem_compl hxK
--    rw [SeminormedAddCommGroup.dist_eq, sub_zero] at h28
--    rw [norm_mul, mul_comm]
--    apply mul_le_mul
--    rw [← Complex.abs_ofReal, ← Complex.norm_eq_abs] at h241
--    have h281 : (1 - (k x : ℂ)) = ((1 - k x) : ℝ) := by simp
--    rw [← h281] at h241
--    exact h241
--    rw [← one_div]
--    exact le_of_lt h28
--    simp
--    norm_num
--   apply (BoundedContinuousFunction.norm_le (le_of_lt Nat.one_div_pos_of_nat)).mpr h2
--  obtain ⟨g, hg⟩ := Classical.axiomOfChoice h
--  use g
--  constructor
--  intro n
--  exact (hg n).left
--  rw [Metric.tendsto_atTop]
--  intro ε hε
--  use Nat.ceil (1/ε)
--  intro n hn
--  rw [dist_comm, SeminormedAddCommGroup.dist_eq]
--  apply Nat.le_of_ceil_le at hn
--  have h5 : 1 / (n+1) < ε := by
--   rw [(one_div_lt (Nat.cast_add_one_pos n) hε)]
--   exact lt_of_le_of_lt hn (lt_add_one (n : ℝ))
--  exact lt_of_le_of_lt (hg n).right h5


/-- The product of a bounded continuous function and a function vanishing at infinity vanishes
at infinity. -/
lemma zero_at_infty_mul_BCF_ZeroAtInfty
    [NonUnitalSeminormedRing β] [NonUnitalSeminormedRing (α →ᵇ β)](f : α →ᵇ β) (g : C₀(α, β)) :
    Filter.Tendsto (f * g.toBCF) (Filter.cocompact α) (nhds 0) := by
  have : Filter.Tendsto (fun x => ‖f‖ * ‖g.toContinuousMap.toFun x‖)
      (Filter.cocompact α) (nhds (‖f‖ * ‖(0 : β)‖)) := by
    exact Tendsto.const_mul ‖f‖ (Filter.Tendsto.norm g.2)
  rw [norm_zero, mul_zero] at this
  apply squeeze_zero_norm _ this
  intro x
  calc ‖(f * (g.toBCF)) x‖ = ‖f x * (g.toBCF x)‖ := rfl
  _ ≤ ‖f x‖ * ‖g.toBCF x‖ := norm_mul_le (f x) (g.toBCF x)
  _ ≤  ‖f‖ * ‖g.toBCF x‖ :=
    mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm f x)
      (norm_nonneg (g.toBCF x))
  _ = ‖f‖ * ‖g.toContinuousMap.toFun x‖ := rfl


/-- A function which has compact support vanishes at infinity. -/
lemma zero_at_infty_of_hasCompactSupport [TopologicalSpace β] [Zero β]
    (f : C(α, β)) (hf : HasCompactSupport f) :
    Filter.Tendsto f (Filter.cocompact α) (nhds 0) := by
  rw [_root_.tendsto_nhds]
  intro s _ hzero
  rw [Filter.mem_cocompact]
  use tsupport f
  constructor
  · exact hf
  · intro x hx
    simp only [Set.mem_preimage]
    rw [← Set.not_mem_compl_iff, compl_compl] at hx
    rw [image_eq_zero_of_nmem_tsupport hx]
    exact hzero

/-! ### The case with β : RCLike

Whenever `β : RCLike`, one can apply Urysohn's lemma to show that any function vanishing at infinity
can be approximated by functions with compact support.
-/

open Urysohns

-- -- helped by Filippo Nuccio
/-- For a function which vanishes at infinity there is a sequence of functions with compact support
that tend to the given function. -/
lemma exist_HasCompactSupport_and_Tendsto [T2Space α] {𝕂 : Type*} [RCLike 𝕂] (f : C₀(α, 𝕂)) (ε : ℝ)
    (hε : 0 < ε) : ∃ (g : C₀(α ,𝕂)), HasCompactSupport g ∧ ‖f - g‖ < ε := by
-- take a set such that f is small outside it
  have hfltephalf : {x : α | dist (f x) 0 < ε /2} ∈ Filter.cocompact α := by
    apply Filter.eventually_iff.mp
    apply Metric.tendsto_nhds.mp (ZeroAtInftyContinuousMap.zero_at_infty' f)
    exact half_pos hε
  rw [Filter.mem_cocompact] at hfltephalf
-- take a compact set K including the above set
  obtain ⟨K, hKcp, hKcompl⟩ := hfltephalf
  rw [Set.compl_subset_comm] at hKcompl
-- take an open set with compact closure containing K
  obtain ⟨U, hUopen, hKsubU, hUccp⟩ := exists_isOpen_superset_and_isCompact_closure hKcp
-- take a function k which is 1 on K and supported in U by Urysohn's lemma
  obtain ⟨k, hk1K, hk0Uc, hkcp, hk01⟩ := exists_continuous_one_zero_of_isCompact hKcp
    (IsOpen.isClosed_compl hUopen) (LE.le.disjoint_compl_right hKsubU)
-- k is ℝ-valued, so need to compose with `ofRealCLM`
  have hkcp : HasCompactSupport
      (ContinuousMap.comp ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k) := by
    have hkcp1 : Function.support
        (ContinuousMap.comp ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k) ⊆
        Function.support k := by
      apply Function.support_comp_subset RCLike.ofReal_zero
    unfold HasCompactSupport
    exact IsCompact.closure_of_subset hkcp (subset_trans hkcp1 subset_closure)
-- define g as the product of f and k
  set g : C₀(α, 𝕂)
    := ⟨f.1 * (ContinuousMap.comp ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k),
      (zero_at_infty_of_hasCompactSupport (f.1 * (ContinuousMap.comp
      ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k)) hkcp.mul_left)⟩ with hg
  use g
  refine ⟨hkcp.mul_left, ?_⟩
-- g is close to f
  have hnormdiff : ∀ (x : α), ‖(f - g) x‖ ≤ ε / 2 := by
    intro x
    simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply]
    rw [hg]
    have hgval : g x = f x * k x := rfl
    rw [hgval]
    have hkval01 : 0 ≤ k x ∧ k x ≤ 1 := hk01 x
    have hfkx : f x - f x * k x = f x * (1 - k x) := by ring
    rw [hfkx]
-- when x ∈ K
    by_cases hxK : x ∈ K
    · rw [(hk1K hxK)]
      simp only [Pi.one_apply, algebraMap.coe_one, sub_self, mul_zero, norm_zero, ge_iff_le]
      exact le_of_lt (half_pos hε)
-- when x ∉ K
    · rw [norm_mul, ← mul_one (ε / 2)]
      apply mul_le_mul _ _ (norm_nonneg _) (le_of_lt (half_pos hε))
      · rw [Set.compl_subset_comm] at hKcompl
        rw [← sub_zero (f x), ← SeminormedAddCommGroup.dist_eq]
        apply le_of_lt (hKcompl hxK)
      · have h1subx : (1 - (k x : 𝕂)) = ((1 - k x) : ℝ) := by
          simp only [RCLike.ofReal_sub, algebraMap.coe_one]
        rw [h1subx, RCLike.norm_ofReal]
        nth_rw 2 [← abs_one]
        exact abs_le_abs_of_nonneg (sub_nonneg_of_le hkval01.2) (sub_le_self 1 hkval01.1)
  exact lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).mpr hnormdiff)
    (half_lt_self hε)


-- -- helped by Filippo Nuccio
-- /-- For a function which vanishes at infinity there is a sequence of functions with compact support
-- that tend to the given function. -/
-- lemma exist_HasCompactSupport_and_Tendsto' [LocallyCompactSpace α] [T2Space α]
--     {𝕂 : Type*} [RCLike 𝕂](f : C₀(α, 𝕂)) : ∃ (g : ℕ → C₀(α ,𝕂)),
--     (∀ (n : ℕ), HasCompactSupport (g n)) ∧ Filter.Tendsto g Filter.atTop (nhds f) := by
-- -- find a function gn for each n
--   have h : ∀ (n : ℕ), ∃ (gn : C₀(α, 𝕂)), HasCompactSupport gn ∧ ‖f - gn‖ ≤ 1/((n : ℝ)+1) := by
--     intro n
-- -- take a set such that f is small outside it
--     have h1 : {x : α | dist (f x) 0 < 1/((n : ℝ)+1)} ∈ Filter.cocompact α := by
--       apply Filter.eventually_iff.mp
--       apply Metric.tendsto_nhds.mp (ZeroAtInftyContinuousMap.zero_at_infty' f)
--       exact Nat.one_div_pos_of_nat
--     rw [Filter.mem_cocompact] at h1
-- -- take a compact set K including the above set
--     obtain ⟨K, hK⟩ := h1
--     rw [Set.compl_subset_comm] at hK
-- -- take an open set with compact closure containing K
--     obtain ⟨U, hU⟩ := exists_isOpen_superset_and_isCompact_closure hK.left
-- -- take a function k which is 1 on K and supported in U by Urysohn's lemma
--     obtain ⟨k, hk⟩ := exists_continuous_one_zero_of_isCompact hK.left
--       (IsOpen.isClosed_compl hU.left) (LE.le.disjoint_compl_right hU.right.left)
-- -- k is ℝ-valued, so need to compose with `ofRealCLM`
--     have hkcp : HasCompactSupport
--         (ContinuousMap.comp ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k) := by
--       have hkcp1 : Function.support
--           (ContinuousMap.comp ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k) ⊆
--           Function.support k := by
--         apply Function.support_comp_subset RCLike.ofReal_zero
--       unfold HasCompactSupport
--       exact IsCompact.closure_of_subset hk.right.right.left (subset_trans hkcp1 subset_closure)
-- -- define gn as the product of f and k
--     let gn : C₀(α, 𝕂)
--       := ⟨f.1 * (ContinuousMap.comp ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k),
--         (zero_at_infty_of_hasCompactSupport (f.1 * (ContinuousMap.comp
--         ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂), RCLike.ofRealCLM.cont⟩ k)) hkcp.mul_left)⟩
--     use gn
--     constructor
-- -- gn is compact
--     exact hkcp.mul_left
-- -- gn is close to f
--     have h2 : ∀ (x : α), ‖(f - gn) x‖ ≤ 1 / (↑n + 1) := by
--       intro x
--       have h21 : gn x = f x * k x := by rfl
--       have h22 : (f - gn) x = f x - gn x := by rfl
--       rw [h22, h21]
--       have h23 : 0 ≤ k x ∧ k x ≤ 1 := by
--        apply hk.right.right.right x
--       have h24 : f x - f x * k x = f x * (1 - k x) := by ring
--       rw [h24]
-- -- when x ∈ K
--       by_cases hxK : x ∈ K
--       · have h25 : k x = 1 := by exact (hk.1 hxK)
--         rw [h25]
--         simp only [algebraMap.coe_one, sub_self, mul_zero, norm_zero, one_div, inv_nonneg,
--           ge_iff_le]
--         exact le_of_lt (Nat.cast_add_one_pos n)
-- -- when x ∉ K
--       · rw [Set.compl_subset_comm] at hK
--         rw [norm_mul, mul_comm]
--         apply mul_le_mul
--         · have h26 : (1 - (k x : 𝕂)) = ((1 - k x) : ℝ) := by simp only [RCLike.ofReal_sub,
--             algebraMap.coe_one]
--           rw [h26, RCLike.norm_ofReal]
--           have h27 : 0 ≤ 1 - k x ∧ 1 - k x ≤ 1 := by
--             constructor
--             · nth_rw 1 [← sub_self 1]
--               exact (sub_le_sub (le_refl 1) h23.right)
--             · nth_rw 2 [← sub_zero 1]
--               exact (sub_le_sub (le_refl 1) h23.left)
--           have h28 : |1 - k x| ≤ |1| := by
--             exact abs_le_abs_of_nonneg h27.1 h27.2
--           rw [abs_one, ← Real.norm_eq_abs] at h28
--           exact h28
--         · rw [← one_div]
--           have h29 : dist (f x) 0 < 1/(n+1) := by
--             apply hK.2
--             exact Set.mem_compl hxK
--           rw [SeminormedAddCommGroup.dist_eq, sub_zero] at h29
--           exact le_of_lt h29
--         · simp only [norm_nonneg]
--         · norm_num
--     exact (BoundedContinuousFunction.norm_le (le_of_lt Nat.one_div_pos_of_nat)).mpr h2
-- -- make gn into a sequence
--   obtain ⟨g, hg⟩ := Classical.axiomOfChoice h
--   use g
--   constructor
--   · intro n
--     exact (hg n).left
--   · rw [Metric.tendsto_atTop]
--     intro ε hε
--     use Nat.ceil (1/ε)
--     intro n hn
--     rw [dist_comm, SeminormedAddCommGroup.dist_eq]
--     apply Nat.le_of_ceil_le at hn
--     have hnε  : 1 / (n+1) < ε := by
--      rw [(one_div_lt (Nat.cast_add_one_pos n) hε)]
--      exact lt_of_le_of_lt hn (lt_add_one (n : ℝ))
--     exact lt_of_le_of_lt (hg n).right hnε
--   done
