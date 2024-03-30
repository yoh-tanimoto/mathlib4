import Mathlib

open ZeroAtInfty Filter Urysohns Topology

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open BoundedContinuousFunction Topology Bornology

open Filter Metric

open ZeroAtInfty

-- /-- `C_c(α, β)` is the type of continuous functions `α → β` which have compact support from a
-- topological space to a metric space with a zero element.

-- When possible, instead of parametrizing results over `(f : C_c(α, β))`,
-- you should parametrize over `(F : Type*) [CompactlySupportedContinuousMap F α β] (f : F)`.

-- When you extend this structure, make sure to extend `CompactlySupportedContinuousMap`. -/
-- structure CompactlySupportedContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
--     [TopologicalSpace β] extends ZeroAtInftyContinuousMap α β : Type max u v where
--   hasCompactSupport' : HasCompactSupport toFun

-- @[inherit_doc]
-- scoped[CompactlySupported] notation (priority := 2000) "C_c(" α ", " β ")" =>
--     CompactlySupportedContinuousMap α β

-- @[inherit_doc]
-- scoped[CompactlySupported] notation α " →C_c " β => CompactlySupportedContinuousMap α β

-- open CompactlySupported

-- section

-- /-- `CompactlySupportedContinuousMapClass F α β` states that `F` is a type of continuous maps which
-- have compact support.

-- You should also extend this typeclass when you extend `CompactlySupportedContinuousMap`. -/
-- class CompactlySupportedContinuousMapClass (F : Type*) (α β : outParam <| Type*)
--     [TopologicalSpace α] [Zero β] [TopologicalSpace β] [FunLike F α β] extends
--     ZeroAtInftyContinuousMapClass F α β : Prop where
--   /-- Each member of the class has compact support. -/
--   hasCompactSupport (f : F) : HasCompactSupport f



-- namespace CompactlySupportedContinuousMap

-- section Basics

-- variable [TopologicalSpace β] [Zero β] [FunLike F α β] [CompactlySupportedContinuousMapClass F α β]

-- instance instFunLike : FunLike C_c(α, β) α β where
--   coe f := f.toFun
--   coe_injective' f g h := by
--     obtain ⟨⟨_, _⟩, _⟩ := f
--     obtain ⟨⟨_, _⟩, _⟩ := g
--     congr
--     exact ContinuousMap.ext (congrFun h)

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
 [T2Space X]

variable {𝕂 : Type*} [IsROrC 𝕂]

lemma zero_at_infty_of_hasCompactSupport (f : C(X, 𝕂)) (hf : HasCompactSupport f) :
    Filter.Tendsto f (Filter.cocompact X) (nhds 0) := by
 rw [Metric.tendsto_nhds]
 intro ε hε
 rw [Filter.eventually_iff, Filter.mem_cocompact]
 use tsupport f
 constructor
 · exact hf
 · intro x hx
   rw [← Set.not_mem_compl_iff, compl_compl] at hx
   rw [Set.mem_setOf_eq, image_eq_zero_of_nmem_tsupport hx, dist_self]
   exact hε
 done


variable {α : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
variable [NonUnitalSeminormedRing β] [NonUnitalSeminormedRing (α →ᵇ β)]


lemma zero_at_infty_mul_BCF_ZeroAtInfty (f : α →ᵇ β) (g : C₀(α, β)) :
    Filter.Tendsto (f * g.toBCF) (Filter.cocompact α) (nhds 0) := by
  have : Filter.Tendsto
      (fun x => ‖f‖ * ‖g.toContinuousMap.toFun x‖) (Filter.cocompact α) (nhds (‖f‖ * ‖(0 : β)‖)) := by
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
--   have h4 : ∀ (x : X), ‖(f - gn) x‖ ≤ 1 / (↑n + 1) := by
--    intro x
--    have h41 : gn x = f x * k x := by rfl
--    have h42 : (f - gn) x = f x - gn x := by rfl
--    rw [h42, h41]
--    have h43 : 0 ≤ k x ∧ k x ≤ 1 := by
--     apply hk.right.right.right x
--    have h44 : 0 ≤ 1 - k x ∧ 1 - k x ≤ 1 := by
--     constructor
--     nth_rw 1 [← sub_self 1]
--     exact (sub_le_sub (le_refl 1) h43.right)
--     nth_rw 2 [← sub_zero 1]
--     exact (sub_le_sub (le_refl 1) h43.left)
--    have h441 : |1 - k x| ≤ |1| := by
--     exact abs_le_abs_of_nonneg h44.1 h44.2
--    rw [abs_one] at h441
--    have h45 : f x - f x * k x = f x * (1 - k x) := by ring
--    rw [h45]
--    by_cases hxK : x ∈ K
--    have h46 : k x = 1 := by exact (hk.1 hxK)
--    rw [h46]
--    simp
--    apply le_of_lt (Nat.cast_add_one_pos n)
--    rw [Set.compl_subset_comm] at hK
--    have h47 : dist (f x) 0 < 1/(n+1) := by
--     apply hK.2
--     exact Set.mem_compl hxK
--    rw [SeminormedAddCommGroup.dist_eq, sub_zero] at h47
--    rw [norm_mul, mul_comm]
--    apply mul_le_mul
--    rw [← Complex.abs_ofReal, ← Complex.norm_eq_abs] at h441
--    have h471 : (1 - (k x : ℂ)) = ((1 - k x) : ℝ) := by simp
--    rw [← h471] at h441
--    exact h441
--    rw [← one_div]
--    exact le_of_lt h47
--    simp
--    norm_num
--   apply (BoundedContinuousFunction.norm_le (le_of_lt Nat.one_div_pos_of_nat)).mpr h4
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

-- -- helped by Filippo Nuccio
lemma exist_HasCompactSupport_and_Tendsto (f : C₀(X, 𝕂)) : ∃ (g : ℕ → C₀(X ,𝕂)),
    (∀ (n : ℕ), HasCompactSupport (g n)) ∧ Filter.Tendsto g Filter.atTop (nhds f) := by
 have h : ∀ (n : ℕ), ∃ (gn : C₀(X, 𝕂)), HasCompactSupport gn ∧ ‖f - gn‖ ≤ 1/((n : ℝ)+1) := by
  intro n
  have h1 : {x : X | dist (f x) 0 < 1/((n : ℝ)+1)} ∈ Filter.cocompact X := by
   apply Filter.eventually_iff.mp
   apply Metric.tendsto_nhds.mp (ZeroAtInftyContinuousMap.zero_at_infty' f)
   exact Nat.one_div_pos_of_nat
  rw [Filter.mem_cocompact] at h1
  obtain ⟨K, hK⟩ := h1
  rw [Set.compl_subset_comm] at hK
  obtain ⟨U, hU⟩ := exists_isOpen_superset_and_isCompact_closure hK.left
  obtain ⟨k, hk⟩ := exists_continuous_one_zero_of_isCompact hK.left (IsOpen.isClosed_compl hU.left) (LE.le.disjoint_compl_right hU.right.left)
  have hkcp : HasCompactSupport (ContinuousMap.comp ⟨(IsROrC.ofRealCLM : ℝ →L[ℝ] 𝕂), IsROrC.ofRealCLM.cont⟩ k) := by
   have hkcp1 : Function.support (ContinuousMap.comp ⟨(IsROrC.ofRealCLM : ℝ →L[ℝ] 𝕂), IsROrC.ofRealCLM.cont⟩ k) ⊆ Function.support k := by
    apply Function.support_comp_subset IsROrC.ofReal_zero
   unfold HasCompactSupport
   exact IsCompact.closure_of_subset hk.right.right.left (subset_trans hkcp1 subset_closure)

  let gn : C₀(X, 𝕂)
    := ⟨f.1 * (ContinuousMap.comp ⟨(IsROrC.ofRealCLM : ℝ →L[ℝ] 𝕂), IsROrC.ofRealCLM.cont⟩ k),
       (zero_at_infty_of_hasCompactSupport (f.1 * (ContinuousMap.comp
       ⟨(IsROrC.ofRealCLM : ℝ →L[ℝ] 𝕂), IsROrC.ofRealCLM.cont⟩ k)) hkcp.mul_left)⟩
  use gn
  constructor
  exact hkcp.mul_left
  have h4 : ∀ (x : X), ‖(f - gn) x‖ ≤ 1 / (↑n + 1) := by
   intro x
   have h41 : gn x = f x * k x := by rfl
   have h42 : (f - gn) x = f x - gn x := by rfl
   rw [h42, h41]
   have h43 : 0 ≤ k x ∧ k x ≤ 1 := by
    apply hk.right.right.right x
   have h44 : 0 ≤ 1 - k x ∧ 1 - k x ≤ 1 := by
    constructor
    nth_rw 1 [← sub_self 1]
    exact (sub_le_sub (le_refl 1) h43.right)
    nth_rw 2 [← sub_zero 1]
    exact (sub_le_sub (le_refl 1) h43.left)
   have h441 : |1 - k x| ≤ |1| := by
    exact abs_le_abs_of_nonneg h44.1 h44.2
   rw [abs_one, ← Real.norm_eq_abs] at h441
   have h45 : f x - f x * k x = f x * (1 - k x) := by ring
   rw [h45]
   by_cases hxK : x ∈ K
   have h46 : k x = 1 := by exact (hk.1 hxK)
   rw [h46]
   simp
   apply le_of_lt (Nat.cast_add_one_pos n)
   rw [Set.compl_subset_comm] at hK
   have h47 : dist (f x) 0 < 1/(n+1) := by
    apply hK.2
    exact Set.mem_compl hxK
   rw [SeminormedAddCommGroup.dist_eq, sub_zero] at h47
   rw [norm_mul, mul_comm]
   apply mul_le_mul
   have h471 : (1 - (k x : 𝕂)) = ((1 - k x) : ℝ) := by simp
   rw [h471]
   rw [IsROrC.norm_ofReal]
   exact h441
   rw [← one_div]
   exact le_of_lt h47
   simp
   norm_num
  apply (BoundedContinuousFunction.norm_le (le_of_lt Nat.one_div_pos_of_nat)).mpr h4
 obtain ⟨g, hg⟩ := Classical.axiomOfChoice h
 use g
 constructor
 intro n
 exact (hg n).left
 rw [Metric.tendsto_atTop]
 intro ε hε
 use Nat.ceil (1/ε)
 intro n hn
 rw [dist_comm, SeminormedAddCommGroup.dist_eq]
 apply Nat.le_of_ceil_le at hn
 have h5 : 1 / (n+1) < ε := by
  rw [(one_div_lt (Nat.cast_add_one_pos n) hε)]
  exact lt_of_le_of_lt hn (lt_add_one (n : ℝ))
 exact lt_of_le_of_lt (hg n).right h5
