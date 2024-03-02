import Mathlib

open ZeroAtInfty Filter Urysohns

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
 [T2Space X]

variable (k : C(X, ℝ))
def CoR : C(ℝ, ℂ) := ⟨Complex.ofReal', Complex.continuous_ofReal⟩

lemma CompactSupportZeroAtInfty (f : C(X, ℂ)) (hf : HasCompactSupport f)
 : Filter.Tendsto f (Filter.cocompact X) (nhds 0) := by
 rw [Metric.tendsto_nhds]
 intro ε hε
 rw [Filter.eventually_iff, Filter.mem_cocompact]
 use closure (Function.support f)
 constructor
 have hf' : IsCompact (closure (Function.support f)) := by
  exact hf
 exact hf'
 intro x hx
 rw [← Set.not_mem_compl_iff, compl_compl] at hx
 have hfx : f x = 0 := by
  have hxns : x ∉ Function.support f := by exact not_mem_of_not_mem_closure hx
  rw [← Function.nmem_support]
  exact hxns
 have hxz : dist (f x) 0 < ε := by
  rw [hfx, dist_self]
  exact hε
 exact hxz

example (g : C(X, ℂ)) (hG : HasCompactSupport g)
 : ∃ (g' : C₀(X, ℂ)), ∀ (x : X), g x = g' x := by
 let g' : C₀(X, ℂ) := ⟨g, (CompactSupportZeroAtInfty g hG)⟩
 use g'
 intro x
 rfl

lemma HasCompactSupportProduct (f : C(X, ℂ)) (g : C(X, ℂ)) (hG : HasCompactSupport g)
: HasCompactSupport (f * g) := hG.mul_left
--  have hs : Function.support (f * g) ⊆ Function.support g := by
--   simp
--  have hG' : IsCompact (closure (Function.support g)) := by exact hG
--  have hs' : Function.support (f * g) ⊆ closure (Function.support g) := by
--   exact subset_trans hs subset_closure
--  unfold HasCompactSupport
--  exact IsCompact.closure_of_subset hG' hs'
--  done

lemma CompactNeightbourhood (K : Set X) (h : IsCompact K)
 : ∃ (U : Set X), IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) :=
  exists_isOpen_superset_and_isCompact_closure h
--  have h1 : ∀ (p : X), ∃ (Up : Set X), p ∈ Up ∧ IsOpen Up ∧ IsCompact (closure Up) := by
--   intro p
--   obtain ⟨Np, hNp⟩ := exists_compact_mem_nhds p
--   use interior Np
--   constructor
--   refine mem_interior_iff_mem_nhds.mpr ?h.left.a
--   exact hNp.right
--   constructor
--   exact isOpen_interior
--   have h2 : closure (interior Np) ⊆ Np := by
--    exact closure_minimal interior_subset (IsCompact.isClosed hNp.left)
--   exact IsCompact.of_isClosed_subset hNp.left isClosed_closure h2
--  obtain ⟨f, hf⟩ := Classical.axiomOfChoice h1
--  have h3 : ∀ (p : X), IsOpen (f p) := by
--   intro p
--   exact (hf p).right.left
--  have h4 : K ⊆ ⋃ p, f p := by
--   intro p hp
--   use f p
--   constructor
--   use p
--   exact (hf p).left
--  obtain ⟨g, hg⟩ := IsCompact.elim_finite_subcover h f h3 h4
--  use ⋃ p ∈ g, f p
--  constructor
--  exact isOpen_biUnion fun i a => h3 i
--  constructor
--  exact hg
--  rw [Finset.closure_biUnion]
--  refine Finset.isCompact_biUnion g ?h.right.right.hf
--  intro i hi
--  exact (hf i).right.right
--  done

variable (k : C(X, ℂ))
variable (f : C₀(X, ℂ))
#check f * k

-- instance : Semiring C₀(X, ℂ) := by sorry
instance : StarRing C₀(X, ℂ) := by infer_instance

-- def StarAlegbraCC : (StarSubalgebra ℂ C₀(X, ℂ)) := by sorry

lemma ApproximatedByCompactlySuppportedFunctions (f : C₀(X, ℂ))
 : ∃ (g : ℕ → C₀(X ,ℂ)),
 (∀ (n : ℕ), HasCompactSupport (g n)) ∧ Filter.Tendsto g Filter.atTop (nhds f) := by
 have h : ∀ (n : ℕ), ∃ (gn : C₀(X, ℂ)), HasCompactSupport gn ∧ ‖f - gn‖ ≤ 1/((n : ℝ)+1) := by
  have h1 : ∀ ε > 0, ∀ᶠ (x : X) in Filter.cocompact X, dist (ContinuousMap.toFun f.toContinuousMap x) 0 < ε := by
   exact Metric.tendsto_nhds.mp (ZeroAtInftyContinuousMap.zero_at_infty' f)
  intro n
  have h21 : 0 < 1 / ((n : ℝ)+1) := by
   exact Nat.one_div_pos_of_nat
  have h2 : {x : X | dist (ContinuousMap.toFun f.toContinuousMap x) 0 < 1/((n : ℝ)+1)} ∈ Filter.cocompact X := by
   apply Filter.eventually_iff.mp
   apply h1
   exact h21
  have h3 : ∃ (s : Set X), IsCompact s ∧ {x : X | dist (ContinuousMap.toFun f.toContinuousMap x) 0 < 1/((n : ℝ)+1)}ᶜ ⊆ s := by
   rw [Filter.mem_cocompact] at h2
   obtain ⟨t, ht⟩ := h2
   use t
   rw [Set.compl_subset_comm] at ht
   exact ht
  obtain ⟨K, hK⟩ := h3
  obtain ⟨U, hU⟩ := CompactNeightbourhood K hK.left
  obtain ⟨k, hk⟩ := exists_continuous_one_zero_of_isCompact hK.left (IsOpen.isClosed_compl hU.left) (LE.le.disjoint_compl_right hU.right.left)
  have hkcp : HasCompactSupport (ContinuousMap.comp CoR k) := by
   have hk1 : CoR 0 = 0 := by rfl
   have hk2 : Function.support (ContinuousMap.comp CoR k) ⊆ Function.support k := by
    apply Function.support_comp_subset hk1
--   have hk3 : IsCompact (closure (Function.support (ContinuousMap.comp CoR k))) := by
   unfold HasCompactSupport
   exact IsCompact.closure_of_subset hk.right.right.left (subset_trans hk2 subset_closure)

   --Function.support_comp_subset
  let gn : C₀(X, ℂ) := ⟨f.1 * (ContinuousMap.comp CoR k), (CompactSupportZeroAtInfty (f.1 * (ContinuousMap.comp CoR k)) (HasCompactSupportProduct f.1 (ContinuousMap.comp CoR k) hkcp))⟩
  use gn
  constructor
  exact HasCompactSupportProduct f.1 (ContinuousMap.comp CoR k) hkcp
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
   rw [abs_one] at h441
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
   rw [← Complex.abs_ofReal, ← Complex.norm_eq_abs] at h441
   have h471 : (1 - (k x : ℂ)) = ((1 - k x) : ℝ) := by simp
   rw [← h471] at h441
   exact h441
   rw [← one_div]
   exact le_of_lt h47
   simp
   norm_num
  apply (BoundedContinuousFunction.norm_le (le_of_lt h21)).mpr h4
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


-- -- variable (M : ℝ) (PM : 0 ≤ M) (F : C(X, ℂ)) (P : ∀ (x : X), ‖F x‖ ≤ M)
-- -- C(X, ℂ) is not bounded!
-- -- variable (M : ℝ) (PM : 0 ≤ M) (F : C₀(X, ℂ)) (P : ∀ (x : X), ‖F x‖ ≤ M)
-- -- C₀(X, ℂ) is bounded, but not an extension of BoundedContinuousFunction X ℂ!
-- variable (M : ℝ) (PM : 0 ≤ M) (F : BoundedContinuousFunction X ℂ) (P : ∀ (x : X), ‖F x‖ ≤ M)
-- #check (BoundedContinuousFunction.norm_le PM).mpr P


universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open BoundedContinuousFunction Topology Bornology

open Filter Metric

structure CompactlySupportedContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ZeroAtInftyContinuousMap α β : Type max u v where
  compactly_supported' : IsCompact (closure (Function.support toFun))
#align compactly_supported_continuous_map CompactlySupportedContinuousMap


@[inherit_doc]
scoped[CompactlySupported] notation (priority := 2000) "C_c(" α ", " β ")" => CompactlySupportedContinuousMap α β

@[inherit_doc]
scoped[CompactlySupported] notation α " →C_c " β => CompactlySupportedContinuousMap α β

open CompactlySupported ZeroAtInfty

section

/-- `ZeroAtInftyContinuousMapClass F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `ZeroAtInftyContinuousMap`. -/
class CompactlySupportedMapClass (F : Type*) (α β : outParam <| Type*) [TopologicalSpace α]
    [Zero β] [TopologicalSpace β] [FunLike F α β] extends ZeroAtInftyContinuousMapClass F α β : Prop where
  /-- Each member of the class tends to zero along the `cocompact` filter. -/
  compactly_supported  (f : F) : Tendsto f (cocompact α) (𝓝 0)
#align compactly_supported_continuous_map_class ZeroAtInftyContinuousMapClass

variable (f : C_c(ℝ, ℝ))
variable (x : ℝ)
#check f

#check f.compactly_supported'

end
