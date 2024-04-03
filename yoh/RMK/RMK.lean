import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Function.Support
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.ContinuousFunction.CocompactMap
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Topology.Sets.Compacts
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner




-- /-! ### Construction of the content: -/


-- /-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
-- `λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
-- content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
-- def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
--   sInf (Λ '' { f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })
-- #align riesz_content_aux rieszContentAux

-- section RieszMonotone

-- /-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
-- functions f on X such that `f ≥ 1` on K. -/
-- theorem rieszContentAux_image_nonempty (K : Compacts X) :
--     (Λ '' { f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
--   rw [image_nonempty]
--   use (1 : X →ᵇ ℝ≥0)
--   intro x _
--   simp only [BoundedContinuousFunction.coe_one, Pi.one_apply]; rfl
-- #align riesz_content_aux_image_nonempty rieszContentAux_image_nonempty

-- /-- Riesz content λ (associated with a positive linear functional Λ) is
-- monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
-- theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
--     rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ :=
--   csInf_le_csInf (OrderBot.bddBelow _) (rieszContentAux_image_nonempty Λ K₂)
--     (image_subset Λ (setOf_subset_setOf.mpr fun _ f_hyp x x_in_K₁ => f_hyp x (h x_in_K₁)))
-- #align riesz_content_aux_mono rieszContentAux_mono

-- end RieszMonotone

-- section RieszSubadditive

-- /-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
-- content of K; namely `λ(K) ≤ Λ f`. -/
-- theorem rieszContentAux_le {K : Compacts X} {f : X →ᵇ ℝ≥0} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
--     rieszContentAux Λ K ≤ Λ f :=
--   csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩
-- #align riesz_content_aux_le rieszContentAux_le

-- /-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
-- functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
-- function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
-- theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
--     ∃ f : X →ᵇ ℝ≥0, (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
--   --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
--   obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
--     exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
--       (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
--   refine' ⟨f, f_hyp.left, _⟩
--   rw [f_hyp.right]
--   exact α_hyp
-- #align exists_lt_riesz_content_aux_add_pos exists_lt_rieszContentAux_add_pos

-- /-- The Riesz content λ associated to a given positive linear functional Λ is
-- finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
-- theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
--     rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
--   apply NNReal.le_of_forall_pos_le_add
--   intro ε εpos
--   --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
--   obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
--   obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
--   --let `f := f1 + f2` test function for the content of `K`
--   have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
--     rintro x (x_in_K1 | x_in_K2)
--     · exact le_add_right (f_test_function_K1.left x x_in_K1)
--     · exact le_add_left (f_test_function_K2.left x x_in_K2)
--   --use that `Λf` is an upper bound for `λ(K1⊔K2)`
--   apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
--   rw [map_add]
--   --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
--   apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
--     (le_of_eq _)
--   rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]
-- #align riesz_content_aux_sup_le rieszContentAux_sup_le

-- end RieszSubadditive

noncomputable section

open BoundedContinuousFunction NNReal ENNReal

open Set Function TopologicalSpace

variable {X : Type*} [TopologicalSpace X]
variable (Λ : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ (f : X →ᵇ ℝ), 0 ≤ f → 0 ≤ Λ f)

lemma Λ_mono {f g : X →ᵇ ℝ} (h : f ≤ g) : Λ f ≤ Λ g := by
  have : 0 ≤ g - f := by exact sub_nonneg.mpr h
  calc Λ f ≤ Λ f + Λ (g - f) := by exact le_add_of_nonneg_right (hΛ (g - f) this)
  _ = Λ (f + (g - f)) := by rw [← LinearMap.map_add Λ f (g - f)]
  _ = Λ g := by simp only [add_sub_cancel]


-- /-! ### Construction of the content: -/

/-- Given a positive linear functional Λ on X, for `V ⊆ X` open define
-- `λ(K) = sup {Λf | 0 ≤ f ≤ 1 and supp f ⊆ V}`. -/
def rieszContentAux' : Opens X → ℝ≥0∞ := fun V =>
  sSup ((fun (x : ℝ) => ENNReal.ofReal x) ''
    (Λ '' ({ f : X →ᵇ ℝ | (tsupport f.1) ⊆ (V : Set X) ∧ ∀ x : X, 0 ≤ f.1 x ∧ f.1 x ≤ 1})))

section RieszMonotone

/-- For any pair of open subsets `V₁ ⊆ V₂`, it holds that Λ V₁ ≤ Λ V₂. -/
theorem rieszContentAux'_image_nonempty (V : Opens X) :
    ((fun (x : ℝ) => ENNReal.ofReal x) ''
    (Λ '' { f : X →ᵇ ℝ | (tsupport f.1) ⊆ V ∧ ∀ x : X, 0 ≤ f.1 x ∧ f.1 x ≤ 1})).Nonempty := by
  rw [image_nonempty, image_nonempty]
  use (0 : X →ᵇ ℝ)
  simp only [coe_to_continuous_fun, mem_setOf_eq, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    le_refl, zero_le_one, and_self, implies_true, and_true]
  unfold tsupport
  rw [Function.support_zero', closure_empty]
  exact Set.empty_subset _
  done

/-- rieszContentAux' is monotone on open sets. -/
lemma rieszContentAux'_mono {V₁ V₂ : Opens X} (h : V₁ ≤ V₂) :
    rieszContentAux' Λ V₁ ≤ rieszContentAux' Λ V₂ := by
  apply sSup_le_sSup
  rw [← Set.image_comp, ← Set.image_comp]
  apply Set.image_subset
  intro f
  simp only [coe_to_continuous_fun, mem_setOf_eq, and_imp]
  intro hf hfx
  constructor
  · intro x hx
    exact (mem_of_subset_of_mem (fun ⦃a⦄ a_1 => h (hf a_1)) hx)
  · exact hfx
  done


/-- For any subset E of X, we define rieszContent' Λ E to be the inf of
riesContent' V such that E ⊆ V. -/
def rieszContent' : Set X → ℝ≥0∞ := fun E  =>
  sInf (rieszContentAux' Λ '' { V : Opens X | E ⊆ V })

/-- rieszContent' is monotone. -/
lemma rieszContent'_mono {E₁ E₂ : Set X} (h : E₁ ⊆ E₂) : rieszContent' Λ E₁ ≤ rieszContent' Λ E₂ := by
  apply sInf_le_sInf
  apply Set.image_subset
  intro V
  simp only [mem_setOf_eq]
  exact fun a ⦃a_1⦄ a_2 => a (h a_2)

/-- rieszContent' coincides with rieszContentAux' on open sets. -/
lemma rieszContent'_eq_rieszContentAux'_open (V : Opens X) :
    rieszContent' Λ V = rieszContentAux' Λ V := by
  apply le_antisymm
  apply sInf_le_of_le
  use V
  simp only [SetLike.coe_subset_coe, mem_setOf_eq, le_refl, true_and]
  rfl
  exact rieszContentAux'_mono Λ fun ⦃a⦄ a => a
  apply le_sInf
  intro x hx
  simp only [SetLike.coe_subset_coe, mem_image, mem_setOf_eq] at hx
  obtain ⟨V', hV'⟩ := hx
  rw [← hV'.2]
  exact rieszContentAux'_mono Λ hV'.1

def M_F (Λ : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Set (Set X) := {E : Set X | rieszContent' Λ E < ∞
  ∧ rieszContent' Λ E = sSup (rieszContent' Λ '' {K : Set X | IsCompact K ∧ K ⊆ E })}

def M (Λ : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Set (Set X) :=
  {E : Set X | ∀ (K : Set X), IsCompact K → (E ∩ K) ∈ M_F Λ}

-- P.42 of Rudin "Real and Complex analysis"
-- Continue with "Proof that μ and M have the required properties"

lemma in_M_F_of_rieszContent'_zero {E : Set X} (h : rieszContent' Λ E = 0) : E ∈ M_F Λ := by
  sorry

lemma in_M_of_rieszContent'_zero {E : Set X} (h : rieszContent' Λ E = 0) : E ∈ M Λ := by
  intro K _
  have : rieszContent' Λ (E ∩ K) = 0 := by
    apply le_antisymm
    rw [← h]
    exact rieszContent'_mono Λ (Set.inter_subset_left E K)
    exact zero_le (rieszContent' Λ (E ∩ K))
  constructor
  · rw [this]
    exact zero_lt_top
  · apply le_antisymm
    rw [this]
    exact zero_le (sSup (rieszContent' Λ '' {K_1 | IsCompact K_1 ∧ K_1 ⊆ E ∩ K}))
    apply sSup_le
    intro x hx
    obtain ⟨E', hE'⟩ := hx
    rw [← hE'.2]
    exact rieszContent'_mono Λ hE'.1.2

/-- The Riesz content μ associated to a given positive linear functional Λ is
finitely subadditive for open sets : `μ (V₁ ∪ V₂) ≤ μ(V₁) + μ(V₂)`. -/
lemma rieszContentAux'_sup_le (V₁ V₂ : Opens X) :
    rieszContentAux' Λ (V₁ ⊔ V₂) ≤ rieszContentAux' Λ V₁ + rieszContentAux' Λ V₂ := by
  sorry


-- to mathlib NEEReal??

lemma sInf_diff_singleton_eq_sInf {s : Set ENNReal} {b : ENNReal} (h : ∃ (a : ENNReal), a ∈ s ∧ a < b)
    : sInf (s \ {b}) = sInf s := by
  apply le_antisymm
  apply sInf_le_sInf_of_forall_exists_le
  intro x hxins
  obtain ⟨a, ha⟩ := h
  by_cases hx : x = b
  · use a
    constructor
    · constructor
      · exact ha.1
      · simp only [mem_singleton_iff]
        exact ne_of_lt ha.2
    · rw [hx]
      exact le_of_lt ha.2
  · use x
    constructor
    · constructor
      exact hxins
      simp only [mem_singleton_iff]
      exact hx
    · exact Preorder.le_refl x
  exact sInf_le_sInf (Set.diff_subset _ _)

variable (s : Set ℝ≥0∞)
#check s \ ({⊤} : Set ℝ≥0∞)

lemma ENNReal.toNNReal_sInf' (s : Set ℝ≥0∞) (hs : ∃ r ∈ s, r ≠ ⊤)
    : (sInf s).toNNReal = sInf (ENNReal.toNNReal '' (s \ {⊤})) := by
  have : Set.Nonempty (s \ ({⊤} : Set ℝ≥0∞)) := by
    exact hs
  have : sInf (s \ ({⊤} : Set ℝ≥0∞)) = sInf s := by
    apply sInf_diff_singleton_eq_sInf
    obtain ⟨r, hr⟩ := hs
    use r
    constructor
    · exact hr.1
    · exact Ne.lt_top hr.2
  rw [← this]
-- use ENNReal.neTopEquivNNReal

lemma ex_in_add_pos_lt {s : Set ℝ≥0∞} (hs : Nonempty s) (hsinf : sInf s < ⊤) (ε : ℝ≥0) :
    ∃ (a : ℝ≥0), ENNReal.ofNNReal a ∈ s ∧ a < ENNReal.toNNReal (sInf s) + ε := by
  sorry

/-- The Riesz content can be approximated arbitrarily well from outside by open sets. -/
lemma exists_lt_rieszContent'_add_pos {E : Set X} (hE : rieszContent' Λ E < ∞)
    {ε : ℝ≥0} (εpos : 0 < ε) : ∃ (V : Opens X), (V : Set X) ⊆ E ∧ rieszContent' Λ V ≤ rieszContent' Λ E + ε := by
  by_cases hinf : rieszContent' Λ E = ∞
  · use ⟨∅, isOpen_empty⟩
    have : rieszContent' Λ ((Opens.mk (∅ : Set X) isOpen_empty) : Set X) = 0 := by
      rw [rieszContent'_eq_rieszContentAux'_open Λ ⟨∅, isOpen_empty⟩]
      apply le_antisymm
      apply sSup_le
      simp only [nonpos_iff_eq_zero]
      intro x hx
      obtain ⟨z, hz⟩ := hx
      obtain ⟨f, hf⟩ := hz.1
      rw [← hz.right, ← hf.right]
      simp only [ofReal_eq_zero, ge_iff_le]
      have : f.toFun = 0 := by
        exact tsupport_eq_empty_iff.mp (Set.eq_empty_of_subset_empty (Set.mem_setOf.mp hf.1).1)
      simp only [ContinuousMap.toFun_eq_coe, coe_to_continuous_fun] at this
      have : f = 0 := by
        apply (BoundedContinuousFunction.forall_coe_zero_iff_zero f).mp
        intro x
        exact congrFun this x
      rw [this, LinearMap.map_zero Λ]
      simp only [Opens.mk_empty, zero_le]
    constructor
    · exact Set.empty_subset E
    · rw [this]
      exact zero_le (rieszContent' Λ E + ↑ε)
  · have : ∃ (a : ℝ≥0), rieszContent' Λ E = a := by
      use (rieszContent' Λ E).toNNReal
      exact (coe_toNNReal hinf).symm
    obtain ⟨a, ha⟩ := this
    rw [ha,]




open ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
 [T2Space X] [MeasurableSpace X] [BorelSpace X]


theorem RMK (Λ : C₀(X, ℂ) → ℂ) : Continuous Λ ∧ (∀ (f : C₀(X, ℂ)) (x : X), ((f x).re ≥ 0 ∧ (f x).im = 0) → ((Λ f).re ≥ 0 ∧ (Λ f).im = 0)) →
 ∃ (μ : MeasureTheory.Measure X), (∀ (f : C₀(X, ℂ)), ∫ (x : X), f x ∂μ = Λ f) := by
 sorry
