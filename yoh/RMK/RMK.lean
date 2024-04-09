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
  constructor
  · rw [h]
    simp only [zero_lt_top]
  · apply le_antisymm
    rw [h]
    simp only [zero_le]
    apply sSup_le
    intro b hb
    obtain ⟨K, hK⟩ := hb
    rw [← hK.2]
    exact rieszContent'_mono Λ (Set.mem_setOf.mp hK.1).2

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


-- to mathlib UrysohnsLemma?

open BigOperators

lemma exists_tsupport_one_of_isOpen_isClosed [NormalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsClosed t) (hst : t ⊆ s) : ∃ f : C(X, ℝ), tsupport f ⊆ s ∧ EqOn f 1 t
    ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨U, V, hUV⟩ := normal_separation (IsOpen.isClosed_compl hs) ht
      (HasSubset.Subset.disjoint_compl_left hst)
    have : Disjoint (closure U) t := by
      apply le_compl_iff_disjoint_right.mp
      apply _root_.subset_trans _ (Set.compl_subset_compl.mpr hUV.2.2.2.1)
      apply (IsClosed.closure_subset_iff (IsOpen.isClosed_compl hUV.2.1)).mpr
      exact Set.subset_compl_iff_disjoint_right.mpr hUV.2.2.2.2
    obtain ⟨f, hf⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure ht this
    use f
    constructor
    · apply _root_.subset_trans _ (Set.compl_subset_comm.mp hUV.2.2.1)
      rw [← IsClosed.closure_eq (IsOpen.isClosed_compl hUV.1)]
      apply closure_mono
      rw [Set.subset_compl_iff_disjoint_left, Function.disjoint_support_iff]
      exact Set.EqOn.mono subset_closure hf.1
    · exact hf.2

open Classical

lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed [NormalSpace X] [T2Space X]
    [LocallyCompactSpace X] {n : ℕ} {t : Set X} {s : Fin n → Set X}
    (hs : ∀ (i : Fin n), IsOpen (s i))
    (ht : IsClosed t) (htcp : IsCompact t) (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧ EqOn (∑ i, f i) 1 t
    ∧ ∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1 := by
  rcases n with _ | n
  · simp only [Nat.zero_eq, Finset.univ_eq_empty, Finset.sum_empty, mem_Icc, IsEmpty.forall_iff,
    and_true, exists_const]
    have : t = ∅ := by
      rw [Set.iUnion_of_empty s] at hst
      exact subset_eq_empty hst rfl
    constructor
    · exact trivial
    · intro x
      rw [this]
      exact fun a => a.elim
  induction' n with n ih
  · simp only [Nat.zero_eq, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, mem_Icc]
    obtain ⟨g, hg⟩ := exists_tsupport_one_of_isOpen_isClosed (isOpen_iUnion hs) ht hst
    set f := fun (i : Fin 1) => g with hf
    use f
    have : ∀ (i : Fin 1), s i = ⋃ j, s j := by
      intro i
      apply subset_antisymm
      · exact Set.subset_iUnion _ _
      · apply Set.iUnion_subset
        intro j
        have : j = i := Eq.trans (Fin.eq_zero j) (Eq.symm (Fin.eq_zero i))
        apply subset_of_eq
        rw [← this]
    constructor
    · intro i
      rw [hf]
      simp only
      rw [this i]
      exact hg.1
    constructor
    · exact hg.2.1
    · intro i
      rw [hf]
      simp only
      exact hg.2.2
  · have : ∀ (x : X), x ∈ t → ∃ (Wx : Set X), x ∈ Wx ∧ IsOpen Wx ∧ IsCompact (closure Wx)
        ∧ ∃ (i : Fin (n+2)), (closure Wx) ⊆ s i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((Set.mem_of_subset_of_mem hst) hx)
      obtain ⟨cWx, hWx⟩ := exists_compact_subset (hs i) hi
      use interior cWx
      constructor
      · exact hWx.2.1
      constructor
      · simp only [isOpen_interior]
      constructor
      · apply IsCompact.of_isClosed_subset hWx.1 isClosed_closure
        nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hWx.1)]
        exact closure_mono interior_subset
      · use i
        apply _root_.subset_trans _ hWx.2.2
        nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hWx.1)]
        exact closure_mono interior_subset
    set W : X → Set X := fun x => if hx : x ∈ t then Classical.choose (this x hx) else default with hW
    have : ∀ (x : X), x ∈ t → W x ∈ nhds x := by
      intro x hx
      apply mem_nhds_iff.mpr
      use W x
      constructor
      · exact fun ⦃a⦄ a => a
      · rw [hW]
        simp only
        rw [dif_pos hx]
        exact And.intro (Classical.choose_spec (this x hx)).2.1 (Classical.choose_spec (this x hx)).1
    obtain ⟨ι, hι⟩ := IsCompact.elim_nhds_subcover htcp W this
    set Wx : Fin (n+2) → ι → Set X := fun i xj =>
      if hmV : closure (W xj) ⊆ s i then closure (W xj) else ∅ with hWx
    set H : Fin (n+2) → Set X := fun i => ⋃ xj, closure (Wx i xj) with hH
    have IsClosedH : ∀ (i : Fin (n+2)), IsClosed (H i) := by
      intro i
      rw [hH]
      simp only
      exact isClosed_iUnion_of_finite (fun (xj : ι) => isClosed_closure)
    have IsHSubS : ∀ (i : Fin (n+2)), H i ⊆ s i := by
      intro i
      rw [hH]
      simp only
      apply Set.iUnion_subset
      intro xj
      rw [hWx]
      simp only
      by_cases hmV : closure (W xj) ⊆ s i
      · rw [dif_pos hmV, closure_closure]
        exact hmV
      · rw [dif_neg hmV, closure_empty]
        exact Set.empty_subset _
    set g : Fin (n+2) → C(X, ℝ) := fun i => Classical.choose
      (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i)) with hg
    set f : Fin (n+2) → C(X, ℝ) := fun i => (∏ j in {j : Fin n| j < i}.toFinset, (1 - g j)) * g i with hf
    use f
    constructor
    · rw [hf]
      simp only
      intro i
      apply _root_.subset_trans tsupport_mul_subset_right
      exact (Classical.choose_spec
        (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))).1
    constructor
    · sorry
    · sorry


  -- use exists_compact_subset

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

lemma ENNReal.toNNReal_sInf' {s : Set ℝ≥0∞} (hs : ∃ (r : ℝ≥0∞), r ∈ s ∧ r ≠ ⊤) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' (s \ {⊤})) := by
  rw [← ENNReal.toNNReal_sInf]
  have : sInf (s \ ({⊤} : Set ℝ≥0∞)) = sInf s := by
    apply sInf_diff_singleton_eq_sInf
    obtain ⟨r, hr⟩ := hs
    use r
    constructor
    · exact hr.1
    · exact Ne.lt_top hr.2
  rw [← this]
  intro x hx
  exact (Set.mem_diff_singleton.mp hx).right

lemma toReal_eq_toReal_toNNReal (x : ℝ≥0∞) : x.toReal = (x.toNNReal).toReal := by
  exact rfl

lemma NNReal.bddBelow (s : Set ℝ≥0) : BddBelow s := by
  exact OrderBot.bddBelow s

lemma toReal_sInf_eq_sInf_toReal {s : Set ℝ≥0} (hs : Set.Nonempty s) :
    (sInf s).toReal = sInf (toReal '' s) := by
  apply le_antisymm
  have : ∀ (b : ℝ), b ∈ (toReal '' s) → (sInf s).toReal ≤ b := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    rw [← ha.2]
    simp only [NNReal.coe_le_coe]
    apply csInf_le (OrderBot.bddBelow s) ha.1
  exact le_csInf (Set.image_nonempty.mpr hs) this
  rw [(csInf_le_iff (NNReal.bddBelow_coe s) (Set.image_nonempty.mpr hs))]
  intro b hb
  rw [mem_lowerBounds] at hb
  by_cases hbnonneg : 0 ≤ b
  rw [(Real.coe_toNNReal b hbnonneg).symm, NNReal.coe_le_coe]
  apply le_csInf hs
  intro b1 hb1
  exact Real.toNNReal_le_iff_le_coe.mpr (hb b1.toReal (Set.mem_image_of_mem toReal hb1))
  push_neg at hbnonneg
  exact le_of_lt (lt_of_lt_of_le hbnonneg zero_le_coe)

lemma toReal_sInf_eq_sInf_toReal' {s : Set ℝ≥0∞} (hs : ∃ (r : ℝ≥0∞), r ∈ s ∧ r ≠ ⊤) :
    (sInf (s \ {⊤})).toReal = sInf (ENNReal.toReal '' (s \ {⊤})) := by
  obtain ⟨r, hr⟩ := hs
  apply le_antisymm
  have hble : ∀ (b : ℝ), b ∈ (ENNReal.toReal '' (s \ {⊤})) → (sInf (s \ {⊤})).toReal ≤ b := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    rw [← ha.2, ENNReal.toReal_le_toReal]
    exact sInf_le ha.1
    simp only [sInf_diff_singleton_top, ne_eq, sInf_eq_top, not_forall, exists_prop]
    use r
    exact (Set.mem_diff_singleton.mp ha.1).2
  apply (le_csInf_iff _ _).mpr hble
  use 0
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2]
  exact ENNReal.toReal_nonneg
  use r.toReal
  exact mem_image_of_mem ENNReal.toReal hr
  apply (csInf_le_iff _ _).mpr
  intro b hb
  rw [@mem_lowerBounds] at hb
  by_cases hbnonneg : 0 ≤ b
  rw [← ENNReal.toReal_ofReal hbnonneg, ENNReal.toReal_le_toReal]
  apply (le_csInf_iff _ _).mpr
  intro y hy
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr (Set.mem_diff_singleton.mp hy).2]
  simp only [toReal_nonneg, ofReal_le_ofReal_iff]
  exact (hb y.toReal) (Set.mem_image_of_mem ENNReal.toReal hy)
  exact OrderBot.bddBelow (s \ {⊤})
  exact nonempty_of_mem hr
  exact ofReal_ne_top
  simp only [sInf_diff_singleton_top, ne_eq, sInf_eq_top, not_forall, exists_prop]
  use r
  push_neg at hbnonneg
  exact le_of_lt (lt_of_lt_of_le hbnonneg zero_le_coe)
  use 0
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2]
  exact ENNReal.toReal_nonneg
  use r.toReal
  exact mem_image_of_mem ENNReal.toReal hr

lemma ex_in_add_pos_lt {s : Set ℝ≥0∞} (hsinf : sInf s < ⊤) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (a : ℝ≥0), ENNReal.ofNNReal a ∈ s ∧ a < ENNReal.toNNReal (sInf s) + ε := by
  have : ∃ (x : ℝ≥0∞), x ∈ s ∧ x ≠ ⊤ := by
    by_contra! h
    have : ⊤ ≤ sInf s := by
      apply le_sInf
      intro x hx
      exact eq_top_iff.mp (h x hx)
    exact LT.lt.false (lt_of_le_of_lt this hsinf)
  have : Set.Nonempty (ENNReal.toReal '' (s \ {⊤})) := by
    simp only [image_nonempty]
    obtain ⟨x, hx⟩ := this
    use x
    constructor
    · exact hx.1
    · exact not_mem_of_mem_diff hx
  obtain ⟨a, ha⟩ := Real.lt_sInf_add_pos this hε
  obtain ⟨b, hb⟩ := ha.1
  use b.toNNReal
  have hbnottop : b ≠ ⊤ := by
    exact (Set.mem_diff_singleton.mpr hb.1).2
  constructor
  · rw [ENNReal.coe_toNNReal (Set.mem_diff_singleton.mpr hb.1).2]
    exact ((Set.mem_diff b).mp hb.1).1
  · have : ∃ (r : ℝ≥0∞), r ∈ s ∧ r ≠ ⊤ := by
      use b
      constructor
      · exact ((Set.mem_diff b).mp hb.1).1
      · exact hbnottop
    rw [ENNReal.toNNReal_sInf' this, ← NNReal.coe_lt_coe]
    rw [← toReal_eq_toReal_toNNReal b, hb.2]
    simp
    rw [← ENNReal.toNNReal_sInf' this, ← toReal_eq_toReal_toNNReal (sInf s)]
    rw [← sInf_diff_singleton_eq_sInf (sInf_lt_iff.mp hsinf), toReal_sInf_eq_sInf_toReal']
    exact ha.2
    use b
    constructor
    · exact ((Set.mem_diff b).mp hb.1).1
    · exact hbnottop

lemma ex_in_add_pos_lt' {s : Set ℝ≥0∞} (hsinf : sInf s < ⊤) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (a : ℝ≥0), ENNReal.ofNNReal a ∈ s ∧ ENNReal.ofNNReal a < (sInf s) + ε := by
  obtain ⟨a, ha⟩ := ex_in_add_pos_lt hsinf ε hε
  use a
  have : sInf s ≠ ⊤ := by
    exact LT.lt.ne_top hsinf
  constructor
  · exact ha.1
  · rw [← ENNReal.coe_toNNReal this]
    rw [← ENNReal.coe_add, ENNReal.coe_lt_coe]
    exact ha.2



/-- The Riesz content can be approximated arbitrarily well from outside by open sets. -/
lemma exists_lt_rieszContent'_add_pos {E : Set X} {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ (V : Opens X), E ⊆ (V : Set X) ∧ rieszContent' Λ V ≤ rieszContent' Λ E + ε := by
  by_cases hinf : rieszContent' Λ E = ∞
  · use ⊤
    constructor
    exact le_top
    rw [hinf]
    exact sup_eq_left.mp rfl
  · obtain ⟨b, hb⟩ := ex_in_add_pos_lt' (Ne.lt_top hinf) ε εpos
    obtain ⟨V, hV⟩ := hb.1
    use V
    constructor
    exact Set.mem_setOf.mp hV.1
    rw [rieszContent'_eq_rieszContentAux'_open Λ V, hV.2]
    apply le_of_lt
    exact hb.2



open ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
 [T2Space X] [MeasurableSpace X] [BorelSpace X]


theorem RMK (Λ : C₀(X, ℂ) → ℂ) : Continuous Λ ∧ (∀ (f : C₀(X, ℂ)) (x : X), ((f x).re ≥ 0 ∧ (f x).im = 0) → ((Λ f).re ≥ 0 ∧ (Λ f).im = 0)) →
 ∃ (μ : MeasureTheory.Measure X), (∀ (f : C₀(X, ℂ)), ∫ (x : X), f x ∂μ = Λ f) := by
 sorry
