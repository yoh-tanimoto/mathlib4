-- import LeanCopilot
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

noncomputable section

open BoundedContinuousFunction Set Function TopologicalSpace BigOperators

variable {X : Type*} [TopologicalSpace X]

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
  induction' n with n ihn
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
    set f : Fin (n+2) → C(X, ℝ) := fun i => (∏ j in { j : Fin (n+2) | j < i }.toFinset, (1 - g j)) * g i with hf
    use f
    constructor
    · rw [hf]
      simp only
      intro i
      apply _root_.subset_trans tsupport_mul_subset_right
      exact (Classical.choose_spec
        (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))).1
    constructor
    · have (m : ℕ) (hm : m < n+2) : ∑ j in { j : Fin (n+2) | j ≤ ⟨m, hm⟩ }.toFinset, f j
          = 1 - (∏ j in { j : Fin (n+2) | j ≤ ⟨m, hm⟩ }.toFinset, (1 - g j)) := by
        induction' m with m ihm
        · simp only [Nat.zero_eq, Nat.cast_zero, Fin.le_zero_iff, setOf_eq_eq_singleton,
            toFinset_singleton, Finset.sum_singleton, Finset.prod_singleton, _root_.sub_sub_cancel]
          rw [hf]
          simp only [Fin.not_lt_zero, setOf_false, toFinset_empty, Finset.prod_empty, one_mul]
        · have hmlt : m < n + 2 := by
            exact Nat.lt_of_succ_lt hm
          have hUnion: { j : Fin (n+2) | j ≤ ⟨m + 1, hm⟩} = { j : Fin (n+2) | j ≤ ⟨m, hmlt⟩ } ∪ {⟨m+1, hm⟩} := by
            simp only [union_singleton]
            ext j
            simp only [Nat.cast_add, Nat.cast_one, mem_setOf_eq, mem_insert_iff]
            constructor
            · intro hj
              by_cases hjm : j.1 ≤ m
              · right
                exact hjm
              · push_neg at hjm
                left
                rw [Fin.ext_iff]
                simp only
                rw [Fin.le_def] at hj
                exact (Nat.le_antisymm hjm hj).symm
            · intro hj
              rcases hj with hjmone | hjmle
              · exact le_of_eq hjmone
              · rw [Fin.le_def]
                simp only
                rw [Fin.le_def] at hjmle
                simp only at hjmle
                rw [Nat.le_add_one_iff]
                left
                exact hjmle
          simp_rw [hUnion]
          simp only [union_singleton, toFinset_insert, mem_setOf_eq, toFinset_setOf]
          rw [Finset.sum_insert _] -- same premise
          rw [Finset.prod_insert _]
          sorry
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
          rw [Fin.lt_def]
          simp only [Fin.val_nat_cast]
          exact lt_add_one m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
          rw [Fin.lt_def]
          simp only [Fin.val_nat_cast]
          exact lt_add_one m
      intro x hx
      simp
      rw [hf]
      sorry
    · sorry


  -- use exists_compact_subset
