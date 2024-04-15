import LeanCopilot
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
open Classical

variable {X : Type*} [TopologicalSpace X]

lemma icc_mul_Icc {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) : x * y ∈ Icc 0 1 := by
  simp only [mem_Icc]
  simp only [mem_Icc] at hx
  simp only [mem_Icc] at hy
  constructor
  · exact mul_nonneg hx.1 hy.1
  · rw [← mul_one 1]
    exact mul_le_mul hx.2 hy.2 hy.1 zero_le_one

open Classical

lemma icc_prod_Icc {ι : Type*} (n : ℕ) (x : ι → ℝ) : ∀ (s : Finset ι),
    ((∀ (i : ι), i ∈ s → x i ∈ Icc 0 1) ∧ s.card = n) → ∏ i in s, x i ∈ Icc 0 1 := by
  induction' n with n ih
  · intro s hs
    rw [Finset.card_eq_zero.mp hs.2]
    simp only [Finset.prod_empty, mem_Icc, zero_le_one, le_refl, and_self]
  · intro s hs
    have : 0 < s.card := by
      rw [hs.2]
      exact Nat.succ_pos n
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    have : (s \ {a}).card = n := by
      rw [Finset.card_sdiff]
      simp only [Finset.card_singleton]
      rw [hs.2]
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      simp only [Finset.singleton_subset_iff]
      exact ha
    have hUnion : s = (s \ {a}) ∪ {a} := by
      apply Eq.symm
      apply Finset.sdiff_union_of_subset
      simp only [Finset.singleton_subset_iff]
      exact ha
    have hDisjoint : Disjoint (s \ {a}) {a} := by
      simp only [Finset.disjoint_singleton_right, Finset.mem_sdiff, Finset.mem_singleton,
        not_true_eq_false, and_false, not_false_eq_true]
    rw [hUnion, Finset.prod_union hDisjoint, Finset.prod_singleton _ _]
    have hsdiffa : ∀ (i : ι), i ∈ s \ {a} → x i ∈ Icc 0 1 := by
      intro j hj
      exact hs.1 j (Finset.mem_of_subset (Finset.sdiff_subset s {a}) hj)
    exact icc_mul_Icc (ih (s \ {a}) (And.intro hsdiffa this)) (hs.1 a ha)


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
  · have htW : ∀ (x : X), x ∈ t → ∃ (Wx : Set X), x ∈ Wx ∧ IsOpen Wx ∧ IsCompact (closure Wx)
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
    set W : X → Set X := fun x => if hx : x ∈ t then Classical.choose (htW x hx) else default with hW
    have htWnhds : ∀ (x : X), x ∈ t → W x ∈ nhds x := by
      intro x hx
      apply mem_nhds_iff.mpr
      use W x
      constructor
      · exact fun ⦃a⦄ a => a
      · rw [hW]
        simp only
        rw [dif_pos hx]
        exact And.intro (Classical.choose_spec (htW x hx)).2.1 (Classical.choose_spec (htW x hx)).1
    obtain ⟨ι, hι⟩ := IsCompact.elim_nhds_subcover htcp W htWnhds
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
    · have hsumf(m : ℕ) (hm : m < n+2) : ∑ j in { j : Fin (n+2) | j ≤ ⟨m, hm⟩ }.toFinset, f j
          = 1 - (∏ j in { j : Fin (n+2) | j ≤ ⟨m, hm⟩ }.toFinset, (1 - g j)) := by
        induction' m with m ihm
        · simp only [Nat.zero_eq, Fin.zero_eta, Fin.le_zero_iff, setOf_eq_eq_singleton,
          toFinset_singleton, Finset.sum_singleton, Finset.prod_singleton, sub_sub_cancel]
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
          simp only [mem_setOf_eq, toFinset_setOf] at ihm
          rw [ihm hmlt]
          rw [sub_mul, one_mul, hf]
          ring_nf
          simp only [mem_setOf_eq, toFinset_setOf]
          have : 1+m < n+2 := by
            rw [add_comm 1 m]
            exact hm
          have : Finset.filter (fun (x : Fin (n+2)) => x < { val := 1+m, isLt := this }) = Finset.filter (fun (x : Fin (n+2)) => x ≤ { val := m, isLt := hmlt }) := by
            ext Finset.univ a
            simp only [Finset.mem_filter, and_congr_right_iff]
            intro hauniv
            constructor
            · intro ha
              rw [Fin.le_def]
              rw [Fin.lt_def] at ha
              simp only at ha
              simp only
              rw [add_comm 1 m] at ha
              exact Nat.le_of_lt_succ ha
            · intro ha
              rw [Fin.le_def] at ha
              rw [Fin.lt_def]
              simp only at ha
              simp only
              rw [add_comm 1 m]
              exact Nat.lt_succ_of_le ha
          rw [this]
          ring
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
          rw [Fin.lt_def]
          simp only [Fin.val_nat_cast]
          exact lt_add_one m -- same proof repeated
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
          rw [Fin.lt_def]
          simp only [Fin.val_nat_cast]
          exact lt_add_one m
      intro x hx
      have huniv : {j : Fin (n+2) | j ≤ ⟨n+1, (lt_add_one (n+1))⟩ }.toFinset = Finset.univ := by
        ext j
        constructor
        · intro _
          simp only [Finset.mem_univ]
        · intro _
          simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
            true_and]
          apply Fin.mk_le_of_le_val
          simp only
          exact Nat.lt_succ_iff.mp j.isLt
      rw [← huniv]
      have heqfun (x : X) : (∑ j in { j : Fin (n+2) | j ≤ ⟨n+1, (lt_add_one (n+1))⟩ }.toFinset, f j) x
          = (1 - (∏ j in { j : Fin (n+2) | j ≤ ⟨n+1, (lt_add_one (n+1))⟩ }.toFinset, (1 - g j))) x := by
        apply Function.funext_iff.mp
        sorry --exact (hsumf (n+1) (lt_add_one (n+1)))
      simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.coe_prod,
        ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply, Pi.sub_apply,
        Pi.one_apply] at heqfun
      simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.sum_apply, Pi.one_apply]
      rw [heqfun]
      simp only [sub_eq_self]
      obtain ⟨xj, hxj⟩ := exists_exists_eq_and.mp (hι.2 hx)
      simp only [mem_iUnion, exists_prop] at hxj
      rw [hW] at hxj
      simp at hxj
      rw [dif_pos (hι.1 xj hxj.1)] at hxj
      obtain ⟨i, hi⟩ := (Classical.choose_spec (htW xj (hι.1 xj hxj.1))).2.2.2
      have hxHi : x ∈ H i := by
        rw [hH]
        simp only [mem_iUnion]
        use ⟨xj, hxj.1⟩
        rw [hWx]
        simp only [dite_eq_ite]
        rw [hW]
        simp only
        rw [dif_pos (hι.1 xj hxj.1)]
        apply Set.mem_of_mem_of_subset _ subset_closure
        rw [dif_pos hi] --why?

      simp at huniv
      rw [huniv]

      -- use hW
      sorry
    · sorry
