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
import Mathlib.Data.Set.Intervals.Instances

noncomputable section

open BoundedContinuousFunction Set Function TopologicalSpace BigOperators
open Classical

variable {X : Type*} [TopologicalSpace X]

open Classical

-- there is prod_mem
lemma mem_prod_of_forall_mem {ι α : Type*} [CommMonoid α] {n : ℕ} (x : ι → α) {t : Set α} (ht1 : 1 ∈ t)
    (ht : ∀ (x y : α), x ∈ t → y ∈ t → x * y ∈ t) :
    ∀ (s : Finset ι), ((∀ (i : ι), i ∈ s → x i ∈ t)) ∧ s.card = n → ∏ i in s, x i ∈ t := by
  induction' n with n ih
  · intro s hs
    rw [Finset.card_eq_zero.mp hs.2]
    simp only [Finset.prod_empty, mem_Icc, zero_le_one, le_refl, and_self]
    exact ht1
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
    have hsdiffa : ∀ (i : ι), i ∈ s \ {a} → x i ∈ t := by
      intro j hj
      exact hs.1 j (Finset.mem_of_subset (Finset.sdiff_subset s {a}) hj)
    exact ht (∏ i in s \ {a}, x i) (x a) (ih (s \ {a}) (And.intro hsdiffa this)) (hs.1 a ha)
  done

-- probably one can use prod_mem
lemma icc_prod_Icc {ι : Type*} (n : ℕ) (x : ι → ℝ) : ∀ (s : Finset ι),
    ((∀ (i : ι), i ∈ s → x i ∈ Icc 0 1) ∧ s.card = n) → ∏ i in s, x i ∈ Icc 0 1 := by
  have mul_mem': ∀ (x y : ℝ), x ∈ Icc 0 1 → y ∈ Icc 0 1 → x * y ∈ Icc 0 1 := by
    intro x y hx hy
    exact unitInterval.mul_mem hx hy
  exact mem_prod_of_forall_mem x (Set.right_mem_Icc.mpr (zero_le_one)) mul_mem'


/-- A variation of Urysohn's lemma. In a normal space `X`, for a closed set `t` and an open set `s`
such that `t ⊆ s`, there is a continuous function `f` supported in `s`, `f x = 1` on `t` and
`0 ≤ f x ≤ 1`. -/
lemma exists_tsupport_one_of_isOpen_isClosed [NormalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsClosed t) (hst : t ⊆ s) : ∃ f : C(X, ℝ), tsupport f ⊆ s ∧ EqOn f 1 t
    ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨U, V, hUV⟩ := normal_separation (IsOpen.isClosed_compl hs) ht
      (HasSubset.Subset.disjoint_compl_left hst)
    have hDisjoint : Disjoint (closure U) t := by
      apply le_compl_iff_disjoint_right.mp
      apply _root_.subset_trans _ (Set.compl_subset_compl.mpr hUV.2.2.2.1)
      apply (IsClosed.closure_subset_iff (IsOpen.isClosed_compl hUV.2.1)).mpr
      exact Set.subset_compl_iff_disjoint_right.mpr hUV.2.2.2.2
    obtain ⟨f, hf⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure ht hDisjoint
    use f
    constructor
    · apply _root_.subset_trans _ (Set.compl_subset_comm.mp hUV.2.2.1)
      rw [← IsClosed.closure_eq (IsOpen.isClosed_compl hUV.1)]
      apply closure_mono
      rw [Set.subset_compl_iff_disjoint_left, Function.disjoint_support_iff]
      exact Set.EqOn.mono subset_closure hf.1
    · exact hf.2

open Classical

/-- A variation of Urysohn's lemma. In a normal T2 space `X`, for a compact set `t` and a finite
family of open sets `{s i}` such that `t ⊆ ⋃ i, s i`, there is a family of continuous function
`{f i}` supported in `s i`, `∑ i, f i x = 1` on `t` and `0 ≤ f x ≤ 1`. -/
lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed [NormalSpace X] [T2Space X]
    [LocallyCompactSpace X] {n : ℕ} {t : Set X} {s : Fin n → Set X}
    (hs : ∀ (i : Fin n), IsOpen (s i))
    (htcp : IsCompact t) (hst : t ⊆ ⋃ i, s i) :
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
  · have htW : ∀ (x : X), x ∈ t → ∃ (Wx : Set X), x ∈ Wx ∧ IsOpen Wx ∧ IsCompact (closure Wx)
        ∧ ∃ (i : Fin (Nat.succ n)), (closure Wx) ⊆ s i := by
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
    set W : X → Set X := fun x => if hx : x ∈ t then Classical.choose (htW x hx) else default
      with hW
    have htWnhds : ∀ (x : X), x ∈ t → W x ∈ nhds x := by
      intro x hx
      apply mem_nhds_iff.mpr
      use W x
      constructor
      · exact subset_refl (W x)
      · rw [hW]
        simp only
        rw [dif_pos hx]
        exact And.intro (Classical.choose_spec (htW x hx)).2.1 (Classical.choose_spec (htW x hx)).1
    obtain ⟨ι, hι⟩ := IsCompact.elim_nhds_subcover htcp W htWnhds
    set Wx : Fin (Nat.succ n) → ι → Set X := fun i xj =>
      if closure (W xj) ⊆ s i then closure (W xj) else ∅
      with hWx
    set H : Fin (Nat.succ n) → Set X := fun i => ⋃ xj, closure (Wx i xj)
      with hH
    have IsClosedH : ∀ (i : Fin (Nat.succ n)), IsClosed (H i) := by
      intro i
      rw [hH]
      simp only
      exact isClosed_iUnion_of_finite (fun (xj : ι) => isClosed_closure)
    have IsHSubS : ∀ (i : Fin (Nat.succ n)), H i ⊆ s i := by
      intro i
      rw [hH]
      simp only
      apply Set.iUnion_subset
      intro xj
      rw [hWx]
      simp only
      by_cases hmV : closure (W xj) ⊆ s i
      · rw [if_pos hmV, closure_closure]
        exact hmV
      · rw [if_neg hmV, closure_empty]
        exact Set.empty_subset _
    set g : Fin (Nat.succ n) → C(X, ℝ) := fun i => Classical.choose
      (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))
      with hg
    set f : Fin (Nat.succ n) → C(X, ℝ) :=
      fun i => (∏ j in { j : Fin (Nat.succ n) | j < i }.toFinset, (1 - g j)) * g i
      with hf
    use f
    constructor
    · rw [hf]
      simp only
      intro i
      apply _root_.subset_trans tsupport_mul_subset_right
      exact (Classical.choose_spec
        (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))).1
    constructor
    · have hsumf (m : ℕ) (hm : m < Nat.succ n) :
          ∑ j in { j : Fin (Nat.succ n) | j ≤ ⟨m, hm⟩ }.toFinset, f j
          = 1 - (∏ j in { j : Fin (Nat.succ n) | j ≤ ⟨m, hm⟩ }.toFinset, (1 - g j)) := by
        induction' m with m ihm
        · simp only [Nat.zero_eq, Fin.zero_eta, Fin.le_zero_iff, setOf_eq_eq_singleton,
          toFinset_singleton, Finset.sum_singleton, Finset.prod_singleton, sub_sub_cancel]
          rw [hf]
          simp only [Fin.not_lt_zero, setOf_false, toFinset_empty, Finset.prod_empty, one_mul]
        · have hmlt : m < Nat.succ n := by
            exact Nat.lt_of_succ_lt hm
          have hUnion: { j : Fin (Nat.succ n) | j ≤ ⟨m + 1, hm⟩}
              = { j : Fin (Nat.succ n) | j ≤ ⟨m, hmlt⟩ } ∪ {⟨m+1, hm⟩} := by
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
          rw [Finset.sum_insert _, Finset.prod_insert _]
          simp only [mem_setOf_eq, toFinset_setOf] at ihm
          rw [ihm hmlt, sub_mul, one_mul, hf]
          ring_nf
          simp only [mem_setOf_eq, toFinset_setOf]
          have honeaddm: 1+m < Nat.succ n := by
            rw [add_comm 1 m]
            exact hm
          have hxlem : Finset.filter (fun (x : Fin (Nat.succ n)) => x < { val := 1+m, isLt := honeaddm })
              = Finset.filter (fun (x : Fin (Nat.succ n)) => x ≤ { val := m, isLt := hmlt }) := by
            ext Finset.univ a
            simp only [Finset.mem_filter, and_congr_right_iff]
            intro _
            rw [Fin.le_def, Fin.lt_def]
            simp only
            rw [add_comm 1 m]
            exact Nat.lt_add_one_iff
          rw [hxlem]
          ring
          all_goals
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
            rw [Fin.lt_def]
            simp only [Fin.val_nat_cast]
            exact lt_add_one m
      intro x hx
      have huniv : {j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset = Finset.univ := by
        ext j
        simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
          true_and, iff_true]
        apply Fin.mk_le_of_le_val
        simp only
        exact Nat.lt_succ_iff.mp j.isLt
      rw [← huniv]
      have heqfun (x : X) :
          (∑ j in { j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset, f j) x
          = (1 - (∏ j in { j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset, (1 - g j)))
          x := by
        apply Function.funext_iff.mp
        ext z
        exact congrFun (congrArg DFunLike.coe (hsumf n (lt_add_one n))) z
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
        simp only [mem_ite_empty_right]
        exact And.intro hi (Set.mem_of_mem_of_subset hxj.2 subset_closure)
      simp at huniv
      rw [huniv]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hg]
      simp only [mem_Icc]
      rw [(Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed
        (hs i) (IsClosedH i) (IsHSubS i))).2.1 hxHi]
      simp only [Pi.one_apply, sub_self]
    · intro i x
      rw [hf]
      simp only [mem_setOf_eq, toFinset_setOf, ContinuousMap.mul_apply, ContinuousMap.coe_prod,
        ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply]
      apply unitInterval.mul_mem
      · apply icc_prod_Icc i.val
        constructor
        · rw [hg]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_nonneg,
            tsub_le_iff_right, le_add_iff_nonneg_right]
          intro j _
          apply Set.Icc.one_sub_mem
          exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed
            (hs j) (IsClosedH j) (IsHSubS j))).2.2 x
        · have hFinIcc: Finset.filter (fun x => x < i) Finset.univ = Finset.Ico 0 i := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico, Fin.zero_le]
          rw [hFinIcc]
          simp only [Fin.card_Ico, Fin.val_zero, tsub_zero]
      · rw [hg]
        simp only
        exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))).2.2 x
