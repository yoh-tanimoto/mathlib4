-- import LeanCopilot
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Support
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousFunction.Bounded
-- import Mathlib.Topology.ContinuousFunction.CocompactMap
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UrysohnsLemma
-- import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Topology.Sets.Compacts
-- import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
-- import Mathlib.MeasureTheory.Integral.Bochner
-- import Mathlib.Data.Set.Intervals.Instances

noncomputable section

open BoundedContinuousFunction Set Function TopologicalSpace BigOperators
open Classical

variable {X : Type*} [TopologicalSpace X]

open Classical

-- there is prod_mem
lemma mem_prod_of_forall_mem {ι α : Type*} [CommMonoid α] {n : ℕ} (x : ι → α) {t : Set α} (ht1 : 1 ∈ t)
    (ht : ∀ (x y : α), x ∈ t → y ∈ t → x * y ∈ t) (s : Finset ι) (h : ∀ (i : ι), i ∈ s → x i ∈ t) :
    ∏ i in s, x i ∈ t := by
  induction s using Finset.cons_induction
  · simp only [Finset.prod_empty, mem_Icc, zero_le_one, le_refl, and_self]
    exact ht1
  · have : 0 < s.card := by
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
      exact hs.1 j (Finset.mem_of_subset Finset.sdiff_subset hj)
    exact ht (∏ i in s \ {a}, x i) (x a) (ih (s \ {a}) (And.intro hsdiffa this)) (hs.1 a ha)
  done

-- probably one can use prod_mem
lemma icc_prod_Icc {ι : Type*} (n : ℕ) (x : ι → ℝ) : ∀ (s : Finset ι),
    ((∀ (i : ι), i ∈ s → x i ∈ Icc 0 1) ∧ s.card = n) → ∏ i in s, x i ∈ Icc 0 1 := by
  have mul_mem': ∀ (x y : ℝ), x ∈ Icc 0 1 → y ∈ Icc 0 1 → x * y ∈ Icc 0 1 := by
    intro x y hx hy
    exact unitInterval.mul_mem hx hy
  exact mem_prod_of_forall_mem x (Set.right_mem_Icc.mpr (zero_le_one)) mul_mem'


lemma separation_of_isCompact_ne_mem {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    ∃ (U : Set X), ∃ (V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ t ⊆ V ∧ Disjoint U V := by
  obtain ⟨v, hv⟩ := Filter.disjoint_iff.mp ((IsCompact.disjoint_nhdsSet_left H1).mpr
    (fun (y : X) (p : y ∈ t) => disjoint_nhds_nhds.mpr (ne_of_mem_of_not_mem p H2)))
  obtain ⟨u, hu⟩ := hv.2
  obtain ⟨V, hV⟩ := mem_nhdsSet_iff_exists.mp hv.1
  obtain ⟨U, hU⟩ := mem_nhds_iff.mp hu.1
  use U
  use V
  constructor
  exact hU.2.1
  constructor
  exact hV.1
  constructor
  exact hU.2.2
  constructor
  exact hV.2.1
  exact Set.disjoint_of_subset hU.1 hV.2.2 (Disjoint.symm hu.2)

lemma separation_of_isCompact_ne_mem' {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    ∃ U ∈ nhds x,  ∃ V ∈ nhdsSet t, Disjoint U V := by
  obtain ⟨U, hU⟩ := separation_of_isCompact_ne_mem H1 H2
  obtain ⟨V, hV⟩ := hU
  use U
  constructor
  · rw [mem_nhds_iff]
    use U
    constructor
    exact subset_rfl
    constructor
    exact hV.1
    exact hV.2.2.1
  · use V
    constructor
    · apply (IsOpen.mem_nhdsSet hV.2.1).mpr hV.2.2.2.1
    · exact hV.2.2.2.2

lemma separation_of_isCompact_isCompact_disjoint {X : Type u_1} [TopologicalSpace X] [T2Space X]
    {s : Set X} {t : Set X} (H1 : IsCompact s) (H2 : IsCompact t) (H3 : Disjoint s t) :
    SeparatedNhds s t := by
  obtain ⟨u, hu⟩ := Filter.disjoint_iff.mp ((IsCompact.disjoint_nhdsSet_left H1).mpr
    (fun (x : X) (p : x ∈ s) => Filter.disjoint_iff.mpr (separation_of_isCompact_ne_mem' H2
    (Set.disjoint_left.mp H3 p))))
  obtain ⟨v, hv⟩ := hu.2
  obtain ⟨U, hU⟩ := mem_nhdsSet_iff_exists.mp hu.1
  obtain ⟨V, hV⟩ := mem_nhdsSet_iff_exists.mp hv.1
  use U
  use V
  constructor
  exact hU.1
  constructor
  exact hV.1
  constructor
  exact hU.2.1
  constructor
  exact hV.2.1
  exact Set.disjoint_of_subset hU.2.2 hV.2.2 hv.2

lemma compact_separation_of_isCompact_isCompact_disjoint {X : Type u_1} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] {s : Set X} {t : Set X}
    (H1 : IsCompact s) (H2 : IsCompact t) (H3 : Disjoint s t) :
    ∃ (k : Set X), IsCompact k ∧ s ⊆ interior k ∧ k ⊆ tᶜ := by
  obtain ⟨U, hU⟩ := separation_of_isCompact_isCompact_disjoint H1 H2 H3
  obtain ⟨V, hV⟩ := hU
  obtain ⟨K, hK⟩ := exists_compact_between H1 isOpen_univ (Set.subset_univ s)
  use (closure U) ∩ K
  constructor
  · exact IsCompact.of_isClosed_subset hK.1
      (IsClosed.inter isClosed_closure (IsCompact.isClosed hK.1))
      (Set.inter_subset_right (closure U) K)
  constructor
  · rw [subset_interior_iff]
    use U ∩ (interior K)
    constructor
    · exact IsOpen.inter hV.1 isOpen_interior
    constructor
    · exact Set.subset_inter_iff.mpr (And.intro hV.2.2.1 hK.2.1)
    · intro x hx
      constructor
      · exact Set.mem_of_subset_of_mem subset_closure hx.1
      · exact Set.mem_of_subset_of_mem interior_subset hx.2
  apply Set.Subset.trans _ (Set.compl_subset_compl.mpr hV.2.2.2.1)
  rw [← Set.subset_compl_iff_disjoint_right] at hV
  apply Set.Subset.trans (Set.inter_subset_left (closure U) K)
  rw [← closure_eq_iff_isClosed.mpr (isClosed_compl_iff.mpr hV.2.1)]
  exact closure_mono hV.2.2.2.2

lemma locallyCompact_t2_separation [LocallyCompactSpace X] [T2Space X]  {s : Set X} {t : Set X}
    (H1 : IsOpen s) (H2 : IsCompact (closure s)) (H3 : IsClosed t) (H4 : t ⊆ s) :
    SeparatedNhds sᶜ t := by
-- separation of (closure s) \ s and t
  obtain ⟨U, hU⟩ := separation_of_isCompact_isCompact_disjoint
    (IsCompact.of_isClosed_subset H2 (IsClosed.sdiff isClosed_closure H1)
    (Set.diff_subset (closure s) s))
    (IsCompact.of_isClosed_subset H2 H3 (Set.Subset.trans H4 subset_closure))
    (Set.disjoint_of_subset_right H4 Set.disjoint_sdiff_left)
  obtain ⟨V, hV⟩ := hU
  use U ∪ (closure s)ᶜ
  use V ∩ s
  constructor
  exact IsOpen.union hV.1 (isOpen_compl_iff.mpr isClosed_closure)
  constructor
  exact IsOpen.inter hV.2.1 H1
  constructor
  rw [Set.diff_eq_compl_inter] at hV
  intro x hx
  by_cases hxs : x ∈ (closure s)ᶜ
  · right
    exact hxs
  · left
    push_neg at hxs
    simp only [mem_compl_iff, not_not] at hxs
    exact Set.mem_of_subset_of_mem hV.2.2.1 (Set.mem_inter hx hxs)
  constructor
  exact Set.subset_inter_iff.mpr (And.intro hV.2.2.2.1 H4)
  rw [Set.disjoint_union_left]
  constructor
  exact Set.disjoint_of_subset_right (Set.inter_subset_left V s) hV.2.2.2.2
  rw [← interior_compl]
  exact Set.disjoint_of_subset interior_subset (Set.inter_subset_right V s) disjoint_compl_left

/-- Urysohn's lemma. In a `LocallyCompactSpace T2Space X`, for disjoint compact sets `s t`, there is a continuous
function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
lemma exists_tsupport_zero_one_of_isCompact_isCompact [T2Space X]
    {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) : ∃ f : C(X, ℝ),
    EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨k, k_comp, sk, kt⟩ : ∃ k, IsCompact k ∧ s ⊆ interior k ∧ k ⊆ tᶜ :=
    compact_separation_of_isCompact_isCompact_disjoint hs ht hst
  let P : Set X → Prop := IsCompact
  set c : Urysohns.CU P :=
  { C := k
    U := tᶜ
    P_C := k_comp
    closed_C := k_comp.isClosed
    open_U := ht.isClosed.isOpen_compl
    subset := kt
    hP := by
      rintro c u - c_comp u_open cu
      rcases exists_compact_closed_between c_comp u_open cu with ⟨k, k_comp, k_closed, ck, ku⟩
      have A : closure (interior k) ⊆ k :=
        (IsClosed.closure_subset_iff k_closed).2 interior_subset
      refine ⟨interior k, isOpen_interior, ck, A.trans ku,
        k_comp.of_isClosed_subset isClosed_closure A⟩ }
  exact ⟨⟨c.lim, c.continuous_lim⟩, fun x hx ↦ c.lim_of_mem_C _ (sk.trans interior_subset hx),
    fun x hx => c.lim_of_nmem_U _ fun h => h hx, c.lim_mem_Icc⟩


/-- A variation of Urysohn's lemma. In a `LocallyCompactSpace T2Space X`, for a closed set `t` and
an open set `s` such that `t ⊆ s`, there is a continuous function `f` supported in `s`, `f x = 1`
on `t` and `0 ≤ f x ≤ 1`. -/
lemma exists_tsupport_one_of_isOpen_isClosed [LocallyCompactSpace X] [T2Space X] {s t : Set X}
    (hs : IsOpen s) (hscp : IsCompact (closure s)) (ht : IsClosed t) (hst : t ⊆ s) : ∃ f : C(X, ℝ),
    tsupport f ⊆ s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨u, v, huv⟩ := locallyCompact_t2_separation hs hscp ht hst
  have hDisjoint : Disjoint (closure u) t := by
    apply le_compl_iff_disjoint_right.mp
    apply _root_.subset_trans _ (Set.compl_subset_compl.mpr huv.2.2.2.1)
    apply (IsClosed.closure_subset_iff (IsOpen.isClosed_compl huv.2.1)).mpr
    exact Set.subset_compl_iff_disjoint_right.mpr huv.2.2.2.2
  rw [← Set.subset_compl_iff_disjoint_right] at huv
  have huvc : closure u ⊆ vᶜ := by
    rw [← IsClosed.closure_eq (isClosed_compl_iff.mpr huv.2.1)]
    exact closure_mono huv.2.2.2.2
  let P : Set X → Prop := fun C => sᶜ ⊆ C
  set c : Urysohns.CU P :=
  { C := closure u
    U := tᶜ
    P_C := Set.Subset.trans huv.2.2.1 subset_closure
    closed_C := isClosed_closure
    open_U := ht.isOpen_compl
    subset := Set.subset_compl_comm.mp (Set.Subset.trans huv.2.2.2.1 (Set.subset_compl_comm.mp huvc))
    hP := by
      intro c u cIsClosed Pc uIsOpen csubu
      obtain ⟨u1, hu1⟩ := locallyCompact_t2_separation (isOpen_compl_iff.mpr cIsClosed)
        (IsCompact.of_isClosed_subset hscp isClosed_closure
        (closure_mono (Set.compl_subset_comm.mp Pc)))
        (isClosed_compl_iff.mpr uIsOpen) (Set.compl_subset_compl_of_subset csubu)
      obtain ⟨v1, hv1⟩ := hu1
      use u1
      simp only [compl_compl] at hv1
      rw [← Set.subset_compl_iff_disjoint_right] at hv1
      constructor
      · exact hv1.1
      constructor
      · exact hv1.2.2.1
      constructor
      · apply Set.Subset.trans _ (Set.compl_subset_comm.mp hv1.2.2.2.1)
        rw [← IsClosed.closure_eq (isClosed_compl_iff.mpr hv1.2.1)]
        exact closure_mono hv1.2.2.2.2
      · exact Set.Subset.trans (Set.Subset.trans Pc hv1.2.2.1) subset_closure
  }
  use ⟨c.lim, c.continuous_lim⟩
  simp only [ContinuousMap.coe_mk]
  constructor
  · apply Set.Subset.trans _ (Set.compl_subset_comm.mp huv.2.2.1)
    rw [← IsClosed.closure_eq (isClosed_compl_iff.mpr huv.1)]
    apply closure_mono
    intro x hx
    simp only [mem_support, ne_eq] at hx
    push_neg at hx
    simp only [mem_compl_iff]
    apply Not.intro
    intro hxu
    apply Ne.elim hx
    exact Urysohns.CU.lim_of_mem_C c x (Set.mem_of_subset_of_mem subset_closure hxu)
  constructor
  · intro x hx
    apply Urysohns.CU.lim_of_nmem_U
    exact Set.not_mem_compl_iff.mpr hx
  · exact Urysohns.CU.lim_mem_Icc c

open Classical

-- todo/-- A variation of Urysohn's lemma. In a normal T2 space `X`, for a compact set `t` and a finite
family of open sets `{s i}_i` such that `t ⊆ ⋃ i, s i`, there is a family of compactly supported
continuous functions `{f i}_i` supported in `s i`, `∑ i, f i x = 1` on `t` and `0 ≤ f i x ≤ 1`. -/
lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClose [T2Space X] [LocallyCompactSpace X]
    {n : ℕ} {t : Set X} {s : Fin n → Set X} (hs : ∀ (i : Fin n), IsOpen (s i)) (htcp : IsCompact t)
    (hst : t ⊆ ⋃ i, s i) : ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧
    EqOn (∑ i, f i) 1 t ∧ (∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1) ∧ (∀ (i : Fin n),
    HasCompactSupport (f i)) := by
  have : ∃ sc : Fin n → Set X, (∀ (i : Fin n), IsOpen (sc i)) ∧ (∀ (i : Fin n), IsCompact
    (closure (sc i))) ∧ t ⊆ ⋃ i, sc i ∧ (∀ (i : Fin n), sc i ⊆ s i):= by
    set sc := fun (i : Fin n) => Classical.choose (exists_isOpen_superset_and_isCompact_closure
      htcp) ∩ s i
    set spsc := Classical.choose_spec (exists_isOpen_superset_and_isCompact_closure htcp)
    use sc
    refine ⟨fun i => IsOpen.inter spsc.1 (hs i), ?_, ?_, ?_⟩
    · intro i
      apply IsCompact.of_isClosed_subset spsc.2.2 isClosed_closure
      exact closure_mono inter_subset_left
    · rw [← inter_iUnion _ s]
      exact subset_inter spsc.2.1 hst
    · exact fun i => inter_subset_right
  obtain ⟨sc, hscopen, hscccompact, htsubsc, hssubsc⟩ := this
  rcases n with _ | n
  · simp only [Nat.zero_eq, Finset.univ_eq_empty, Finset.sum_empty, mem_Icc, IsEmpty.forall_iff,
    and_true, exists_const]
    have : t = ∅ := by
      rw [Set.iUnion_of_empty s] at hst
      exact subset_eq_empty hst rfl
    refine ⟨trivial, ?_⟩
    intro x
    rw [this]
    exact fun a => a.elim
  · have htW : ∀ (x : X), x ∈ t → ∃ (Wx : Set X), x ∈ Wx ∧ IsOpen Wx ∧ IsCompact (closure Wx)
        ∧ ∃ (i : Fin (Nat.succ n)), (closure Wx) ⊆ sc i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((Set.mem_of_subset_of_mem htsubsc) hx)
      obtain ⟨cWx, hcWxCompact, hxinintcWx, hcWxsubsi⟩ := exists_compact_subset (hscopen i) hi
      use interior cWx
      refine ⟨hxinintcWx, ?_, ?_, ?_⟩
      · simp only [isOpen_interior]
      · apply IsCompact.of_isClosed_subset hcWxCompact isClosed_closure
        nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcWxCompact)]
        exact closure_mono interior_subset
      · use i
        apply _root_.subset_trans _ hcWxsubsi
        nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcWxCompact)]
        exact closure_mono interior_subset
    set W : X → Set X := fun x => if hx : x ∈ t then Classical.choose (htW x hx) else default
      with hW
    have htWnhds : ∀ (x : X), x ∈ t → W x ∈ nhds x := by
      intro x hx
      apply mem_nhds_iff.mpr
      use W x
      refine ⟨subset_refl (W x), ?_⟩
      rw [hW]
      simp only
      rw [dif_pos hx]
      exact And.intro (Classical.choose_spec (htW x hx)).2.1 (Classical.choose_spec (htW x hx)).1
    obtain ⟨ι, hι⟩ := IsCompact.elim_nhds_subcover htcp W htWnhds
    set Wx : Fin (Nat.succ n) → ι → Set X := fun i xj =>
      if closure (W xj) ⊆ sc i then closure (W xj) else ∅
      with hWx
    set H : Fin (Nat.succ n) → Set X := fun i => ⋃ xj, closure (Wx i xj)
      with hH
    have IsClosedH : ∀ (i : Fin (Nat.succ n)), IsClosed (H i) := by
      intro i
      rw [hH]
      simp only
      exact isClosed_iUnion_of_finite (fun (xj : ι) => isClosed_closure)
    have IsHSubS : ∀ (i : Fin (Nat.succ n)), H i ⊆ sc i := by
      intro i
      rw [hH]
      simp only
      apply Set.iUnion_subset
      intro xj
      rw [hWx]
      simp only
      by_cases hmV : closure (W xj) ⊆ sc i
      · rw [if_pos hmV, closure_closure]
        exact hmV
      · rw [if_neg hmV, closure_empty]
        exact Set.empty_subset _
    set g : Fin (Nat.succ n) → C(X, ℝ) := fun i => Classical.choose
      (exists_tsupport_one_of_isOpen_isClosed (hscopen i) (hscccompact i) (IsClosedH i) (IsHSubS i))
      with hg
    set f : Fin (Nat.succ n) → C(X, ℝ) :=
      fun i => (∏ j in { j : Fin (Nat.succ n) | j < i }.toFinset, (1 - g j)) * g i
      with hf
    use f
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      apply _root_.subset_trans tsupport_mul_subset_right
      apply subset_trans _ (hssubsc i)
      exact (Classical.choose_spec
        (exists_tsupport_one_of_isOpen_isClosed (hscopen i) (hscccompact i) (IsClosedH i)
        (IsHSubS i))).1
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
          have hxlem : Finset.filter (fun (x : Fin (Nat.succ n)) =>
              x < { val := 1+m, isLt := honeaddm })
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
            simp only [Fin.val_natCast]
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
        apply funext_iff.mp
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
        (hscopen i) (hscccompact i) (IsClosedH i) (IsHSubS i))).2.1 hxHi]
      simp only [Pi.one_apply, sub_self]
    · intro i x
      rw [hf]
      simp only [mem_setOf_eq, toFinset_setOf, ContinuousMap.mul_apply, ContinuousMap.coe_prod,
        ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply]
      apply unitInterval.mul_mem
      · apply unitInterval.prod_mem
        intro c _
        simp only [Pi.sub_apply, Pi.one_apply]
        rw [hg, ← unitInterval.mem_iff_one_sub_mem]
        exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed (hscopen c)
          (hscccompact c) (IsClosedH c) (IsHSubS c))).2.2 x
      · rw [hg]
        simp only
        exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed (hscopen i)
          (hscccompact i) (IsClosedH i) (IsHSubS i))).2.2 x
    · intro i
      apply IsCompact.of_isClosed_subset (hscccompact i) (isClosed_closure)
      apply closure_mono
      apply _root_.subset_trans (Function.support_mul_subset_right _ _)
      exact subset_trans subset_closure (Classical.choose_spec
        (exists_tsupport_one_of_isOpen_isClosed (hscopen i) (hscccompact i) (IsClosedH i)
        (IsHSubS i))).1
