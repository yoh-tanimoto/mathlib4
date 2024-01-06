/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Int.Card
import Mathlib.Order.Partition.Equipartition
import Mathlib.Tactic.Linarith

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations show
that the graph is (isomorphic to) the Turán graph for the given parameters.

The reverse direction...

## Main declarations

* `G.IsTuranMaximal r`: predicate saying that `G` has the most number of edges for its number `n`
  of vertices while still being `r + 1`-cliquefree.
* `turanGraph n r`: the canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `isTuranMaximalIsoTuranGraph`: isomorphism between `G` with `G.IsTuranMaximal r` and
  `turanGraph n r`.
-/


open Finset

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {s t u : V}

/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

/-- First part of Zykov symmetrisation. If vertex `s` has larger degree than
a non-adjacent other vertex `t`, `G.replaceVertex s t` has more edges than `G`. -/
theorem card_lt_card_replaceVertex1 (hn : ¬G.Adj s t) (hd : G.degree t < G.degree s) :
    G.edgeFinset.card < (G.replaceVertex s t).edgeFinset.card := by
  rw [G.card_edgeFinset_replaceVertex_of_not_adj hn, add_tsub_assoc_of_le hd.le]
  exact Nat.lt_add_of_pos_right <| tsub_pos_iff_lt.mpr hd

/-- Second part of Zykov symmetrisation. A witness to non-transitivity of non-adjacency
where the involved vertices have the same degree can be used to generate
(using `replaceVertex` only) a graph with more edges. -/
theorem card_lt_card_replaceVertex2 (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) (htu : G.Adj t u)
    (hdt : G.degree s = G.degree t) (hdu : G.degree s = G.degree u) :
    G.edgeFinset.card < ((G.replaceVertex s t).replaceVertex s u).edgeFinset.card := by
  have ntu : t ≠ u := G.ne_of_adj htu
  have nst : s ≠ t := fun a => by subst a; contradiction
  have := (G.adj_replaceVertex_iff_of_ne s t nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, hdt, Nat.add_sub_cancel]
  have de1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset, SimpleGraph.irrefl, ite_self]
    by_cases eq : v = t <;> simp_all
  have de2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    unfold degree
    rw [← card_singleton t, ← card_sdiff (by simp [htu.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton]
    split_ifs with hu hv hv
    · simp_all
    · simp_all
    · simp [adj_comm, hsu, hv]
    · simp [adj_comm, hsu, hv]
  have dpos : 0 < G.degree u := by
    rw [G.degree_pos_iff_exists_adj u]
    use t
    exact htu.symm
  have dmp : G.degree u - 1 + 1 = G.degree u := Nat.succ_pred_eq_of_pos dpos
  nth_rw 1 [de1, de2, hdu, ← dmp, add_tsub_assoc_of_le (by simp), add_tsub_cancel_left]
  linarith

variable {r}

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
theorem not_adj_transitive (hmax : G.IsTuranMaximal r) (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) :
    ¬G.Adj t u := by
  by_cases z : G.degree s = G.degree t ∧ G.degree s = G.degree u <;>
    (contrapose! hmax; unfold IsTuranMaximal; push_neg; intro cf)
  · use (G.replaceVertex s t).replaceVertex s u, inferInstance
    exact ⟨(cf.replaceVertex s t).replaceVertex s u,
      card_lt_card_replaceVertex2 _ hst hsu hmax z.1 z.2⟩
  · rw [Decidable.not_and] at z
    cases' z with st su
    · cases' lt_or_gt_of_ne st with less more
      · use G.replaceVertex t s, inferInstance
        rw [adj_comm] at hst
        exact ⟨cf.replaceVertex t s, G.card_lt_card_replaceVertex1 hst less⟩
      · use G.replaceVertex s t, inferInstance
        exact ⟨cf.replaceVertex s t, G.card_lt_card_replaceVertex1 hst more⟩
    · cases' lt_or_gt_of_ne su with less more
      · use G.replaceVertex u s, inferInstance
        rw [adj_comm] at hsu
        exact ⟨cf.replaceVertex u s, G.card_lt_card_replaceVertex1 hsu less⟩
      · use G.replaceVertex s u, inferInstance
        exact ⟨cf.replaceVertex s u, G.card_lt_card_replaceVertex1 hsu more⟩

variable {G} (hmax : G.IsTuranMaximal r)

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem notAdj_equivalence : Equivalence fun x y => ¬G.Adj x y where
  refl x := by simp
  symm xy := by simp [xy, adj_comm]
  trans xy yz := by
    rw [adj_comm] at xy
    exact G.not_adj_transitive hmax xy yz

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph that exists
because of `notAdj_equivalence`. Said graph is therefore a complete multipartite graph. -/
def notAdjSetoid : Setoid V := ⟨_, (notAdj_equivalence hmax)⟩

instance : DecidableRel (notAdjSetoid hmax).r :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

/-- The finpartition derived from `notAdjSetoid`. -/
def notAdjFinpartition : Finpartition (univ : Finset V) :=
  Finpartition.ofSetoid (notAdjSetoid hmax)

theorem degree_eq_fintype_card_sub_part_card : G.degree s = Fintype.card V -
    ((notAdjFinpartition hmax).part (mem_univ s)).card := by
  calc
    G.degree s = (univ.filter (fun b => G.Adj s b)).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter (fun b => ¬G.Adj s b)).card :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert (Finpartition.mem_part_ofSetoid_iff_rel).symm
      simp [notAdjSetoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
theorem notAdj_equipartition : (notAdjFinpartition hmax).IsEquipartition := by
  let fp := notAdjFinpartition hmax
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  have large_eq : large = fp.part (a := w) (mem_univ _) :=
    (fp.existsUnique_mem (a := w) (mem_univ _)).unique
      ⟨hl, hw⟩ ⟨fp.part_mem _, fp.mem_part _⟩
  have small_eq : small = fp.part (a := v) (mem_univ _) :=
    (fp.existsUnique_mem (a := v) (mem_univ _)).unique
      ⟨hs, hv⟩ ⟨fp.part_mem _, fp.mem_part _⟩
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro cf
    use G.replaceVertex v w, inferInstance
    refine' ⟨cf.replaceVertex v w, _⟩
    have ha : G.Adj v w := by
      have lsn : large ≠ small := fun _ => by simp_all only [add_lt_iff_neg_left, not_lt_zero']
      contrapose! lsn
      have : _ ∈ fp.part _ ↔ ¬G.Adj v w := Finpartition.mem_part_ofSetoid_iff_rel
      exact fp.eq_of_mem_parts hl hs hw (small_eq ▸ this.mpr lsn)
    rw [G.card_edgeFinset_replaceVertex_of_adj ha]
    have large_le : large.card ≤ Fintype.card V := by
      simpa using card_le_card large.subset_univ
    have small_le : small.card ≤ Fintype.card V := by
      simpa using card_le_card small.subset_univ
    rw [degree_eq_fintype_card_sub_part_card, ← small_eq,
      degree_eq_fintype_card_sub_part_card, ← large_eq,
      Nat.add_sub_assoc (by rw [tsub_le_tsub_iff_left small_le]; linarith),
      tsub_tsub_tsub_cancel_left large_le, Nat.add_sub_assoc (lt_tsub_iff_left.mpr ineq).le]
    linarith [tsub_pos_iff_lt.mpr (lt_tsub_iff_left.mpr ineq)]
  contradiction

theorem notAdj_card_parts_le : (notAdjFinpartition hmax).parts.card ≤ r := by
  let fp := notAdjFinpartition hmax
  by_contra! h
  -- `z` is an `r + 1`-clique in `G`, contradicting Turán-maximality
  let z := fp.reprs
  have ncf : ¬G.CliqueFree z.card := by
    apply IsNClique.not_cliqueFree (s := z)
    constructor
    swap; · rfl
    intro v hv w hw hn
    norm_cast at hv hw
    contrapose! hn
    exact fp.reprs_injective hv hw (fp.eq_of_mem_parts (fp.part_mem _) (fp.part_mem _)
      (Finpartition.mem_part_ofSetoid_iff_rel.mpr hn) (fp.mem_part _))
  rw [Finpartition.card_reprs] at ncf
  exact absurd (CliqueFree.mono (Nat.succ_le_of_lt h) hmax.1) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
The `min` is necessary because `r` may be greater than `n`, in which case `G` is complete but
still `r + 1`-cliquefree for having insufficiently many vertices. -/
theorem notAdj_card_parts : (notAdjFinpartition hmax).parts.card = min (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  apply le_antisymm (le_min fp.card_parts_le_card (notAdj_card_parts_le _))
  by_contra! h
  rw [lt_min_iff] at h
  obtain ⟨x, _, y, _, hn, he⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun a => fp.part (a := a) (by simp)) univ fp.parts h.1 (fun _ _ => fp.part_mem _)
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro
    use G.addEdge x y, inferInstance
    have cf : G.CliqueFree r := by
      simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
        forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff]
      intro z zc
      obtain ⟨x', xm, y', ym, hn', he'⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
        (f := fun a => fp.part (a := a) (by simp)) z fp.parts (zc.symm ▸ h.2)
        (fun _ _ => fp.part_mem _)
      unfold Set.Pairwise; push_neg; norm_cast
      use x', xm, y', ym, hn'
      change (notAdjSetoid hmax).r x' y'
      apply Finpartition.mem_part_ofSetoid_iff_rel.mp
      exact he' ▸ fp.mem_part _
    refine' ⟨cf.addEdge x y, _⟩
    rw [G.card_edgeFinset_addEdge _ hn]; · linarith
    change (notAdjSetoid hmax).r x y
    apply Finpartition.mem_part_ofSetoid_iff_rel.mp
    exact he ▸ fp.mem_part _
  contradiction

/-- **Turán's theorem**, forward direction.
Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
noncomputable def isTuranMaximalIsoTuranGraph : G ≃g turanGraph (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  obtain ⟨zm, zp⟩ := (notAdj_equipartition hmax).partPreservingEquiv
  use (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  rw [← not_iff_not]
  change _ ↔ (notAdjSetoid hmax).r a b
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change _ ↔ b ∈ fp.part _
  have pe : b ∈ fp.part (mem_univ a) ↔ fp.part (mem_univ a) = fp.part (mem_univ b) := by
    constructor <;> intro h
    · exact fp.eq_of_mem_parts (fp.part_mem _) (fp.part_mem _) h (fp.mem_part _)
    · rw [h]; exact fp.mem_part _
  rw [pe, zp ⟨a, mem_univ _⟩ ⟨b, mem_univ _⟩, notAdj_card_parts, not_not, min_comm]
  rcases le_or_lt r (Fintype.card V) with h | h
  · rw [min_eq_left h]; rfl
  · rw [min_eq_right h.le]
    have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ _⟩).2
    have cn0 : Fintype.card V ≠ 0 := by by_contra h; exact absurd (h ▸ lc a) not_lt_zero'
    have rn0 : r ≠ 0 := by linarith
    rw [(Nat.mod_eq_iff_lt cn0).mpr (lc a), (Nat.mod_eq_iff_lt cn0).mpr (lc b),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc a).trans h),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc b).trans h)]
    rfl

variable {n : ℕ}

instance : DecidableRel (turanGraph n r).Adj := by dsimp only [turanGraph]; infer_instance

variable (hr : 0 < r)

/-- Equivalence 0 -/
def equivFin0 (p : ℕ → Prop) : { x : Fin n // p ↑x } ≃ { x : ℕ // x < n ∧ p x } where
  toFun := fun ⟨v, q⟩ ↦ ⟨v.1, ⟨v.2, q⟩⟩
  invFun := fun ⟨v, q⟩ ↦ ⟨⟨v, q.1⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem degree_turanGraph (v : Fin n) :
    (turanGraph n r).degree v = n - (n / r + if v % r < n % r then 1 else 0) := by
  simp_rw [← card_neighborFinset_eq_degree, neighborFinset, Set.toFinset_card,
    Fintype.card_ofFinset, mem_neighborSet, turanGraph, filter_not, card_univ_diff,
    Fintype.card_fin, ← Fintype.card_subtype]
  congr
  rw [← Nat.count_modEq_card _ hr, Nat.count_eq_card_fintype]
  apply @Fintype.card_congr _ _ _ (Nat.CountSet.fintype _ n) _
  convert (equivFin0 _) using 3
  rw [Nat.ModEq.comm]; rfl

private lemma aux2 : n - n / r = (r - 1) * (n / r) + n % r := by
  nth_rw 1 [← Nat.div_add_mod n r, add_comm]
  nth_rw 2 [← one_mul (n / r)]
  nth_rw 1 [add_tsub_assoc_of_le (by exact Nat.mul_le_mul_right (n / r) hr),
    ← tsub_mul, add_comm]

private lemma aux3 (v : ℕ) : n - (n / r + if v % r < n % r then 1 else 0) =
    (r - 1) * (n / r) + (n % r - if v % r < n % r then 1 else 0) := by
  rw [← Nat.sub_sub, aux2 hr, add_tsub_assoc_of_le]
  split_ifs with c
  · exact (zero_le _).trans_lt c
  · apply zero_le

private lemma aux4 : Even ((n + n % r) * (r - 1) * (n / r)) := by
  cases' (r - 1).even_or_odd with re ro
  · simp [re]
  · rw [Nat.odd_sub' hr] at ro
    simp only [Nat.odd_iff_not_even, Nat.not_even_one, not_false_eq_true, true_iff] at ro
    cases' n.even_or_odd with ne no
    · have v : Even (n + n % r) := Even.add ne ((Even.mod_even_iff ro).mpr ne)
      simp [v, parity_simps]
    · have v : Even (n + n % r) := Odd.add_odd no ((Odd.mod_even_iff ro).mpr no)
      simp [v, parity_simps]

open BigOperators in
/-- Formula for the number of edges in `turanGraph n r`. -/
theorem card_edgeFinset_turanGraph : (turanGraph n r).edgeFinset.card =
    (n + n % r) * (r - 1) * (n / r) / 2 + (n % r).choose 2 := by
  rw [← mul_left_cancel_iff_of_pos zero_lt_two, ← sum_degrees_eq_twice_card_edges]
  simp_rw [degree_turanGraph hr, aux3 hr]
  rw [sum_add_distrib, sum_tsub_distrib]
  swap
  · intro x _
    split_ifs with c
    · exact (zero_le _).trans_lt c
    · apply zero_le
  simp_rw [sum_const, card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ if x % r < n % r then 1 else 0),
    ← sum_fiberwise_of_maps_to (g := (· % r)) (t := Ico 0 r) (fun _ _ ↦ by simp [Nat.mod_lt _ hr])]
  have : ∀ j ∈ Ico 0 r,
      (∑ i in (range n).filter (· % r = j), if i % r < n % r then 1 else 0) =
      if j < n % r then n.count (· ≡ j [MOD r]) else 0 := by
    intro j hj
    rw [sum_boole, filter_filter]
    split_ifs with hl
    · have re : (range n).filter (fun a ↦ a % r = j ∧ a % r < n % r) =
          (range n).filter (fun a ↦ a % r = j % r) := by
        ext a
        simp_rw [mem_filter, and_congr_right_iff]
        have je := Nat.mod_eq_of_lt (mem_Ico.mp hj).2
        intro; constructor
        · intro ⟨h1, _⟩; exact h1.trans je.symm
        · intro h; rw [h, je]; exact ⟨rfl, hl⟩
      rw [re, Nat.cast_id, Nat.count_eq_card_filter_range]; rfl
    · have re : (range n).filter (fun a ↦ a % r = j ∧ a % r < n % r) =
          (range n).filter (fun _ ↦ False) := by
        ext a
        simp_rw [mem_filter, and_congr_right_iff]
        intro; constructor
        · intro ⟨h1, h2⟩; exact absurd (h1 ▸ h2) hl
        · tauto
      simp [re]
  rw [sum_congr rfl this, ← sum_Ico_consecutive _ (Nat.zero_le _) (Nat.mod_lt n hr).le]
  clear this
  have : ∀ i ∈ Ico 0 (n % r),
      (if i < n % r then Nat.count (fun x ↦ x ≡ i [MOD r]) n else 0) = n / r + 1 := by
    intro i hi
    rw [mem_Ico] at hi
    simp_rw [hi.2, ite_true, Nat.count_modEq_card _ hr, (i.mod_le r).trans_lt hi.2, ite_true]
  rw [sum_congr rfl this, sum_const, Nat.Ico_zero_eq_range, card_range, smul_eq_mul]
  clear this
  have : ∀ i ∈ Ico (n % r) r,
      (if i < n % r then Nat.count (fun x ↦ x ≡ i [MOD r]) n else 0) = 0 := by
    intro i hi
    rw [mem_Ico] at hi
    simp [hi.1.not_lt]
  rw [sum_congr rfl this, sum_const_zero, add_zero]
  clear this
  rw [mul_comm n (n % r), ← Nat.mul_sub_left_distrib, ← Nat.sub_sub, mul_tsub, mul_one,
    ← add_tsub_assoc_of_le]
  swap
  · cases' (n % r).eq_zero_or_pos with h h; · simp [h]
    rw [le_mul_iff_one_le_right h, Nat.one_le_iff_ne_zero, Nat.sub_ne_zero_iff_lt]
    change 1 ≤ r at hr
    cases' hr.eq_or_gt with i i
    · rw [i, Nat.mod_one] at h; simp at h
    · refine' Nat.div_lt_self _ i
      contrapose! h
      simp only [nonpos_iff_eq_zero] at h; subst h; simp
  rw [aux2 hr, mul_add, ← add_assoc, ← add_mul, ← mul_assoc]
  rw [mul_add, Nat.two_mul_div_two_of_even (aux4 hr), add_tsub_assoc_of_le (Nat.le_mul_self _)]
  congr
  cases' (n % r).eq_zero_or_pos with h h; · simp [h]
  rw [Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_self_pred _), mul_tsub,
    mul_one]

theorem card_edgeFinset_turanGraph_add : (turanGraph (n + r) r).edgeFinset.card =
    r.choose 2 + (r - 1) * n + (turanGraph n r).edgeFinset.card := by
  simp_rw [card_edgeFinset_turanGraph hr, Nat.add_mod_right]
  rw [Nat.add_div_right _ hr, ← add_assoc]; congr
  rw [Nat.mul_succ]
  conv_lhs => enter [1, 1, 1, 1]; rw [add_assoc, add_comm r, ← add_assoc]
  rw [add_mul, add_mul, add_assoc]
  conv_lhs =>
    enter [1, 2]
    rw [mul_assoc, mul_comm, mul_comm _ (r - 1), mul_assoc, ← mul_add, mul_comm _ r,
      add_comm (n + r), ← add_assoc, Nat.div_add_mod, ← add_assoc, mul_comm, ← two_mul, add_mul]
  nth_rw 1 [← Nat.div_two_mul_two_of_even (aux4 hr),
    ← Nat.div_two_mul_two_of_even (n := 2 * n * (r - 1)) (by simp),
    ← Nat.div_two_mul_two_of_even (n := r * (r - 1)) (Nat.even_mul_self_pred _),
    ← add_mul, ← add_mul, Nat.mul_div_left _ zero_lt_two]
  rw [← Nat.choose_two_right, add_comm, add_comm _ (r.choose 2)]; congr
  rw [mul_assoc, mul_comm, Nat.mul_div_left _ zero_lt_two, mul_comm]

/-- When `n < r`, `turanGraph n r` is Turán-maximal (in fact it is the complete graph `K_n`). -/
theorem isTuranMaximal_turanGraph_of_lt (ht : n < r) : (turanGraph n r).IsTuranMaximal r := by
  constructor
  · exact cliqueFree_of_card_lt (by rw [Fintype.card_fin]; linarith)
  · intro H _ _
    rw [card_edgeFinset_turanGraph hr, (Nat.div_eq_zero_iff hr).mpr ht, mul_zero, Nat.zero_div,
      zero_add, Nat.mod_eq_of_lt ht]
    convert card_edgeFinset_le_card_choose_two
    · simp
    · infer_instance
    · infer_instance
