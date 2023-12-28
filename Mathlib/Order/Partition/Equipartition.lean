/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.Set.Equitable
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Partition.Finpartition

#align_import order.partition.equipartition from "leanprover-community/mathlib"@"b363547b3113d350d053abdf2884e9850a56b205"

/-!
# Finite equipartitions

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `Finpartition.IsEquipartition`: Predicate for a `Finpartition` to be an equipartition.
-/


open Finset Fintype

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} (P : Finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def IsEquipartition : Prop :=
  (P.parts : Set (Finset α)).EquitableOn card
#align finpartition.is_equipartition Finpartition.IsEquipartition

theorem isEquipartition_iff_card_parts_eq_average :
    P.IsEquipartition ↔
      ∀ a : Finset α,
        a ∈ P.parts → a.card = s.card / P.parts.card ∨ a.card = s.card / P.parts.card + 1 :=
  by simp_rw [IsEquipartition, Finset.equitableOn_iff, P.sum_card_parts]
#align finpartition.is_equipartition_iff_card_parts_eq_average Finpartition.isEquipartition_iff_card_parts_eq_average

variable {P}

lemma not_isEquipartition :
    ¬P.IsEquipartition ↔ ∃ a ∈ P.parts, ∃ b ∈ P.parts, Finset.card b + 1 < Finset.card a :=
  Set.not_equitableOn

theorem Set.Subsingleton.isEquipartition (h : (P.parts : Set (Finset α)).Subsingleton) :
    P.IsEquipartition :=
  Set.Subsingleton.equitableOn h _
#align finpartition.set.subsingleton.is_equipartition Finpartition.Set.Subsingleton.isEquipartition

theorem IsEquipartition.card_parts_eq_average (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card ∨ t.card = s.card / P.parts.card + 1 :=
  P.isEquipartition_iff_card_parts_eq_average.1 hP _ ht
#align finpartition.is_equipartition.card_parts_eq_average Finpartition.IsEquipartition.card_parts_eq_average

theorem IsEquipartition.card_part_eq_average_iff (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card ↔ t.card ≠ s.card / P.parts.card + 1 := by
  have a := hP.card_parts_eq_average ht
  have b : ¬(t.card = s.card / P.parts.card ∧ t.card = s.card / P.parts.card + 1) := by
    by_contra h; exact absurd (h.1 ▸ h.2) (lt_add_one _).ne
  tauto

theorem IsEquipartition.average_le_card_part (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    s.card / P.parts.card ≤ t.card := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le hP ht
#align finpartition.is_equipartition.average_le_card_part Finpartition.IsEquipartition.average_le_card_part

theorem IsEquipartition.card_part_le_average_add_one (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card ≤ s.card / P.parts.card + 1 := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le_add_one hP ht
#align finpartition.is_equipartition.card_part_le_average_add_one Finpartition.IsEquipartition.card_part_le_average_add_one

theorem IsEquipartition.filter_neg_average_add_one_eq_average (hP : P.IsEquipartition) :
    P.parts.filter (fun p ↦ ¬p.card = s.card / P.parts.card + 1) =
    P.parts.filter (fun p ↦ p.card = s.card / P.parts.card) := by
  ext p
  simp only [mem_filter, and_congr_right_iff]
  exact fun hp ↦ (hP.card_part_eq_average_iff hp).symm

/-- An equipartition of a finset with `n` elements into `k` parts has
`n % k` parts of size `n / k + 1`. -/
theorem IsEquipartition.card_large_parts_eq_mod (hP : P.IsEquipartition) :
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card + 1).card = s.card % P.parts.card := by
  have z := P.sum_card_parts
  rw [← sum_filter_add_sum_filter_not (s := P.parts)
      (p := fun x ↦ x.card = s.card / P.parts.card + 1),
    hP.filter_neg_average_add_one_eq_average,
    sum_const_nat (m := s.card / P.parts.card + 1) (by simp),
    sum_const_nat (m := s.card / P.parts.card) (by simp),
    ← hP.filter_neg_average_add_one_eq_average,
    mul_add, add_comm, ← add_assoc, ← add_mul, mul_one, add_comm (Finset.card _),
    filter_card_add_filter_neg_card_eq_card, add_comm] at z
  rw [← add_left_inj, Nat.mod_add_div, z]

/-- An equipartition of a finset with `n` elements into `k` parts has
`n - n % k` parts of size `n / k`. -/
theorem IsEquipartition.card_small_parts_eq_mod (hP : P.IsEquipartition) :
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card).card =
    P.parts.card - s.card % P.parts.card := by
  conv_rhs =>
    arg 1
    rw [← filter_card_add_filter_neg_card_eq_card (p := fun p ↦ p.card = s.card / P.parts.card + 1)]
  rw [hP.card_large_parts_eq_mod, add_tsub_cancel_left, hP.filter_neg_average_add_one_eq_average]

/-- Large side of `IsEquipartition.partsEquiv`. -/
noncomputable def IsEquipartition.largePartsEquiv (hP : P.IsEquipartition) :
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card + 1) ≃
    Ico 0 (s.card % P.parts.card) where
  toFun p := by
    let e := (P.parts.filter fun p ↦ p.card = s.card / P.parts.card + 1).equivFin
    rw [hP.card_large_parts_eq_mod] at e
    exact ⟨e p, by simp⟩
  invFun i := by
    let e := (P.parts.filter fun p ↦ p.card = s.card / P.parts.card + 1).equivFin
    rw [hP.card_large_parts_eq_mod] at e
    exact e.symm ⟨i.1, (mem_Ico.mp i.2).2⟩
  left_inv p := by simp
  right_inv i := by simp

/-- Small side of `IsEquipartition.partsEquiv`. -/
noncomputable def IsEquipartition.smallPartsEquiv (hP : P.IsEquipartition) :
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card) ≃
    Ico (s.card % P.parts.card) P.parts.card where
  toFun p := by
    let e := (P.parts.filter fun p ↦ p.card = s.card / P.parts.card).equivFin
    rw [hP.card_small_parts_eq_mod] at e
    exact ⟨e p + s.card % P.parts.card, by
      simp only [mem_Ico, le_add_iff_nonneg_left, zero_le, true_and]
      have := add_lt_add_right (e p).2 (s.card % P.parts.card)
      rw [tsub_add_cancel_of_le P.card_mod_card_parts_le] at this; exact this⟩
  invFun i := by
    let e := (P.parts.filter fun p ↦ p.card = s.card / P.parts.card).equivFin
    rw [hP.card_small_parts_eq_mod] at e
    exact e.symm ⟨i.1 - s.card % P.parts.card, by
      obtain ⟨l, u⟩ := mem_Ico.mp i.2
      apply tsub_lt_tsub_right_of_le l u⟩
  left_inv p := by simp
  right_inv i := by
    simp only [Equiv.apply_symm_apply]; congr
    exact tsub_add_cancel_of_le (mem_Ico.mp i.2).1

/-- Left side of `IsEquipartition.partsEquiv`, the "splitter". -/
def IsEquipartition.partsEquivLeft (hP : P.IsEquipartition) : P.parts ≃
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card + 1) ⊕
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card) where
  toFun p := if c : p.1.card = s.card / P.parts.card + 1
    then Sum.inl (by use p.1; rw [mem_filter]; exact ⟨p.2, c⟩)
    else Sum.inr (by use p.1; rw [mem_filter]; exact ⟨p.2, (hP.card_part_eq_average_iff p.2).mpr c⟩)
  invFun p := by
    cases' p with p p <;> (simp only [mem_filter] at p; exact ⟨p.1, p.2.1⟩)
  left_inv p := by
    conv_lhs => arg 1; dsimp only
    by_cases c : p.1.card = s.card / P.parts.card + 1 <;>
      ((conv_lhs => arg 1; simp only [c]); simp)
  right_inv p := by
    cases' p with p p
    · simp [(mem_filter.mp p.2).2]
    · obtain ⟨p1, p2⟩ := mem_filter.mp p.2
      simp [(hP.card_part_eq_average_iff p1).mp p2]

/-- Right side of `IsEquipartition.partsEquiv`, the "collector". -/
def IsEquipartition.partsEquivRight :
    Ico 0 (s.card % P.parts.card) ⊕ Ico (s.card % P.parts.card) P.parts.card ≃
    Ico 0 P.parts.card where
  toFun i := by
    cases' i with i i
    · exact ⟨i.1, by simp [(mem_Ico.mp i.2).2.trans_le P.card_mod_card_parts_le]⟩
    · exact ⟨i.1, by simp [(mem_Ico.mp i.2).2]⟩
  invFun i := if c : i < s.card % P.parts.card
    then Sum.inl (by use i.1; simp [c])
    else Sum.inr (by use i.1; rw [mem_Ico]; rw [not_lt] at c; exact ⟨c, (mem_Ico.mp i.2).2⟩)
  left_inv i := by cases' i with i i <;> simp [mem_Ico.mp i.2]
  right_inv i := by
    conv_lhs => arg 1; dsimp only
    by_cases c : i < s.card % P.parts.card <;> conv_lhs => arg 1; simp only [c]

/-- Equivalence between the `k` parts of an equipartition and `[0, k)`, with the larger parts
mapping to the smaller numbers and vice versa. -/
noncomputable def IsEquipartition.partsEquiv (hP : P.IsEquipartition) :=
  (hP.partsEquivLeft.trans (hP.largePartsEquiv.sumCongr hP.smallPartsEquiv)).trans partsEquivRight

noncomputable def equivFinOf (p : { x // x ∈ P.parts }) := p.1.equivFin

noncomputable def kkk (hP : P.IsEquipartition) :
    s ≃ { t : Finset α × ℕ // t.1 ∈ P.parts ∧ t.2 < t.1.card } where
  toFun x := by
    let p := P.part x.2
    exact ⟨⟨p, p.equivFin ⟨x.1, P.mem_part x.2⟩⟩,
      ⟨by dsimp only; exact P.part_mem x.2, by dsimp only; apply Fin.prop⟩⟩
  invFun t := by
    obtain ⟨⟨p, i⟩, ⟨m, l⟩⟩ := t
    let x := p.equivFin.symm ⟨i, l⟩
    exact ⟨x.1, mem_of_subset ((le_sup m).trans P.supParts.le) x.2⟩
  left_inv x := by simp
  right_inv t := by
    obtain ⟨⟨p, i⟩, ⟨m, l⟩⟩ := t
    dsimp only at m l
    let x := p.equivFin.symm ⟨i, l⟩
    have ξ : ↑x ∈ s := mem_of_subset ((le_sup m).trans P.supParts.le) x.2
    have ξ' : P.part ξ = p := P.eq_of_mem_parts (P.part_mem _) m (P.mem_part _) x.2
    simp only [ξ', id_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
    change (P.part ξ).equivFin _ = i
    simp

theorem IsEquipartition.large_part_iff_partsEquiv_lt (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card + 1 ↔ hP.partsEquiv ⟨t, ht⟩ < s.card % P.parts.card := by
  constructor <;> intro h
  · unfold IsEquipartition.partsEquiv
    simp only [Equiv.trans_apply]
    unfold IsEquipartition.partsEquivLeft
    simp only [eq_mp_eq_cast, filter_congr_decidable, filter_val, Multiset.mem_filter, mem_val,
      set_coe_cast, Equiv.coe_fn_mk, h, dite_true, Equiv.sumCongr_apply, Sum.map_inl]
    unfold IsEquipartition.partsEquivRight
    simp only [Equiv.coe_fn_mk]
    unfold IsEquipartition.largePartsEquiv
    simp
  · contrapose! h
    rw [← hP.card_part_eq_average_iff] at h
    unfold IsEquipartition.partsEquiv
    simp only [Equiv.trans_apply]
    unfold IsEquipartition.partsEquivLeft
    simp only [eq_mp_eq_cast, filter_congr_decidable, filter_val, Multiset.mem_filter, mem_val,
      set_coe_cast, Equiv.coe_fn_mk, h, self_eq_add_right, dite_false, Equiv.sumCongr_apply,
      Sum.map_inr]
    unfold IsEquipartition.partsEquivRight
    simp only [Equiv.coe_fn_mk]
    unfold IsEquipartition.smallPartsEquiv
    simp only [Equiv.coe_fn_mk, le_add_iff_nonneg_left, zero_le]
    exact ht

noncomputable def IsEquipartition.partPreservingEquivToFun (hP : P.IsEquipartition)
    (x : { x // x ∈ s }) : Fin s.card := by
  let part := P.part x.2
  let q := part.equivFin ⟨x.1, P.mem_part x.2⟩
  let r := hP.partsEquiv ⟨part, P.part_mem x.2⟩
  exact ⟨q * P.parts.card + r, by
    cases' hP.card_parts_eq_average (P.part_mem x.2) with h h
    · calc
        q * P.parts.card + r < q * P.parts.card + P.parts.card := by
          rw [add_lt_add_iff_left]
          exact (mem_Ico.mp r.2).2
        _ = (q + 1) * P.parts.card := (Nat.succ_mul _ _).symm
        _ ≤ s.card / P.parts.card * P.parts.card := by
          apply mul_le_mul_of_nonneg_right (Nat.succ_le_of_lt _) (Nat.zero_le _)
          rw [← h]
          exact q.2
        _ ≤ s.card / P.parts.card * P.parts.card + s.card % P.parts.card := by simp
        _ = _ := by rw [add_comm, mul_comm, Nat.mod_add_div]
    · calc
        q * P.parts.card + r ≤ s.card / P.parts.card * P.parts.card + r := by
          rw [add_le_add_iff_right]
          apply mul_le_mul_of_nonneg_right _ (Nat.zero_le _)
          rw [← Nat.lt_add_one_iff, ← h]
          exact q.2
        _ < s.card / P.parts.card * P.parts.card + s.card % P.parts.card := by
          rw [add_lt_add_iff_left]
          exact (hP.large_part_iff_partsEquiv_lt (P.part_mem x.2)).mp h
        _ = _ := by rw [add_comm, mul_comm, Nat.mod_add_div]⟩

theorem IsEquipartition.toFun_div (hP : P.IsEquipartition) (x : { x // x ∈ s }) :
    (hP.partPreservingEquivToFun x) / P.parts.card =
    (P.part x.2).equivFin ⟨x.1, P.mem_part x.2⟩ := by
  let r := hP.partsEquiv ⟨P.part x.2, P.part_mem x.2⟩
  simp_rw [partPreservingEquivToFun]
  have ppos : 0 < P.parts.card := by
    rw [Finset.card_pos]
    exact P.parts_nonempty_of_mem x.2
  rw [add_comm, Nat.add_mul_div_right _ _ ppos, Nat.div_eq_of_lt (mem_Ico.mp r.2).2, zero_add]

theorem IsEquipartition.toFun_mod (hP : P.IsEquipartition) (x : { x // x ∈ s }) :
    (hP.partPreservingEquivToFun x) % P.parts.card =
    hP.partsEquiv ⟨P.part x.2, P.part_mem x.2⟩ := by
  let res := hP.partsEquiv ⟨P.part x.2, P.part_mem x.2⟩
  simp_rw [partPreservingEquivToFun]
  have ppos : 0 < P.parts.card := by
    rw [Finset.card_pos]
    exact P.parts_nonempty_of_mem x.2
  rw [add_comm, mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_iff_lt ppos.ne.symm]
  exact (mem_Ico.mp res.2).2

theorem IsEquipartition.toFun_val (hP : P.IsEquipartition) (x : { x // x ∈ s }) :
    hP.partPreservingEquivToFun x =
    ⟨((P.part x.2).equivFin ⟨x.1, P.mem_part x.2⟩).1 * P.parts.card +
    hP.partsEquiv ⟨P.part x.2, P.part_mem x.2⟩, (hP.partPreservingEquivToFun x).prop⟩ := by
  congr

noncomputable def IsEquipartition.partPreservingEquivInvFun (hP : P.IsEquipartition)
    (i : Fin s.card) : { x // x ∈ s } := by
  have ppos : 0 < P.parts.card := by
    rw [Finset.card_pos]
    obtain ⟨_, xm⟩ := Finset.card_pos.mp ((zero_le _).trans_lt i.2)
    exact P.parts_nonempty_of_mem xm
  let q := i.1 / P.parts.card
  let r := i.1 % P.parts.card
  let p := hP.partsEquiv.symm ⟨r, by rw [mem_Ico]; exact ⟨zero_le _, Nat.mod_lt _ ppos⟩⟩
  have ql : q < p.1.card := by
    cases' hP.card_parts_eq_average p.2 with h h <;> rw [h]
    · by_contra! q'
      rw [← mul_le_mul_left ppos] at q'
      have r' := ((hP.card_part_eq_average_iff p.2).trans
        (hP.large_part_iff_partsEquiv_lt p.2).not).mp h
      simp_rw [Subtype.coe_eta, Equiv.apply_symm_apply, not_lt] at r'
      have g := add_le_add r' q'
      simp_rw [Nat.mod_add_div, ← not_lt] at g
      exact absurd i.2 g
    · rw [Nat.lt_add_one_iff]; exact Nat.div_le_div_right i.2.le
  exact ⟨p.1.equivFin.symm ⟨q, ql⟩, Finset.mem_of_subset (P.le p.2) (p.1.equivFin.symm ⟨q, ql⟩).2⟩

/-- Part-preserving equivalence between a finset `s`, over which an equipartition has been
defined, and `Fin s.card`. -/
noncomputable def IsEquipartition.partPreservingEquiv (hP : P.IsEquipartition) :
    s ≃ Fin s.card where
  toFun := hP.partPreservingEquivToFun
  invFun := hP.partPreservingEquivInvFun
  left_inv x := by
    let w := hP.partPreservingEquivToFun x
    unfold partPreservingEquivInvFun; dsimp only
    have r_part := hP.partsEquiv.symm.apply_eq_iff_eq.mpr
      (Subtype.coe_eq_of_eq_mk (hP.toFun_mod x).symm)
    rw [Equiv.symm_apply_apply] at r_part
    have q_part := (hP.toFun_div x).symm
    /- q < Finset.card ↑((partsEquiv hP).symm
    { val := ↑(hP.partPreservingEquivToFun x) % P.parts.card, property := _ })  -/
    have q_part := (Fin.eq_mk_iff_val_eq (a := (P.part x.2).equivFin ⟨x.1, P.mem_part x.2⟩)).mpr q_part
  right_inv := sorry

/-- An equipartition of a finset with `n` elements into `k` parts has
a part-preserving equivalence with the residue classes of `Fin n` modulo `k`. -/
noncomputable def IsEquipartition.partPreservingEquiv' (hP : P.IsEquipartition) :
    { m : s ≃ Fin s.card //
      ∀ a b, P.part a.2 = P.part b.2 ↔ m a % P.parts.card = m b % P.parts.card } := by
  sorry

/-! ### Discrete and indiscrete finpartition -/


variable (s) -- [Decidable (a = ⊥)]

theorem bot_isEquipartition : (⊥ : Finpartition s).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩
#align finpartition.bot_is_equipartition Finpartition.bot_isEquipartition

theorem top_isEquipartition [Decidable (s = ⊥)] : (⊤ : Finpartition s).IsEquipartition :=
  Set.Subsingleton.isEquipartition (parts_top_subsingleton _)
#align finpartition.top_is_equipartition Finpartition.top_isEquipartition

theorem indiscrete_isEquipartition {hs : s ≠ ∅} : (indiscrete hs).IsEquipartition := by
  rw [IsEquipartition, indiscrete_parts, coe_singleton]
  exact Set.equitableOn_singleton s _
#align finpartition.indiscrete_is_equipartition Finpartition.indiscrete_isEquipartition

end Finpartition
