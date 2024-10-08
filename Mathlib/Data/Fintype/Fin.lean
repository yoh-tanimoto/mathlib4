/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Order.Interval.Finset.Fin

/-!
# The structure of `Fintype (Fin n)`

This file contains some basic results about the `Fintype` instance for `Fin`,
especially properties of `Finset.univ : Finset (Fin n)`.
-/

open Mathlib

open Finset

open Fintype

namespace Fin

variable {α β : Type*} {n : ℕ}

theorem map_valEmbedding_univ : (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n := by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

@[simp]
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _) :=
  coe_injective <| by ext; simp [pos_iff_ne_zero]

@[simp]
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb :=
  coe_injective <| by ext; simp [lt_def]

@[simp]
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmb _) := by
  ext i
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, Function.Embedding.coeFn_mk, exists_true_left]
  constructor
  · refine cases ?_ ?_ i
    · rintro ⟨⟨⟩⟩
    · intro i hi
      exact ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    simpa

@[simp]
theorem Iio_castSucc (i : Fin n) : Iio (castSucc i) = (Iio i).map Fin.castSuccEmb := by
  apply Finset.map_injective Fin.valEmbedding
  rw [Finset.map_map, Fin.map_valEmbedding_Iio]
  exact (Fin.map_valEmbedding_Iio i).symm

theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card = ite (p 0) 1 0 + (univ.filter (p ∘ Fin.succ)).card := by
  rw [Fin.univ_succ, filter_cons, card_disjUnion, filter_map, card_map]
  split_ifs <;> simp

theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card =
    if p 0 then (univ.filter (p ∘ Fin.succ)).card + 1 else (univ.filter (p ∘ Fin.succ)).card :=
  (card_filter_univ_succ' p).trans (by split_ifs <;> simp [add_comm 1])

theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : Vector α n) :
    (univ.filter fun i => v.get i = a).card = v.toList.count a := by
  induction' v with n x xs hxs
  · simp
  · simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Function.comp_def,
      Vector.get_cons_succ, hxs, List.count_cons, add_comm (ite (x = a) 1 0), beq_iff_eq]

end Fin
