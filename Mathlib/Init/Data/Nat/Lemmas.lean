/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Std.Data.Nat.Lemmas
import Std.WF
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.Order.Defs
import Mathlib.Util.CompileInductive

#align_import init.data.nat.lemmas from "leanprover-community/lean"@"38b59111b2b4e6c572582b27e8937e92fc70ac02"

universe u

namespace Nat

/-! addition -/

#align nat.add_comm Nat.add_comm

#align nat.add_assoc Nat.add_assoc

#align nat.add_left_comm Nat.add_left_comm

#align nat.add_left_cancel Nat.add_left_cancel

#align nat.add_right_cancel Nat.add_right_cancel

#align nat.succ_ne_zero Nat.succ_ne_zero

#align nat.succ_ne_self Nat.succ_ne_self

#align nat.one_ne_zero Nat.one_ne_zero

#align nat.zero_ne_one Nat.zero_ne_one

#align nat.eq_zero_of_add_eq_zero_right Nat.eq_zero_of_add_eq_zero_right

#align nat.eq_zero_of_add_eq_zero_left Nat.eq_zero_of_add_eq_zero_left

#align nat.add_right_comm Nat.add_right_comm

#align nat.eq_zero_of_add_eq_zero Nat.eq_zero_of_add_eq_zero

/-! multiplication -/

#align nat.mul_zero Nat.mul_zero

#align nat.mul_succ Nat.mul_succ

#align nat.zero_mul Nat.zero_mul

#align nat.succ_mul Nat.succ_mul

#align nat.right_distrib Nat.right_distrib

#align nat.left_distrib Nat.left_distrib

#align nat.mul_comm Nat.mul_comm

#align nat.mul_assoc Nat.mul_assoc

#align nat.mul_one Nat.mul_one

#align nat.one_mul Nat.one_mul

#align nat.succ_add_eq_succ_add Nat.succ_add_eq_add_succ

theorem eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
  | 0, m => fun _ => Or.inl rfl
  | succ n, m => by
    rw [succ_mul]; intro h
    exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)
#align nat.eq_zero_of_mul_eq_zero Nat.eq_zero_of_mul_eq_zero

/-! properties of inequality -/

#align nat.le_of_eq Nat.le_of_eq

#align nat.le_succ_of_le Nat.le_succ_of_le

#align nat.le_of_succ_le Nat.le_of_succ_le

#align nat.le_of_lt Nat.le_of_lt

#align nat.lt.step Nat.lt.step

#align nat.eq_zero_or_pos Nat.eq_zero_or_pos

#align nat.pos_of_ne_zero Nat.pos_of_ne_zero

#align nat.lt_trans Nat.lt_trans

#align nat.lt_of_le_of_lt Nat.lt_of_le_of_lt

#align nat.lt.base Nat.lt.base

#align nat.lt_succ_self Nat.lt_succ_self

#align nat.le_antisymm Nat.le_antisymm

#align nat.lt_or_ge Nat.lt_or_ge

#align nat.le_total Nat.le_total

#align nat.lt_of_le_and_ne Nat.lt_of_le_of_ne

#align nat.lt_iff_le_not_le Nat.lt_iff_le_not_le

instance linearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance
#align nat.linear_order Nat.linearOrder

#align nat.eq_zero_of_le_zero Nat.eq_zero_of_le_zero

#align nat.succ_lt_succ Nat.succ_lt_succ

#align nat.lt_of_succ_lt Nat.lt_of_succ_lt

#align nat.lt_of_succ_lt_succ Nat.lt_of_succ_lt_succ

#align nat.pred_lt_pred Nat.pred_lt_pred

#align nat.lt_of_succ_le Nat.lt_of_succ_le

#align nat.succ_le_of_lt Nat.succ_le_of_lt

#align nat.le_add_right Nat.le_add_right

#align nat.le_add_left Nat.le_add_left

#align nat.le.dest Nat.le.dest

#align nat.le.intro Nat.le.intro

#align nat.add_le_add_left Nat.add_le_add_left

#align nat.add_le_add_right Nat.add_le_add_right

#align nat.le_of_add_le_add_left Nat.le_of_add_le_add_left

#align nat.le_of_add_le_add_right Nat.le_of_add_le_add_rightₓ

#align nat.add_le_add_iff_right Nat.add_le_add_iff_right

#align nat.lt_of_add_lt_add_left Nat.lt_of_add_lt_add_left

#align nat.lt_of_add_lt_add_right Nat.lt_of_add_lt_add_right

#align nat.add_lt_add_left Nat.add_lt_add_left

#align nat.add_lt_add_right Nat.add_lt_add_right

#align nat.lt_add_of_pos_right Nat.lt_add_of_pos_right

#align nat.lt_add_of_pos_left Nat.lt_add_of_pos_left

#align nat.add_lt_add Nat.add_lt_add

#align nat.add_le_add Nat.add_le_add

#align nat.zero_lt_one Nat.zero_lt_one

#align nat.mul_le_mul_left Nat.mul_le_mul_left

#align nat.mul_le_mul_right Nat.mul_le_mul_right

#align nat.mul_lt_mul_of_pos_left Nat.mul_lt_mul_of_pos_left

#align nat.mul_lt_mul_of_pos_right Nat.mul_lt_mul_of_pos_right

#align nat.le_of_mul_le_mul_left Nat.le_of_mul_le_mul_left

#align nat.le_of_lt_succ Nat.le_of_lt_succ

#align nat.eq_of_mul_eq_mul_left Nat.eq_of_mul_eq_mul_left

#align nat.mul_pos Nat.mul_pos

#align nat.le_succ_of_pred_le Nat.le_succ_of_pred_le

#align nat.le_lt_antisymm Nat.le_lt_asymm

#align nat.lt_le_antisymm Nat.lt_le_asymm

#align nat.lt_asymm Nat.lt_asymm

protected def ltGeByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
  Decidable.byCases h₁ fun h => h₂ (Or.elim (Nat.lt_or_ge a b) (fun a => absurd a h) fun a => a)
#align nat.lt_ge_by_cases Nat.ltGeByCases

protected def ltByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C) (h₃ : b < a → C) :
    C :=
  Nat.ltGeByCases h₁ fun h₁ => Nat.ltGeByCases h₃ fun h => h₂ (Nat.le_antisymm h h₁)
#align nat.lt_by_cases Nat.ltByCases

#align nat.lt_trichotomy Nat.lt_trichotomy

#align nat.eq_or_lt_of_not_lt Nat.eq_or_lt_of_not_lt

#align nat.lt_succ_of_lt Nat.lt_succ_of_lt

#align nat.one_pos Nat.one_pos

#align nat.mul_le_mul_of_nonneg_left Nat.mul_le_mul_of_nonneg_left

#align nat.mul_le_mul_of_nonneg_right Nat.mul_le_mul_of_nonneg_right

#align nat.mul_lt_mul Nat.mul_lt_mulₓ

#align nat.mul_lt_mul' Nat.mul_lt_mul'ₓ

-- TODO: there are four variations, depending on which variables we assume to be nonneg
#align nat.mul_le_mul Nat.mul_le_mul


/-! successor and predecessor -/

#align nat.pred_zero Nat.pred_zero

#align nat.pred_succ Nat.pred_succ

#align nat.add_one_ne_zero Nat.add_one_ne_zero

#align nat.eq_zero_or_eq_succ_pred Nat.eq_zero_or_eq_succ_pred

#align nat.exists_eq_succ_of_ne_zero Nat.exists_eq_succ_of_ne_zero

def discriminate {B : Sort u} {n : ℕ} (H1 : n = 0 → B) (H2 : ∀ m, n = succ m → B) : B := by
  induction n with
  | zero => exact H1 rfl
  | succ n _ => apply H2 _ rfl
#align nat.discriminate Nat.discriminate

theorem one_eq_succ_zero : 1 = succ 0 :=
  rfl
#align nat.one_succ_zero Nat.one_eq_succ_zero

#align nat.pred_inj Nat.pred_inj

/-! subtraction

Many lemmas are proven more generally in mathlib `algebra/order/sub` -/

#align nat.zero_sub Nat.zero_sub

#align nat.sub_lt_succ Nat.sub_lt_succ

#align nat.sub_zero Nat.sub_zero

#align nat.sub_succ Nat.sub_succ

#align nat.succ_sub_succ Nat.succ_sub_succ

#align nat.sub_self Nat.sub_self

#align nat.add_sub_add_right Nat.add_sub_add_right

#align nat.add_sub_add_left Nat.add_sub_add_left

#align nat.add_sub_cancel Nat.add_sub_cancel

#align nat.add_sub_cancel_left Nat.add_sub_cancel_left

#align nat.sub_sub Nat.sub_sub

#align nat.le_of_le_of_sub_le_sub_right Nat.le_of_le_of_sub_le_sub_right

#align nat.sub_le_sub_iff_right Nat.sub_le_sub_iff_right

#align nat.sub_self_add Nat.sub_self_add

#align nat.le_sub_iff_right Nat.le_sub_iff_add_le

#align nat.sub_lt_of_pos_le Nat.sub_lt_of_pos_le

#align nat.sub_one Nat.sub_one

#align nat.succ_sub_one Nat.add_one_sub_one

#align nat.succ_pred_eq_of_pos Nat.succ_pred_eq_of_pos

#align nat.sub_eq_zero_of_le Nat.sub_eq_zero_of_le

#align nat.le_of_sub_eq_zero Nat.le_of_sub_eq_zero

#align nat.sub_eq_zero_iff_le Nat.sub_eq_zero_iff_le

#align nat.add_sub_of_le Nat.add_sub_of_le

#align nat.sub_add_cancel Nat.sub_add_cancel

#align nat.add_sub_assoc Nat.add_sub_assoc

#align nat.sub_eq_iff_eq_add Nat.sub_eq_iff_eq_add

#align nat.lt_of_sub_eq_succ Nat.lt_of_sub_eq_succ

#align nat.sub_le_sub_left Nat.sub_le_sub_left

#align nat.succ_sub_sub_succ Nat.succ_sub_sub_succ

#align nat.sub.right_comm Nat.sub_right_comm

#align nat.succ_sub Nat.succ_sub

#align nat.sub_pos_of_lt Nat.sub_pos_of_lt

#align nat.sub_sub_self Nat.sub_sub_self

#align nat.sub_add_comm Nat.sub_add_comm

#align nat.sub_one_sub_lt Nat.sub_one_sub_ltₓ

#align nat.mul_pred_left Nat.mul_pred_left

#align nat.mul_pred_right Nat.mul_pred_right

#align nat.mul_sub_right_distrib Nat.mul_sub_right_distrib

#align nat.mul_sub_left_distrib Nat.mul_sub_left_distrib

#align nat.mul_self_sub_mul_self_eq Nat.mul_self_sub_mul_self_eq

#align nat.succ_mul_succ_eq Nat.succ_mul_succ

/-! min -/

#align nat.zero_min Nat.zero_min

#align nat.min_zero Nat.min_zero

#align nat.succ_min_succ Nat.succ_min_succ

#align nat.sub_eq_sub_min Nat.sub_eq_sub_min

#align nat.sub_add_min_cancel Nat.sub_add_min_cancel

/-! induction principles -/


def twoStepInduction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (_IH1 : P n) (_IH2 : P (succ n)), P (succ (succ n))) : ∀ a : ℕ, P a
  | 0 => H1
  | 1 => H2
  | succ (succ _n) => H3 _ (twoStepInduction H1 H2 H3 _) (twoStepInduction H1 H2 H3 _)
#align nat.two_step_induction Nat.twoStepInduction

def subInduction {P : ℕ → ℕ → Sort u} (H1 : ∀ m, P 0 m) (H2 : ∀ n, P (succ n) 0)
    (H3 : ∀ n m, P n m → P (succ n) (succ m)) : ∀ n m : ℕ, P n m
  | 0, _m => H1 _
  | succ _n, 0 => H2 _
  | succ n, succ m => H3 _ _ (subInduction H1 H2 H3 n m)
#align nat.sub_induction Nat.subInduction

#align nat.strong_rec_on Nat.strongRecOn

-- porting note: added `elab_as_elim`
@[elab_as_elim]
protected theorem strong_induction_on {p : Nat → Prop} (n : Nat)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h
#align nat.strong_induction_on Nat.strong_induction_on

protected theorem case_strong_induction_on {p : Nat → Prop} (a : Nat) (hz : p 0)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
  Nat.strong_induction_on a fun n =>
    match n with
    | 0 => fun _ => hz
    | n + 1 => fun h₁ => hi n fun _m h₂ => h₁ _ (lt_succ_of_le h₂)
#align nat.case_strong_induction_on Nat.case_strong_induction_on

/-! mod -/

#align nat.mod_def Nat.mod_eq

#align nat.mod_zero Nat.mod_zero

#align nat.mod_eq_of_lt Nat.mod_eq_of_lt

#align nat.zero_mod Nat.zero_mod

#align nat.mod_eq_sub_mod Nat.mod_eq_sub_mod

#align nat.mod_lt Nat.mod_lt

#align nat.mod_self Nat.mod_self

#align nat.mod_one Nat.mod_one

#align nat.mod_two_eq_zero_or_one Nat.mod_two_eq_zero_or_one

#align nat.mod_le Nat.mod_le

#align nat.add_mod_right Nat.add_mod_right

#align nat.add_mod_left Nat.add_mod_left

#align nat.add_mul_mod_self_left Nat.add_mul_mod_self_left

#align nat.add_mul_mod_self_right Nat.add_mul_mod_self_right

#align nat.mul_mod_right Nat.mul_mod_right

#align nat.mul_mod_left Nat.mul_mod_left

#align nat.mul_mod_mul_left Nat.mul_mod_mul_left

#align nat.mul_mod_mul_right Nat.mul_mod_mul_right

theorem cond_decide_mod_two (x : ℕ) [d : Decidable (x % 2 = 1)] :
    cond (@decide (x % 2 = 1) d) 1 0 = x % 2 := by
  by_cases h : x % 2 = 1
  · simp! [*]
  · cases mod_two_eq_zero_or_one x <;> simp! [*, Nat.zero_ne_one]
#align nat.cond_to_bool_mod_two Nat.cond_decide_mod_two

#align nat.sub_mul_mod Nat.sub_mul_mod

/-! div -/

#align nat.div_def Nat.div_eq

#align nat.mod_add_div Nat.mod_add_div

#align nat.div_one Nat.div_one

#align nat.div_zero Nat.div_zero

#align nat.zero_div Nat.zero_div

#align nat.div_le_of_le_mul Nat.div_le_of_le_mul

#align nat.div_le_self Nat.div_le_self

#align nat.div_eq_sub_div Nat.div_eq_sub_divₓ

#align nat.div_eq_of_lt Nat.div_eq_of_lt

#align nat.le_div_iff_mul_le Nat.le_div_iff_mul_le

#align nat.div_lt_iff_lt_mul Nat.div_lt_iff_lt_mul

#align nat.sub_mul_div Nat.sub_mul_div

#align nat.div_mul_le_self Nat.div_mul_le_self

#align nat.add_div_right Nat.add_div_right

#align nat.add_div_left Nat.add_div_left

#align nat.mul_div_right Nat.mul_div_right

#align nat.mul_div_left Nat.mul_div_left

#align nat.div_self Nat.div_self

#align nat.add_mul_div_left Nat.add_mul_div_left

#align nat.add_mul_div_right Nat.add_mul_div_right

#align nat.mul_div_cancel Nat.mul_div_cancel

#align nat.mul_div_cancel_left Nat.mul_div_cancel_left

#align nat.div_eq_of_eq_mul_left Nat.div_eq_of_eq_mul_leftₓ

#align nat.div_eq_of_eq_mul_right Nat.div_eq_of_eq_mul_rightₓ

#align nat.div_eq_of_lt_le Nat.div_eq_of_lt_leₓ

#align nat.mul_sub_div Nat.mul_sub_div

#align nat.div_div_eq_div_mul Nat.div_div_eq_div_mul

#align nat.mul_div_mul Nat.mul_div_mul_left

#align nat.div_lt_self Nat.div_lt_self

/-! dvd -/


#align nat.dvd_mul_right Nat.dvd_mul_right

#align nat.dvd_trans Nat.dvd_trans

#align nat.eq_zero_of_zero_dvd Nat.eq_zero_of_zero_dvd

#align nat.dvd_add Nat.dvd_add

#align nat.dvd_add_iff_right Nat.dvd_add_iff_right

#align nat.dvd_add_iff_left Nat.dvd_add_iff_left

#align nat.dvd_sub Nat.dvd_sub

#align nat.dvd_mod_iff Nat.dvd_mod_iff

#align nat.le_of_dvd Nat.le_of_dvd

#align nat.dvd_antisymm Nat.dvd_antisymm

#align nat.pos_of_dvd_of_pos Nat.pos_of_dvd_of_pos

#align nat.eq_one_of_dvd_one Nat.eq_one_of_dvd_one

#align nat.dvd_of_mod_eq_zero Nat.dvd_of_mod_eq_zero

#align nat.mod_eq_zero_of_dvd Nat.mod_eq_zero_of_dvd

#align nat.dvd_iff_mod_eq_zero Nat.dvd_iff_mod_eq_zero

#align nat.decidable_dvd Nat.decidable_dvd

#align nat.mul_div_cancel' Nat.mul_div_cancel'ₓ

#align nat.div_mul_cancel Nat.div_mul_cancelₓ

#align nat.mul_div_assoc Nat.mul_div_assocₓ

#align nat.dvd_of_mul_dvd_mul_left Nat.dvd_of_mul_dvd_mul_leftₓ

#align nat.dvd_of_mul_dvd_mul_right Nat.dvd_of_mul_dvd_mul_rightₓ

-- TODO: move to Std
variable {m n : ℕ}

lemma succ_le_iff : succ m ≤ n ↔ m < n := ⟨lt_of_succ_le, succ_le_of_lt⟩
#align nat.succ_le_iff Nat.succ_le_iff

end Nat
