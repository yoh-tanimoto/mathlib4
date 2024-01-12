/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Associated

#align_import algebra.associated from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# Associated, prime, and irreducible elements.
-/

/-- Notation for two elements of a monoid are associated, i.e.
if one of them is another one multiplied by a unit on the right.-/
local infixl:50 " ~ᵤ " => Associated

attribute [local instance] Associated.setoid

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- The quotient of a monoid by the `Associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `Associates α`. -/
abbrev Associates (α : Type*) [Monoid α] : Type _ :=
  Quotient (Associated.setoid α)
#align associates Associates

namespace Associates

open Associated

/-- The canonical quotient map from a monoid `α` into the `Associates` of `α` -/
protected abbrev mk {α : Type*} [Monoid α] (a : α) : Associates α :=
  ⟦a⟧
#align associates.mk Associates.mk

instance [Monoid α] : Inhabited (Associates α) :=
  ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_associated [Monoid α] {a b : α} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b :=
  Iff.intro Quotient.exact Quot.sound
#align associates.mk_eq_mk_iff_associated Associates.mk_eq_mk_iff_associated

theorem quotient_mk_eq_mk [Monoid α] (a : α) : ⟦a⟧ = Associates.mk a :=
  rfl
#align associates.quotient_mk_eq_mk Associates.quotient_mk_eq_mk

theorem quot_mk_eq_mk [Monoid α] (a : α) : Quot.mk Setoid.r a = Associates.mk a :=
  rfl
#align associates.quot_mk_eq_mk Associates.quot_mk_eq_mk

@[simp]
theorem quot_out [Monoid α] (a : Associates α) : Associates.mk (Quot.out a) = a := by
  rw [← quot_mk_eq_mk, Quot.out_eq]
#align associates.quot_out Associates.quot_outₓ

theorem forall_associated [Monoid α] {p : Associates α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (Associates.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h
#align associates.forall_associated Associates.forall_associated

theorem mk_surjective [Monoid α] : Function.Surjective (@Associates.mk α _) :=
  forall_associated.2 fun a => ⟨a, rfl⟩
#align associates.mk_surjective Associates.mk_surjective

instance [Monoid α] : One (Associates α) :=
  ⟨⟦1⟧⟩

@[simp]
theorem mk_one [Monoid α] : Associates.mk (1 : α) = 1 :=
  rfl
#align associates.mk_one Associates.mk_one

theorem one_eq_mk_one [Monoid α] : (1 : Associates α) = Associates.mk 1 :=
  rfl
#align associates.one_eq_mk_one Associates.one_eq_mk_one

instance [Monoid α] : Bot (Associates α) :=
  ⟨1⟩

theorem bot_eq_one [Monoid α] : (⊥ : Associates α) = 1 :=
  rfl
#align associates.bot_eq_one Associates.bot_eq_one

theorem exists_rep [Monoid α] (a : Associates α) : ∃ a0 : α, Associates.mk a0 = a :=
  Quot.exists_rep a
#align associates.exists_rep Associates.exists_rep

instance [Monoid α] [Subsingleton α] :
    Unique (Associates α) where
  default := 1
  uniq a := by
    apply Quotient.recOnSubsingleton₂
    intro a b
    congr
    simp [eq_iff_true_of_subsingleton]

theorem mk_injective [Monoid α] [Unique (Units α)] : Function.Injective (@Associates.mk α _) :=
  fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)
#align associates.mk_injective Associates.mk_injective

section CommMonoid

variable [CommMonoid α]

instance instMul : Mul (Associates α) :=
  ⟨fun a' b' =>
    (Quotient.liftOn₂ a' b' fun a b => ⟦a * b⟧) fun a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ =>
      Quotient.sound <| ⟨c₁ * c₂, by
        rw [← h₁, ← h₂]
        simp only [Units.val_mul, mul_left_comm, mul_comm]⟩⟩

theorem mk_mul_mk {x y : α} : Associates.mk x * Associates.mk y = Associates.mk (x * y) :=
  rfl
#align associates.mk_mul_mk Associates.mk_mul_mk

instance instCommMonoid : CommMonoid (Associates α) where
  one := 1
  mul := (· * ·)
  mul_one a' := Quotient.inductionOn a' fun a => show ⟦a * 1⟧ = ⟦a⟧ by simp
  one_mul a' := Quotient.inductionOn a' fun a => show ⟦1 * a⟧ = ⟦a⟧ by simp
  mul_assoc a' b' c' :=
    Quotient.inductionOn₃ a' b' c' fun a b c =>
      show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by rw [mul_assoc]
  mul_comm a' b' :=
    Quotient.inductionOn₂ a' b' fun a b => show ⟦a * b⟧ = ⟦b * a⟧ by rw [mul_comm]

instance instPreorder : Preorder (Associates α) where
  le := Dvd.dvd
  le_refl := dvd_refl
  le_trans a b c := dvd_trans

/-- `Associates.mk` as a `MonoidHom`. -/
protected def mkMonoidHom : α →* Associates α :=
  {
    toFun := Associates.mk
    map_one' := mk_one
    map_mul' := fun _ _ => mk_mul_mk}
#align associates.mk_monoid_hom Associates.mkMonoidHom

@[simp]
theorem mkMonoidHom_apply (a : α) : Associates.mkMonoidHom a = Associates.mk a :=
  rfl
#align associates.mk_monoid_hom_apply Associates.mkMonoidHom_apply

theorem associated_map_mk {f : Associates α →* α} (hinv : Function.RightInverse f Associates.mk)
    (a : α) : a ~ᵤ f (Associates.mk a) :=
  Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm
#align associates.associated_map_mk Associates.associated_map_mk

theorem mk_pow (a : α) (n : ℕ) : Associates.mk (a ^ n) = Associates.mk a ^ n := by
  induction n <;> simp [*, pow_succ, Associates.mk_mul_mk.symm]
#align associates.mk_pow Associates.mk_pow

theorem dvd_eq_le : ((· ∣ ·) : Associates α → Associates α → Prop) = (· ≤ ·) :=
  rfl
#align associates.dvd_eq_le Associates.dvd_eq_le

theorem mul_eq_one_iff {x y : Associates α} : x * y = 1 ↔ x = 1 ∧ y = 1 :=
  Iff.intro
    (Quotient.inductionOn₂ x y fun a b h =>
      have : a * b ~ᵤ 1 := Quotient.exact h
      ⟨Quotient.sound <| associated_one_of_associated_mul_one this,
        Quotient.sound <| associated_one_of_associated_mul_one <| by rwa [mul_comm] at this⟩)
    (by simp (config := { contextual := true }))
#align associates.mul_eq_one_iff Associates.mul_eq_one_iff

theorem units_eq_one (u : (Associates α)ˣ) : u = 1 :=
  Units.ext (mul_eq_one_iff.1 u.val_inv).1
#align associates.units_eq_one Associates.units_eq_one

instance uniqueUnits : Unique (Associates α)ˣ where
  default := 1
  uniq := Associates.units_eq_one
#align associates.unique_units Associates.uniqueUnits

@[simp]
theorem coe_unit_eq_one (u : (Associates α)ˣ) : (u : Associates α) = 1 := by
  simp [eq_iff_true_of_subsingleton]
#align associates.coe_unit_eq_one Associates.coe_unit_eq_one

theorem isUnit_iff_eq_one (a : Associates α) : IsUnit a ↔ a = 1 :=
  Iff.intro (fun ⟨_, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ isUnit_one
#align associates.is_unit_iff_eq_one Associates.isUnit_iff_eq_one

theorem isUnit_iff_eq_bot {a : Associates α} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one, bot_eq_one]
#align associates.is_unit_iff_eq_bot Associates.isUnit_iff_eq_bot

theorem isUnit_mk {a : α} : IsUnit (Associates.mk a) ↔ IsUnit a :=
  calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [isUnit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit
#align associates.is_unit_mk Associates.isUnit_mk

section Order

theorem mul_mono {a b c d : Associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_assoc, mul_left_comm]⟩
#align associates.mul_mono Associates.mul_mono

theorem one_le {a : Associates α} : 1 ≤ a :=
  Dvd.intro _ (one_mul a)
#align associates.one_le Associates.one_le

theorem le_mul_right {a b : Associates α} : a ≤ a * b :=
  ⟨b, rfl⟩
#align associates.le_mul_right Associates.le_mul_right

theorem le_mul_left {a b : Associates α} : a ≤ b * a := by rw [mul_comm]; exact le_mul_right
#align associates.le_mul_left Associates.le_mul_left

instance instOrderBot : OrderBot (Associates α) where
  bot := 1
  bot_le _ := one_le

end Order

theorem dvd_of_mk_le_mk {a b : α} : Associates.mk a ≤ Associates.mk b → a ∣ b
  | ⟨c', hc'⟩ =>
    let step : ∀ (c : α),
      Associates.mk b = Associates.mk a * Quotient.mk (Associated.setoid α) c → a ∣ b := by
      intro c hc
      let ⟨d, hd⟩ := (Quotient.exact hc).symm
      exact ⟨↑d * c,
          calc
            b = a * c * ↑d := hd.symm
            _ = a * (↑d * c) := by ac_rfl
            ⟩
    Quotient.inductionOn c' step hc'
#align associates.dvd_of_mk_le_mk Associates.dvd_of_mk_le_mk

theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → Associates.mk a ≤ Associates.mk b := fun ⟨c, hc⟩ =>
  ⟨Associates.mk c, by simp [hc]; rfl⟩
#align associates.mk_le_mk_of_dvd Associates.mk_le_mk_of_dvd

theorem mk_le_mk_iff_dvd_iff {a b : α} : Associates.mk a ≤ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd
#align associates.mk_le_mk_iff_dvd_iff Associates.mk_le_mk_iff_dvd_iff

theorem mk_dvd_mk {a b : α} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd
#align associates.mk_dvd_mk Associates.mk_dvd_mk

end CommMonoid

instance [Zero α] [Monoid α] : Zero (Associates α) :=
  ⟨⟦0⟧⟩

instance [Zero α] [Monoid α] : Top (Associates α) :=
  ⟨0⟩

section MonoidWithZero

variable [MonoidWithZero α]

@[simp]
theorem mk_eq_zero {a : α} : Associates.mk a = 0 ↔ a = 0 :=
  ⟨fun h => (associated_zero_iff_eq_zero a).1 <| Quotient.exact h, fun h => h.symm ▸ rfl⟩
#align associates.mk_eq_zero Associates.mk_eq_zero

theorem mk_ne_zero {a : α} : Associates.mk a ≠ 0 ↔ a ≠ 0 :=
  not_congr mk_eq_zero
#align associates.mk_ne_zero Associates.mk_ne_zero

instance [Nontrivial α] : Nontrivial (Associates α) :=
  ⟨⟨0, 1, fun h =>
      have : (0 : α) ~ᵤ 1 := Quotient.exact h
      have : (0 : α) = 1 := ((associated_zero_iff_eq_zero 1).1 this.symm).symm
      zero_ne_one this⟩⟩

theorem exists_non_zero_rep {a : Associates α} : a ≠ 0 → ∃ a0 : α, a0 ≠ 0 ∧ Associates.mk a0 = a :=
  Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk'') nz, rfl⟩
#align associates.exists_non_zero_rep Associates.exists_non_zero_rep

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero α]

instance instCommMonoidWithZero : CommMonoidWithZero (Associates α) where
    zero_mul := by
      rintro ⟨a⟩
      show Associates.mk (0 * a) = Associates.mk 0
      rw [zero_mul]
    mul_zero := by
      rintro ⟨a⟩
      show Associates.mk (a * 0) = Associates.mk 0
      rw [mul_zero]

instance instOrderTop : OrderTop (Associates α) where
  top := 0
  le_top a := ⟨0, (mul_zero a).symm⟩

instance instBoundedOrder : BoundedOrder (Associates α) where

instance [DecidableRel ((· ∣ ·) : α → α → Prop)] :
    DecidableRel ((· ∣ ·) : Associates α → Associates α → Prop) := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun _ _ => decidable_of_iff' _ mk_dvd_mk

theorem Prime.le_or_le {p : Associates α} (hp : Prime p) {a b : Associates α} (h : p ≤ a * b) :
    p ≤ a ∨ p ≤ b :=
  hp.2.2 a b h
#align associates.prime.le_or_le Associates.Prime.le_or_le

theorem prime_mk (p : α) : Prime (Associates.mk p) ↔ Prime p := by
  rw [Prime, _root_.Prime, forall_associated]
  trans
  · apply and_congr
    rfl
    apply and_congr
    rfl
    apply forall_congr'
    intro a
    exact forall_associated
  apply and_congr mk_ne_zero
  apply and_congr
  · rw [isUnit_mk]
  refine' forall₂_congr fun a b => _
  rw [mk_mul_mk, mk_dvd_mk, mk_dvd_mk, mk_dvd_mk]
#align associates.prime_mk Associates.prime_mk

theorem irreducible_mk (a : α) : Irreducible (Associates.mk a) ↔ Irreducible a := by
  simp only [irreducible_iff, isUnit_mk]
  apply and_congr Iff.rfl
  constructor
  · rintro h x y rfl
    simpa [isUnit_mk] using h (Associates.mk x) (Associates.mk y) rfl
  · intro h x y
    refine' Quotient.inductionOn₂ x y fun x y a_eq => _
    rcases Quotient.exact a_eq.symm with ⟨u, a_eq⟩
    rw [mul_assoc] at a_eq
    show IsUnit (Associates.mk x) ∨ IsUnit (Associates.mk y)
    simpa [isUnit_mk] using h _ _ a_eq.symm
#align associates.irreducible_mk Associates.irreducible_mk

theorem mk_dvdNotUnit_mk_iff {a b : α} :
    DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b := by
  rw [DvdNotUnit, DvdNotUnit, mk_ne_zero]
  apply and_congr_right; intro
  constructor
  · contrapose!
    rw [forall_associated]
    intro h x hx hbax
    rw [mk_mul_mk, mk_eq_mk_iff_associated] at hbax
    cases' hbax with u hu
    apply h (x * ↑u⁻¹)
    · rw [isUnit_mk] at hx
      rw [Associated.isUnit_iff]
      apply hx
      use u
      simp
    simp [← mul_assoc, ← hu]
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use Associates.mk x
    simp [isUnit_mk, mk_mul_mk, hx]
#align associates.mk_dvd_not_unit_mk_iff Associates.mk_dvdNotUnit_mk_iff

theorem dvdNotUnit_of_lt {a b : Associates α} (hlt : a < b) : DvdNotUnit a b := by
  constructor;
  · rintro rfl
    apply not_lt_of_le _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine' ⟨x, _, rfl⟩
  contrapose! ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp
#align associates.dvd_not_unit_of_lt Associates.dvdNotUnit_of_lt

theorem irreducible_iff_prime_iff :
    (∀ a : α, Irreducible a ↔ Prime a) ↔ ∀ a : Associates α, Irreducible a ↔ Prime a := by
  simp_rw [forall_associated, irreducible_mk, prime_mk]
#align associates.irreducible_iff_prime_iff Associates.irreducible_iff_prime_iff

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

instance instPartialOrder : PartialOrder (Associates α) where
    le_antisymm := fun a' b' =>
      Quotient.inductionOn₂ a' b' fun _ _ hab hba =>
        Quot.sound <| associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba)

instance instOrderedCommMonoid : OrderedCommMonoid (Associates α) where
    mul_le_mul_left := fun a _ ⟨d, hd⟩ c => hd.symm ▸ mul_assoc c a d ▸ le_mul_right

instance instCancelCommMonoidWithZero : CancelCommMonoidWithZero (Associates α) :=
{ (by infer_instance : CommMonoidWithZero (Associates α)) with
  mul_left_cancel_of_ne_zero := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h
    rcases Quotient.exact' h with ⟨u, hu⟩
    have hu : a * (b * ↑u) = a * c := by rwa [← mul_assoc]
    exact Quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩ }

instance : NoZeroDivisors (Associates α) := by infer_instance

theorem le_of_mul_le_mul_left (a b c : Associates α) (ha : a ≠ 0) : a * b ≤ a * c → b ≤ c
  | ⟨d, hd⟩ => ⟨d, mul_left_cancel₀ ha <| by rwa [← mul_assoc]⟩
#align associates.le_of_mul_le_mul_left Associates.le_of_mul_le_mul_left

theorem one_or_eq_of_le_of_prime : ∀ p m : Associates α, Prime p → m ≤ p → m = 1 ∨ m = p
  | p, m, ⟨hp0, _, h⟩, ⟨d, r⟩ => by
    have dvd_rfl' : p ∣ m * d := by rw[r]
    rw [r]
    match h m d dvd_rfl' with
    | Or.inl h' =>
      if h : m = 0 then
        simp [h, zero_mul]
      else
        rw [r] at h'
        have : m * d ≤ m * 1 := by simpa using h'
        have : d ≤ 1 := Associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this
        have : d = 1 := bot_unique this
        simp [this]
    | Or.inr h' =>
      if h : d = 0 then
        rw [r] at hp0
        have : m * d = 0 := by rw [h]; simp
        contradiction
      else
        rw [r] at h'
        have : d * m ≤ d * 1 := by simpa [mul_comm] using h'
        exact Or.inl <| bot_unique <| Associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this
#align associates.one_or_eq_of_le_of_prime Associates.one_or_eq_of_le_of_prime

instance : CanonicallyOrderedCommMonoid (Associates α) where
  exists_mul_of_le := fun h => h
  le_self_mul := fun _ b => ⟨b, rfl⟩
  bot_le := fun _ => one_le

theorem dvdNotUnit_iff_lt {a b : Associates α} : DvdNotUnit a b ↔ a < b :=
  dvd_and_not_dvd_iff.symm
#align associates.dvd_not_unit_iff_lt Associates.dvdNotUnit_iff_lt

theorem le_one_iff {p : Associates α} : p ≤ 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]
#align associates.le_one_iff Associates.le_one_iff

end CancelCommMonoidWithZero

end Associates

assert_not_exists Multiset
