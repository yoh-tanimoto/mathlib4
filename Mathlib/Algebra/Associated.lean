/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.GroupPower.Ring

#align_import algebra.associated from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# Associated, prime, and irreducible elements.
-/


variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Two elements of a `Monoid` are `Associated` if one of them is another one
multiplied by a unit on the right. -/
def Associated [Monoid α] (x y : α) : Prop :=
  ∃ u : αˣ, x * u = y
#align associated Associated

/-- Notation for two elements of a monoid are associated, i.e.
if one of them is another one multiplied by a unit on the right.-/
local infixl:50 " ~ᵤ " => Associated

namespace Associated

@[refl]
protected theorem refl [Monoid α] (x : α) : x ~ᵤ x :=
  ⟨1, by simp⟩
#align associated.refl Associated.refl

instance [Monoid α] : IsRefl α Associated :=
  ⟨Associated.refl⟩

@[symm]
protected theorem symm [Monoid α] : ∀ {x y : α}, x ~ᵤ y → y ~ᵤ x
  | x, _, ⟨u, rfl⟩ => ⟨u⁻¹, by rw [mul_assoc, Units.mul_inv, mul_one]⟩
#align associated.symm Associated.symm

instance [Monoid α] : IsSymm α Associated :=
  ⟨fun _ _ => Associated.symm⟩

protected theorem comm [Monoid α] {x y : α} : x ~ᵤ y ↔ y ~ᵤ x :=
  ⟨Associated.symm, Associated.symm⟩
#align associated.comm Associated.comm

@[trans]
protected theorem trans [Monoid α] : ∀ {x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
  | x, _, _, ⟨u, rfl⟩, ⟨v, rfl⟩ => ⟨u * v, by rw [Units.val_mul, mul_assoc]⟩
#align associated.trans Associated.trans

instance [Monoid α] : IsTrans α Associated :=
  ⟨fun _ _ _ => Associated.trans⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def setoid (α : Type*) [Monoid α] :
    Setoid α where
  r := Associated
  iseqv := ⟨Associated.refl, Associated.symm, Associated.trans⟩
#align associated.setoid Associated.setoid

end Associated

theorem unit_associated_one [Monoid α] {u : αˣ} : (u : α) ~ᵤ 1 :=
  ⟨u⁻¹, Units.mul_inv u⟩
#align unit_associated_one unit_associated_one

theorem associated_one_iff_isUnit [Monoid α] {a : α} : (a : α) ~ᵤ 1 ↔ IsUnit a :=
  Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mul _).symm⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩
#align associated_one_iff_is_unit associated_one_iff_isUnit

theorem associated_zero_iff_eq_zero [MonoidWithZero α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
  Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a
#align associated_zero_iff_eq_zero associated_zero_iff_eq_zero

theorem associated_one_of_mul_eq_one [CommMonoid α] {a : α} (b : α) (hab : a * b = 1) : a ~ᵤ 1 :=
  show (Units.mkOfMulEqOne a b hab : α) ~ᵤ 1 from unit_associated_one
#align associated_one_of_mul_eq_one associated_one_of_mul_eq_one

theorem associated_one_of_associated_mul_one [CommMonoid α] {a b : α} : a * b ~ᵤ 1 → a ~ᵤ 1
  | ⟨u, h⟩ => associated_one_of_mul_eq_one (b * u) <| by simpa [mul_assoc] using h
#align associated_one_of_associated_mul_one associated_one_of_associated_mul_one

theorem associated_mul_unit_left {β : Type*} [Monoid β] (a u : β) (hu : IsUnit u) :
    Associated (a * u) a :=
  let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩
#align associated_mul_unit_left associated_mul_unit_left

theorem associated_unit_mul_left {β : Type*} [CommMonoid β] (a u : β) (hu : IsUnit u) :
    Associated (u * a) a := by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu
#align associated_unit_mul_left associated_unit_mul_left

theorem associated_mul_unit_right {β : Type*} [Monoid β] (a u : β) (hu : IsUnit u) :
    Associated a (a * u) :=
  (associated_mul_unit_left a u hu).symm
#align associated_mul_unit_right associated_mul_unit_right

theorem associated_unit_mul_right {β : Type*} [CommMonoid β] (a u : β) (hu : IsUnit u) :
    Associated a (u * a) :=
  (associated_unit_mul_left a u hu).symm
#align associated_unit_mul_right associated_unit_mul_right

theorem associated_mul_isUnit_left_iff {β : Type*} [Monoid β] {a u b : β} (hu : IsUnit u) :
    Associated (a * u) b ↔ Associated a b :=
  ⟨(associated_mul_unit_right _ _ hu).trans, (associated_mul_unit_left _ _ hu).trans⟩
#align associated_mul_is_unit_left_iff associated_mul_isUnit_left_iff

theorem associated_isUnit_mul_left_iff {β : Type*} [CommMonoid β] {u a b : β} (hu : IsUnit u) :
    Associated (u * a) b ↔ Associated a b := by
  rw [mul_comm]
  exact associated_mul_isUnit_left_iff hu
#align associated_is_unit_mul_left_iff associated_isUnit_mul_left_iff

theorem associated_mul_isUnit_right_iff {β : Type*} [Monoid β] {a b u : β} (hu : IsUnit u) :
    Associated a (b * u) ↔ Associated a b :=
  Associated.comm.trans <| (associated_mul_isUnit_left_iff hu).trans Associated.comm
#align associated_mul_is_unit_right_iff associated_mul_isUnit_right_iff

theorem associated_isUnit_mul_right_iff {β : Type*} [CommMonoid β] {a u b : β} (hu : IsUnit u) :
    Associated a (u * b) ↔ Associated a b :=
  Associated.comm.trans <| (associated_isUnit_mul_left_iff hu).trans Associated.comm
#align associated_is_unit_mul_right_iff associated_isUnit_mul_right_iff

@[simp]
theorem associated_mul_unit_left_iff {β : Type*} [Monoid β] {a b : β} {u : Units β} :
    Associated (a * u) b ↔ Associated a b :=
  associated_mul_isUnit_left_iff u.isUnit
#align associated_mul_unit_left_iff associated_mul_unit_left_iff

@[simp]
theorem associated_unit_mul_left_iff {β : Type*} [CommMonoid β] {a b : β} {u : Units β} :
    Associated (↑u * a) b ↔ Associated a b :=
  associated_isUnit_mul_left_iff u.isUnit
#align associated_unit_mul_left_iff associated_unit_mul_left_iff

@[simp]
theorem associated_mul_unit_right_iff {β : Type*} [Monoid β] {a b : β} {u : Units β} :
    Associated a (b * u) ↔ Associated a b :=
  associated_mul_isUnit_right_iff u.isUnit
#align associated_mul_unit_right_iff associated_mul_unit_right_iff

@[simp]
theorem associated_unit_mul_right_iff {β : Type*} [CommMonoid β] {a b : β} {u : Units β} :
    Associated a (↑u * b) ↔ Associated a b :=
  associated_isUnit_mul_right_iff u.isUnit
#align associated_unit_mul_right_iff associated_unit_mul_right_iff

theorem Associated.mul_mul [CommMonoid α] {a₁ a₂ b₁ b₂ : α} :
    a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → a₁ * a₂ ~ᵤ b₁ * b₂
  | ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ => ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩
#align associated.mul_mul Associated.mul_mul

theorem Associated.mul_left [CommMonoid α] (a : α) {b c : α} (h : b ~ᵤ c) : a * b ~ᵤ a * c :=
  (Associated.refl a).mul_mul h
#align associated.mul_left Associated.mul_left

theorem Associated.mul_right [CommMonoid α] {a b : α} (h : a ~ᵤ b) (c : α) : a * c ~ᵤ b * c :=
  h.mul_mul (Associated.refl c)
#align associated.mul_right Associated.mul_right

theorem Associated.pow_pow [CommMonoid α] {a b : α} {n : ℕ} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n := by
  induction' n with n ih
  · simp [h]; rfl
  convert h.mul_mul ih <;> rw [pow_succ]
#align associated.pow_pow Associated.pow_pow

protected theorem Associated.dvd [Monoid α] {a b : α} : a ~ᵤ b → a ∣ b := fun ⟨u, hu⟩ =>
  ⟨u, hu.symm⟩
#align associated.dvd Associated.dvd

protected theorem Associated.dvd_dvd [Monoid α] {a b : α} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
  ⟨h.dvd, h.symm.dvd⟩
#align associated.dvd_dvd Associated.dvd_dvd

theorem associated_of_dvd_dvd [CancelMonoidWithZero α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    a ~ᵤ b := by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases ha0 : a = 0
  · simp_all; rfl
  have hac0 : a * c ≠ 0 := by
    intro con
    rw [con, zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hcd : c * d = 1 := mul_left_cancel₀ ha0 this
  have : a * c * (d * c) = a * c * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hdc : d * c = 1 := mul_left_cancel₀ hac0 this
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩
#align associated_of_dvd_dvd associated_of_dvd_dvd

theorem dvd_dvd_iff_associated [CancelMonoidWithZero α] {a b : α} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
  ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩
#align dvd_dvd_iff_associated dvd_dvd_iff_associated

instance [CancelMonoidWithZero α] [DecidableRel ((· ∣ ·) : α → α → Prop)] :
    DecidableRel ((· ~ᵤ ·) : α → α → Prop) := fun _ _ => decidable_of_iff _ dvd_dvd_iff_associated

theorem Associated.dvd_iff_dvd_left [Monoid α] {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
  let ⟨_, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm
#align associated.dvd_iff_dvd_left Associated.dvd_iff_dvd_left

theorem Associated.dvd_iff_dvd_right [Monoid α] {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
  let ⟨_, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm
#align associated.dvd_iff_dvd_right Associated.dvd_iff_dvd_right

theorem Associated.eq_zero_iff [MonoidWithZero α] {a b : α} (h : a ~ᵤ b) : a = 0 ↔ b = 0 :=
  ⟨fun ha => by
    let ⟨u, hu⟩ := h
    simp [hu.symm, ha], fun hb => by
    let ⟨u, hu⟩ := h.symm
    simp [hu.symm, hb]⟩
#align associated.eq_zero_iff Associated.eq_zero_iff

theorem Associated.ne_zero_iff [MonoidWithZero α] {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
  not_congr h.eq_zero_iff
#align associated.ne_zero_iff Associated.ne_zero_iff

protected theorem Associated.isUnit [Monoid α] {a b : α} (h : a ~ᵤ b) : IsUnit a → IsUnit b :=
  let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, hu.symm]⟩
#align associated.is_unit Associated.isUnit

theorem Associated.isUnit_iff [Monoid α] {a b : α} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b :=
  ⟨h.isUnit, h.symm.isUnit⟩
#align associated.is_unit_iff Associated.isUnit_iff

theorem Associated.of_mul_left [CancelCommMonoidWithZero α] {a b c d : α} (h : a * b ~ᵤ c * d)
    (h₁ : a ~ᵤ c) (ha : a ≠ 0) : b ~ᵤ d :=
  let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : αˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv, mul_assoc c (v : α) d, mul_left_comm c, ← hu]
        simp [hv.symm, mul_assoc, mul_comm, mul_left_comm])⟩
#align associated.of_mul_left Associated.of_mul_left

theorem Associated.of_mul_right [CancelCommMonoidWithZero α] {a b c d : α} :
    a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c := by
  rw [mul_comm a, mul_comm c]; exact Associated.of_mul_left
#align associated.of_mul_right Associated.of_mul_right

section UniqueUnits

variable [Monoid α] [Unique αˣ]

theorem associated_iff_eq {x y : α} : x ~ᵤ y ↔ x = y := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [units_eq_one c, Units.val_one, mul_one]
  · rintro rfl
    rfl
#align associated_iff_eq associated_iff_eq

theorem associated_eq_eq : (Associated : α → α → Prop) = Eq := by
  ext
  rw [associated_iff_eq]
#align associated_eq_eq associated_eq_eq

end UniqueUnits

section CommMonoidWithZero

theorem DvdNotUnit.not_unit [CommMonoidWithZero α] {p q : α} (hp : DvdNotUnit p q) : ¬IsUnit q := by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (isUnit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (isUnit_iff_dvd_one.mp hc)))
#align dvd_not_unit.not_unit DvdNotUnit.not_unit

theorem dvdNotUnit_of_dvdNotUnit_associated [CommMonoidWithZero α] [Nontrivial α] {p q r : α}
    (h : DvdNotUnit p q) (h' : Associated q r) : DvdNotUnit p r := by
  obtain ⟨u, rfl⟩ := Associated.symm h'
  obtain ⟨hp, x, hx⟩ := h
  refine' ⟨hp, x * ↑u⁻¹, DvdNotUnit.not_unit ⟨u⁻¹.ne_zero, x, hx.left, mul_comm _ _⟩, _⟩
  rw [← mul_assoc, ← hx.right, mul_assoc, Units.mul_inv, mul_one]
#align dvd_not_unit_of_dvd_not_unit_associated dvdNotUnit_of_dvdNotUnit_associated

end CommMonoidWithZero

section CancelCommMonoidWithZero

theorem isUnit_of_associated_mul [CancelCommMonoidWithZero α] {p b : α} (h : Associated (p * b) p)
    (hp : p ≠ 0) : IsUnit b := by
  cases' h with a ha
  refine' isUnit_of_mul_eq_one b a ((mul_right_inj' hp).mp _)
  rwa [← mul_assoc, mul_one]
#align is_unit_of_associated_mul isUnit_of_associated_mul

theorem DvdNotUnit.not_associated [CancelCommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q) :
    ¬Associated p q := by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases (mul_right_inj' hp).mp hx' with rfl
  exact hx a.isUnit
#align dvd_not_unit.not_associated DvdNotUnit.not_associated

theorem DvdNotUnit.ne [CancelCommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q) : p ≠ q := by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  conv_lhs at hx'' => rw [← hcontra, ← mul_one p]
  rw [(mul_left_cancel₀ hp hx'').symm] at hx'
  exact hx' isUnit_one
#align dvd_not_unit.ne DvdNotUnit.ne

theorem pow_injective_of_not_unit [CancelCommMonoidWithZero α] {q : α} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) : Function.Injective fun n : ℕ => q ^ n := by
  refine' injective_of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), _, _⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm
#align pow_injective_of_not_unit pow_injective_of_not_unit

end CancelCommMonoidWithZero

assert_not_exists Multiset
