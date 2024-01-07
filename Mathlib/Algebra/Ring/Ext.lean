/-
Copyright (c) 2023 Raghuram Sundararajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raghuram Sundararajan
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Ext
-- import Mathlib

/-!
# Extensionality lemmas for rings and similar structures

In this file we prove extensionality lemmas for the ring-like structures defined in
`Algebra/Ring/Defs`, ranging from `NonUnitalNonAssocSemiring` to `CommRing`. These extensionality
lemmas take the form of asserting that two algebraic structures on a type are equal whenever the
addition and multiplication defined by them are both the same.

## Implementation details

We follow `Algebra/Group/Ext` in using the term `(letI := i; HMul.hMul : R → R → R)` to refer to the
multiplcation specified by a typeclass instance `i` on a type `R` (and similarly for addition).

We use hypotheses for ext lemmas of an extensional form, stating that the operations agree on all
arguments.

Since `Algebra/Group/Ext` proved several injectivity lemmas, we do so as well — even if sometimes we
don't need them to prove extensionality.

## Tags
semiring, ring, extensionality
-/

universe u

variable {R : Type u}

/-!
### Notational abbreviations

Since there is not a lot of variation in these results outside of the proof of the `ext` lemma
itself, we use local notations and a macro to abbreviate.

Specifically, we define the following local notations:
+ `AddEq[inst₁, inst₂]` states that the instances `inst₁` and `inst₂` of suitable algebraic
  typeclasses (on R) define the same addition operation.
+ `MulEq[inst₁, inst₂]` states that the instances `inst₁` and `inst₂` of suitable algebraic
  typeclasses (on R) define the same multiplication operation.
+ `ext_theorems <proof>` is a wrapper generating the `ext` and `ext_iff` theorems for the typeclass
  named by the currently open namespace. All that it needs to be provided is the proof of the `ext`
  result itself, showing that two instances `inst₁` and `inst₂` are equal, assuming that they define
  the same addition and multiplication operations (hypotheses named by `h_add` and `h_mul`
  respectively).

  `ext_theorems` is unhygienic, which is OK since it is only used in this file, and the name
  captures are entirely intentional.
-/

/-- `AddEq[inst₁, inst₂]` states that `inst₁` and `inst₂` define the same addition operation.

`inst₁` and `inst₂` should be instances of classes which induce a `HAdd` instance on `R`. -/
local macro "AddEq[" inst₁:term ", " inst₂:term "]" : term =>
  `(term| ∀ x y : R, (letI := $inst₁; x + y : R) = (letI := $inst₂; x + y))

/-- `MulEq[inst₁, inst₂]` states that `inst₁` and `inst₂` define the same multiplication operation.

`inst₁` and `inst₂` should be instances of classes which induce a `HMul` instance on `R`. -/
local macro "MulEq[" inst₁:term ", " inst₂:term "]" : term =>
  `(term| ∀ x y : R, (letI := $inst₁; x * y : R) = (letI := $inst₂; x * y))

/-- `ext_theorems` generates `ext` and `ext_iff` lemmas for the class named by the current namespace.

It should be followed by a proof that two instances of the class are equal, assuming that they
define the same addition and multiplication operations. The instances will be named `inst₁` and
`inst₂`, and the hypotheses that they define the same operations will be named `h_add` and `h_mul`
respectively. -/
local elab "ext_theorems " val:declVal : command =>
  Lean.Elab.Command.elabCommand =<<
    set_option hygiene false in do
      `(@[ext] theorem ext ⦃inst₁ inst₂ : $(Lean.mkCIdent <| ← Lean.getCurrNamespace) R⦄
            (h_add : AddEq[inst₁, inst₂]) (h_mul : MulEq[inst₁, inst₂]) :
            inst₁ = inst₂ $val:declVal
        theorem ext_iff (inst₁ inst₂ : $(Lean.mkCIdent <| ← Lean.getCurrNamespace) R) :
          inst₁ = inst₂ ↔ AddEq[inst₁, inst₂] ∧ MulEq[inst₁, inst₂] :=
        ⟨fun h ↦ by constructor <;> (intros; congr), And.elim («ext» · ·)⟩)

/-! ### Distrib -/
namespace Distrib

ext_theorems := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr <;> (apply funext₂; assumption)

end Distrib

/-! ### NonUnitalNonAssocSemiring -/
namespace NonUnitalNonAssocSemiring

ext_theorems := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr <;> (ext; apply_assumption)

theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocSemiring

/-! ### NonUnitalSemiring -/
namespace NonUnitalSemiring

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalSemiring

/-! ### NonAssocSemiring -/
namespace NonAssocSemiring

/- The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Algebra/GroupWithZero/Defs` as well. -/
ext_theorems := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext <;> apply_assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZeroOneClass).toMulOneClass.toOne
                = (inst₂.toMulZeroOneClass).toMulOneClass.toOne :=
    congrArg (@MulOneClass.toOne R) <| by
      ext; apply h_mul
  have h_one : (inst₁.toMulZeroOneClass).toMulOneClass.toOne.one
               = (inst₂.toMulZeroOneClass).toMulOneClass.toOne.one :=
    congrArg (@One.one R) h_one'
  -- Mathematically non-trivial fact: `natCast` is determined by `0`, `1` and `+`.
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCast := by
    funext n; induction n with
    | zero     => rewrite [inst₁.natCast_zero, inst₂.natCast_zero]; exact h_zero
    | succ n h => rw [inst₁.natCast_succ, inst₂.natCast_succ, h_add]
                  exact congrArg₂ _ h h_one
  -- Split into `NonUnitalNonAssocSemiring`, `One` instances, `natCast` function and properties.
  rcases inst₁ with @⟨_, _, _, _, ⟨⟩⟩; rcases inst₂ with @⟨_, _, _, _, ⟨⟩⟩
  -- Prove equality of parts using the above lemmas.
  congr

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

end NonAssocSemiring

/-! ### NonUnitalNonAssocRing -/
namespace NonUnitalNonAssocRing

ext_theorems := by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr <;> (ext; apply_assumption)

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocRing

/-! ### NonUnitalRing -/
namespace NonUnitalRing

ext_theorems := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext <;> apply_assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonUnitalRing

/-! ### NonAssocRing -/
namespace NonAssocRing

ext_theorems := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext <;> apply_assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h_intCast : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    have : inst₁.toNatCast = inst₂.toNatCast := by injection h₂
    funext n; cases n with
    | ofNat n   => rewrite [←Int.coe_nat_eq, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  -- Split into fields (extracting `intCast` function) and prove they are equal using the above.
  rcases inst₁ with @⟨_, _, _, _, _, _, _, ⟨⟩⟩
  rcases inst₂ with @⟨_, _, _, _, _, _, _, ⟨⟩⟩
  congr <;> try solve| injection h₁ | injection h₂

theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonAssocRing

/-! ### Semiring -/
namespace Semiring

ext_theorems := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext <;> apply_assumption
  have h₃ : (inst₁.toMonoidWithZero).toMonoid = (inst₂.toMonoidWithZero).toMonoid := by
    ext; apply h_mul
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve| injection h₁ | injection h₂ | injection h₃

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Semiring

/-! ### Ring -/
namespace Ring

ext_theorems := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext <;> apply_assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field away from `Sub` and `Neg`, enabling use of `injection`. -/
  have h₃ : (inst₁.toAddCommGroup).toAddGroup.toSubNegMonoid
            = (inst₂.toAddCommGroup).toAddGroup.toSubNegMonoid :=
    congrArg (@AddGroup.toSubNegMonoid R) <| by ext; apply h_add
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₂ | injection h₃

theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonAssocRing_injective :
    Function.Injective (@toNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Ring

/-! ### NonUnitalNonAssocCommSemiring -/
namespace NonUnitalNonAssocCommSemiring

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalNonAssocCommSemiring

/-! ### NonUnitalCommSemiring -/
namespace NonUnitalCommSemiring

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toNonUnitalSemiring_injective <|
    NonUnitalSemiring.ext h_add h_mul

end NonUnitalCommSemiring

-- At present, there is no `NonAssocCommSemiring` in Mathlib.

/-! ### NonUnitalNonAssocCommRing -/
namespace NonUnitalNonAssocCommRing

theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toNonUnitalNonAssocRing_injective <|
    NonUnitalNonAssocRing.ext h_add h_mul

end NonUnitalNonAssocCommRing

/-! ### NonUnitalCommRing -/
namespace NonUnitalCommRing

theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toNonUnitalRing_injective <|
    NonUnitalRing.ext h_add h_mul

end NonUnitalCommRing

-- At present, there is no `NonAssocCommRing` in Mathlib.

/-! ### CommSemiring -/
namespace CommSemiring

theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toSemiring_injective <|
    Semiring.ext h_add h_mul

end CommSemiring

/-! ### CommRing -/
namespace CommRing

theorem toRing_injective : Function.Injective (@toRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

ext_theorems :=
  toRing_injective <| Ring.ext h_add h_mul

end CommRing
