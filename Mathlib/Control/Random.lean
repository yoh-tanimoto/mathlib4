/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Order
import Mathlib.Control.ULiftable
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.ULift
import Mathlib.Logic.Equiv.Functor

#align_import control.random from "leanprover-community/mathlib"@"fdc286cc6967a012f41b87f76dcd2797b53152af"

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions

* `Rand` and `RandG` monad for computations guided by randomness;
* `Random` class for objects that can be generated randomly;
  * `random` to generate one object;
* `BoundedRandom` class for objects that can be generated randomly inside a range;
  * `randomR` to generate one object inside a range;
* `IO.runRand` to run a randomized computation inside the `IO` monad;

## References

* Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/

set_option autoImplicit true

/-- A monad transformer to generate random objects using the generic generator type `g` -/
abbrev RandG (g : Type) := StateT (ULift g)

/-- A monad transformer to generate random objects using the generator type `Rng`.
`Rand m α` should be thought of a random value in `m α`. -/
abbrev Rand := RandG StdGen

instance [MonadLift m n] : MonadLiftT (RandG g m) (RandG g n) where
  monadLift x := fun s => x s

/-- `Random α` gives us machinery to generate values of type `α` -/
class Random (α : Type u) where
  random [RandomGen g] : RandG g Id α

/-- `BoundedRandom α` gives us machinery to generate values of type `α` between certain bounds -/
class BoundedRandom (α : Type u) [Preorder α] where
  randomR {g : Type} (lo hi : α) (h : lo ≤ hi) [RandomGen g] : RandG g Id {a // lo ≤ a ∧ a ≤ hi}

namespace Rand
  /-- Generate one more `Nat` -/
  def next [RandomGen g] [Monad m] : RandG g m Nat := do
    let rng := (←get).down
    let (res, new) := RandomGen.next rng
    set (ULift.up new)
    pure res

  /-- Create a new random number generator distinct from the one stored in the state -/
  def split {g : Type} [RandomGen g] [Monad m] : RandG g m g := do
    let rng := (←get).down
    let (r1, r2) := RandomGen.split rng
    set (ULift.up r1)
    pure r2

  /-- Get the range of Nat that can be generated by the generator `g` -/
  def range {g : Type} [RandomGen g] [Monad m] : RandG g m (Nat × Nat) := do
    let rng := (←get).down
    pure <| RandomGen.range rng
end Rand

namespace Random

open Rand

variable [Monad m]

-- FIXME Find home.
instance : MonadLift Id m where
  monadLift x := pure x

/-- Generate a random value of type `α`. -/
def rand (α : Type u) [Random α] [RandomGen g] : RandG g m α := do (Random.random : RandG g Id α)

/-- Generate a random value of type `α` between `x` and `y` inclusive. -/
def randBound (α : Type u) [Preorder α] [BoundedRandom α] (lo hi : α) (h : lo ≤ hi) [RandomGen g] :
    RandG g m {a // lo ≤ a ∧ a ≤ hi} :=
  (BoundedRandom.randomR lo hi h : RandG g _ _)

def randFin {n : Nat} [RandomGen g] : RandG g m (Fin n.succ) :=
  λ ⟨g⟩ => pure <| randNat g 0 n.succ |>.map Fin.ofNat ULift.up

instance {n : Nat} : Random (Fin n.succ) where
  random := randFin

def randBool [RandomGen g] : RandG g m Bool :=
  return (← rand (Fin 2)) == 1


instance : Random Bool where
  random := randBool

instance {α : Type u} [Random α] : Random (ULift.{v} α) where
  random {g} := ULiftable.up (random : RandG g Id α)

instance : BoundedRandom Nat where
  randomR := λ lo hi h _ => do
    let z ← rand (Fin (hi - lo).succ)
    pure ⟨
      lo + z.val, Nat.le_add_right _ _,
      Nat.add_le_of_le_sub' h (Nat.le_of_succ_le_succ z.isLt)
    ⟩

instance : BoundedRandom Int where
  randomR := λ lo hi h _ => do
    let ⟨z, _, h2⟩ ← randBound Nat 0 (Int.natAbs $ hi - lo) (Nat.zero_le _)
    pure ⟨
      z + lo,
      Int.le_add_of_nonneg_left (Int.ofNat_zero_le z),
      Int.add_le_of_le_sub_right $ Int.le_trans
        (Int.ofNat_le.mpr h2)
        (le_of_eq $ Int.ofNat_natAbs_eq_of_nonneg _ $ Int.sub_nonneg_of_le h)⟩

instance {n : Nat} : BoundedRandom (Fin n) where
  randomR := λ lo hi h _ => do
    let ⟨r, h1, h2⟩ ← randBound Nat lo.val hi.val h
    pure ⟨⟨r, Nat.lt_of_le_of_lt h2 hi.isLt⟩, h1, h2⟩

instance {α : Type u} [Preorder α] [BoundedRandom α] : BoundedRandom (ULift.{v} α) where
  randomR {g} lo hi h := do
    let (⟨v⟩ : ULift.{v} _)
      ← (ULiftable.up (BoundedRandom.randomR lo.down hi.down h : RandG g _ _) : RandG g _ _)
    pure ⟨ULift.up v.val, v.prop⟩

end Random

open IO

variable {m : Type* → Type*} {m₀ : Type → Type}
variable [Monad m] [MonadLiftT (ST RealWorld) m₀] [ULiftable m₀ m]

/-- Computes a `Rand α` using the global `stdGenRef` as RNG.
    Note that:
    - `stdGenRef` is not necessarily properly seeded on program startup
      as of now and will therefore be deterministic.
    - `stdGenRef` is not thread local, hence two threads accessing it
      at the same time will get the exact same generator.
-/
def runRand (cmd : Rand m α) : m α := do
  let stdGen ← ULiftable.up stdGenRef.get
  let (res, new) ← StateT.run cmd stdGen
  let _ ← ULiftable.up (stdGenRef.set new.down)
  pure res

instance (f : Type u₀ → Type u₁) [Monad f] [LawfulFunctor f] : ULiftable f f where
  congr e := Functor.mapEquiv _ e

instance [LawfulMonad m] : MonadLift (Rand m) m where
  monadLift := runRand

def runRandWith (seed : Nat) (cmd : Rand m α) : m α := do
  pure $ (← cmd.run (ULift.up $ mkStdGen seed)).1
