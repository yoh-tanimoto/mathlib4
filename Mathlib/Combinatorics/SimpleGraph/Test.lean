import Mathlib.Data.Fintype.Card

open Finset

variable {V : Type*} [Fintype V]

def aaa {f : { x : V // x ∈ univ } → { x : V // x ∈ univ } → Prop}
    (z : {m : { x : V // x ∈ univ } ≃ Fin ((univ : Finset V).card) // ∀ a b, f a b}) :
    {m' : V ≃ Fin (Fintype.card V) // ∀ a b, f ⟨a, by simp⟩ ⟨b, by simp⟩} := by
  sorry
