import Mathlib

theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Injective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  sorry

section

variable {X Y : Type} [Group X] [Group Y] (F : X →* Y)

example : Function.Injective F ↔ ∀ g, g = 1 ↔ F g = 1 := by
  sorry

end

theorem Quot.injective_lift {α : Sort*} {γ : Sort*} {r : Setoid α} {f : α → γ}
    (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂) :
    Function.Injective (Quot.lift f h) ↔ ∀ (a₁ a₂ : α), r a₁ a₂ ↔ f a₁ = f a₂ := by
  sorry
