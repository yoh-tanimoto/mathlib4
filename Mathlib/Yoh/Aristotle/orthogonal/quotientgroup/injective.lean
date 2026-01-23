import Mathlib

theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  sorry
