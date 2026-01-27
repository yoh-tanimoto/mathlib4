/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8cb6b708-b7bb-4df7-b0dc-195f258c7897

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example : Function.Injective F ↔ ∀ g, g = 1 ↔ F g = 1

- theorem Quot.injective_lift {α : Sort*} {γ : Sort*} {r : Setoid α} {f : α → γ}
    (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂) :
    Function.Injective (Quot.lift f h) ↔ ∀ (a₁ a₂ : α), r a₁ a₂ ↔ f a₁ = f a₂

The following was negated by Aristotle:

- theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Mathlib


/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
There exists a counterexample to the claim that surjectivity of the quotient map implies N = f⁻¹(M). Consider G = ℤ, H = 1, N = 1, M = 1. The map is surjective but N ≠ f⁻¹(M).
-/
theorem QuotientGroup.map_surjective_counterexample : ∃ (G H : Type) (instG : Group G) (instH : Group H) (N : Subgroup G) (nN : N.Normal) (M : Subgroup H) (nM : M.Normal) (f : G →* H) (h : N ≤ Subgroup.comap f M), Function.Surjective (QuotientGroup.map N M f h) ∧ N ≠ Subgroup.comap f M := by
  use Multiplicative ( ULift ( Fin 2 ) );
  refine' ⟨ PUnit, _, _, ⊥, _, ⊥, _, _ ⟩ <;> norm_num [ Function.Surjective ];
  all_goals try infer_instance;
  refine' ⟨ _, _, _ ⟩;
  exact?;
  · rintro ⟨ ⟩ ; exact ⟨ 1, rfl ⟩ ;
  · simp +decide [ SetLike.ext_iff ]

end AristotleLemmas

theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use ULift ( Multiplicative ( Fin 2 ) );
  refine' ⟨ PUnit, _, _, ⊥, _, ⊥, _, _ ⟩ <;> norm_num [ Function.Surjective ];
  all_goals try infer_instance;
  refine' ⟨ 1, Or.inl ⟨ _, _ ⟩ ⟩ <;> simp +decide [ eq_comm ];
  rintro ⟨ ⟩ ; exact ⟨ 1, rfl ⟩ ;

-/
theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  sorry

section

variable {X Y : Type} [Group X] [Group Y] (F : X →* Y)

example : Function.Injective F ↔ ∀ g, g = 1 ↔ F g = 1 := by
  -- The kernel of $F$ is trivial if and only if $F$ is injective.
  have h_kernel_trivial : Function.Injective F ↔ F.ker = ⊥ := by
    exact?;
  -- The kernel of $F$ being trivial means that the only element in the kernel is the identity element. So, if the kernel is trivial, then for any $g \in X$, $g \in \ker(F)$ implies $g = 1$.
  simp [h_kernel_trivial, Subgroup.eq_bot_iff_forall];
  -- The equivalence follows from the fact that if the kernel of $F$ is trivial, then $F$ is injective, and vice versa.
  apply Iff.intro (fun h => by
    exact fun g => ⟨ fun hg => by simp +decide [ hg ], fun hg => h g hg ⟩) (fun h => by
    -- By applying the hypothesis h to x, we get that x = 1 if and only if F(x) = 1.
    intros x hx
    apply (h x).mpr hx)

end

theorem Quot.injective_lift {α : Sort*} {γ : Sort*} {r : Setoid α} {f : α → γ}
    (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂) :
    Function.Injective (Quot.lift f h) ↔ ∀ (a₁ a₂ : α), r a₁ a₂ ↔ f a₁ = f a₂ := by
  -- To prove the equivalence, we split it into two implications.
  apply Iff.intro;
  · -- Assume that the lift of f to the quotient set is injective. We need to show that for any a₁ and a₂ in α, r a₁ a₂ if and only if f a₁ = f a₂.
    intro h_inj a₁ a₂
    constructor
    intro h_eq
    apply h a₁ a₂ h_eq
    intro h_eq
    have h_lift_eq : Quot.lift f h (Quot.mk r a₁) = Quot.lift f h (Quot.mk r a₂) := by
      convert h_eq using 1;
    exact?;
  · -- Assume that for all a₁ and a₂, r a₁ a₂ ↔ f a₁ = f a₂. We need to show that Quot.lift f h is injective.
    intro h_eq
    intro q1 q2 hq
    obtain ⟨a₁, rfl⟩ := Quot.exists_rep q1
    obtain ⟨a₂, rfl⟩ := Quot.exists_rep q2
    have h_r : r a₁ a₂ := by
      -- By the equivalence h_eq, if f a₁ = f a₂, then r a₁ a₂.
      apply (h_eq a₁ a₂).mpr hq
    have h_f : f a₁ = f a₂ := by
      exact h _ _ h_r
    exact (by
    exact Quot.sound h_r)