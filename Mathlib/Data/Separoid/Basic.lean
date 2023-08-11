import Mathlib.Init.Algebra.Order
import Mathlib.Order.Basic

class WeakSemilatticeSup (α : Type _) extends Sup α, Preorder α where
  le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

class WeakSemilatticeInf (α : Type _) extends Inf α, Preorder α where
  inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

class WeakLattice (α : Type _) extends Sup α, Inf α, Preorder α where
  le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c
  inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

structure Separoid (α : Type _) [WeakSemilatticeSup α] where
  rel : α → α → α → Prop
  selfSep : {x y : α} → rel x y x
  reflSep : {x y z : α} → rel x y z → rel y x z
  submSep : {x y z : α} → rel x y z → {w : α} → w ≤ y → rel x w z
  subrSep : {x y z : α} → rel x y z → {w : α} → w ≤ y → rel x y (z ⊔ w)
  rsupSep : {x y z : α} → rel x y z → {w : α} → rel x w (y ⊔ z) → rel x (y ⊔ w) z

structure StrongSeparoid (α : Type _) [Sup α] [Inf α] [Preorder α] extends Separoid α where
  inflSep : {y z w : α} → z ≤ y → w ≤ y → {x : α} → rel x y z → rel x y w → rel x y (z ⊓ w)

section Separoid

variable {α : Type _} [Sup α] [Preorder α]
variable {S : Separoid α}

protected instance Separoid.isSetoid (α : Type _) [Sup α] [Preorder α] :
    Setoid α where
  r a b := a ≤ b ∧ b ≤ a
  iseqv := ⟨fun _ => ⟨le_rfl, le_rfl⟩,
            fun h => ⟨h.2, h.1⟩,
            fun h₁ h₂ => ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩⟩

notation:60 lhs:61 " ⫫(" Sep:61 ") " mhs:61 " ∣ " rhs:61 => Separoid.rel Sep lhs mhs rhs

theorem lemma1 {x y z : α} : x ⫫(S) y ∣ z ↔ (x ⊔ z) ⫫(S) (y ⊔ z) ∣ z := by
  constructor <;> intro h
  · apply S.rsupSep
    · apply S.reflSep
      apply S.rsupSep (S.reflSep h)
      sorry
    · sorry
  · sorry

end Separoid
