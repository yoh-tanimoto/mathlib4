import Mathlib

example (X α : Type*) [TopologicalSpace X] [TopologicalSpace α] [AddZeroClass α] [ContinuousAdd α]
    {f : C(X, α)} {g : C(X, α)}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (f + g) := by
  simp only [ContinuousMap.coe_add]
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_tsupport (f + g))
  exact tsupport_add

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

variable [TopologicalSpace β] [Zero β] [FunLike F α β] [ContinuousMapClass F α β]

variable (f g : F)

#check f * g
