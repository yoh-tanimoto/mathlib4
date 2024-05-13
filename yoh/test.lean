import Mathlib

example (X α : Type*) [TopologicalSpace X] [TopologicalSpace α] [AddZeroClass α] [ContinuousAdd α]
    {f : C(X, α)} {g : C(X, α)}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (f + g) := by
  simp only [ContinuousMap.coe_add]
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_tsupport (f + g))
  exact tsupport_add
