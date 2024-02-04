/-
The definition of CW complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Order

--universe u v w x
--variable {F : Type*} {X : Type u} {X' : Type v} {Y : Type w} {Z : Type x} {ι : Type*}
--variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

-- A type witnessing that X' is obtained from X by attaching n-cells
structure AttachCells (X X' : Type*) [TopologicalSpace X] [TopologicalSpace X'] (n : ℕ) where
  inclusion : C(X, X') -- rewrite using pushouts?
  cells : Type

structure CWComplex where
  /- Skeleta -/
  sk : ℤ → TopCat
  /- Every n-skeleton for n < 0 is empty. -/
  sk_neg_empty : ∀ n < 0, sk n = Empty
  /- For n ≥ 0, the (n-1)-skeleton is obtained from the n-skeleton by attaching n-cells. -/
  attach : (n : ℕ) → AttachCells (sk (n - 1)) (sk n) n

-- -- A type witnessing that X' is obtained from X by attaching n-cells
-- structure AttachCells (X X' : Type*) [TopologicalSpace X] [TopologicalSpace X'] (n : ℕ) where
--   inclusion : C(X, X')
--   cells : Type
-- -- should also have, for each i in cells a map ∂D^n ⟶ X, and
-- -- a homeomorphism between X' and the result of gluing these n-cells to X

-- structure CWComplex where
--   /- Skeleta -/
--   sk : ℕ → TopCat
--   /- The 0-skeleton is a discrete topological space. -/
--   discrete_sk_zero : DiscreteTopology (sk 0)
--   /- The (n+1)-skeleton is obtained from the n-skeleton by attaching (n+1)-cells. -/
--   attach : (n : ℕ) → AttachCells (sk n) (sk (n + 1)) (n + 1)
