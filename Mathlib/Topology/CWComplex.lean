/-
The definition of CW complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Category.TopCat.Basic

--universe u v w x
--variable {F : Type*} {X : Type u} {X' : Type v} {Y : Type w} {Z : Type x} {ι : Type*}
--variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

--open ContinuousMap

-- A type witnessing that X' is obtained from X by attaching n-cells
--structure CW_aux (X X' : Type*) [TopologicalSpace X] [TopologicalSpace X'] (n : ℕ) where
structure CW_aux (X X' : Type*) [TopologicalSpace X] [TopologicalSpace X'] (n : ℕ) where
  inclusion : ContinuousMap X X' -- C[X, X']
  cells : Type
-- should also have, for each i in cells a map ∂D^n ⟶ X, and
-- a homeomorphism between X' and the result of gluing these n-cells to X

structure CW_complex where
  skeleta : ℕ → TopCat
  foo : (n : ℕ) → CW_aux (skeleta n) (skeleta (n+1)) n

--structure CW_complex (X : Type*) [TopologicalSpace X] where
  -- skeleta : ℕ → ???
  --foo : (n : ℕ) → CW_aux (skeleta n) (skeleta (n+1)) n
  --foo : Π n, CW_aux (skeleta n) (skeleta (n+1)) n

#check CW_aux
