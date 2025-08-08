import Mathlib

section Defs

structure ModelParameter (p : ℝ → Prop) where
  val : ℝ
  prop : p val

instance (p : ℝ → Prop) : CoeTC (ModelParameter p) ℝ where
  coe x := x.val

def Delta := ModelParameter (fun δ => 0 < δ)

instance (p : ℝ → Prop) : HAdd ℝ (ModelParameter p) ℝ where
  hAdd x y := x + y.val

instance (p : ℝ → Prop) : HAdd (ModelParameter p) ℝ ℝ where
  hAdd x y := x.val + y


variable (δ : (ModelParameter (fun δ => 0 < δ))) (x : ℝ)

#check x = δ

abbrev SpaceDimension := ℕ

variable (δ cδ K : ℝ)
(hδ : 0 < δ) (hCδ : 0 < cδ) (hK : 0 < K)

-- structure Delta where
--   val : ℝ
--   prop : val > 0

-- instance : Coe Delta ℝ where
--   coe δ := δ.val

-- structure CDelta where
--   val : ℝ
--   prop : val > 0

-- instance : Coe CDelta ℝ where
--   coe c_δ := c_δ.val

-- structure ConstK where
--   val : ℝ
--   prop : val > 0

-- instance : Coe ConstK ℝ where
--   coe K := K.val

-- structure ConstM0 where
--   val : ℝ
--   prop : 1 < val

-- instance : Coe ConstM0 ℝ where
--   coe M0 := M0.val

-- instance : Coe ConstM0 ℝ where
--   coe M0 := M0.val

abbrev SideLength := ℕ

-- structure VolM' where
--   val : ℕ

-- instance : Coe VolM' ℕ where
--   coe M0 := M0.val

abbrev LatticeSpacing := ℕ

-- structure LatticeSpacing' where
--   val : ℕ

-- instance : Coe LatticeSpacing' ℕ where
--   coe N := N.val

abbrev RGStepL := ℕ

-- structure RGStepL' where
--   val : ℕ
--   prop : 1 < val

-- instance : Coe RGStepL' ℕ where
--   coe L := L.val

-- end Defs
