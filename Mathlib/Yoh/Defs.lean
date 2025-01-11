import Mathlib

section Defs

abbrev SpaceDimension := ℕ

structure Delta where
  val : ℝ
  prop : val > 0

instance : Coe Delta ℝ where
  coe δ := δ.val

structure CDelta where
  val : ℝ
  prop : val > 0

instance : Coe CDelta ℝ where
  coe c_δ := c_δ.val

structure ConstK where
  val : ℝ
  prop : val > 0

instance : Coe ConstK ℝ where
  coe K := K.val

structure ConstM0 where
  val : ℝ
  prop : 1 < val

instance : Coe ConstM0 ℝ where
  coe M0 := M0.val

instance : Coe ConstM0 ℝ where
  coe M0 := M0.val

abbrev SideLength := ℕ

structure VolM' where
  val : ℕ

instance : Coe VolM' ℕ where
  coe M0 := M0.val

abbrev LatticeSpacing := ℕ

structure LatticeSpacing' where
  val : ℕ

instance : Coe LatticeSpacing' ℕ where
  coe N := N.val

abbrev RGStepL := ℕ

structure RGStepL' where
  val : ℕ
  prop : 1 < val

instance : Coe RGStepL' ℕ where
  coe L := L.val

end Defs
