
import Mathlib

variable {F} [Field F] {a b c : F}


structure Point where mk :: (x : F) (y : F)

def groupLaw (a : F) (p1 p2 : Point) :=
let slope := (y_2 - y_1)/(x_2 - x_1);
let intercept := y_1 - slope * x_1;
let x := slope^2 - a - x_1 - x_2;
let y := slope * x + intercept;
  Point.mk x y

def divide (a b : F) : F := a / b

lemma divide_divides (a b : F) : a / b = divide a b := by sorry

notation:100 "frac {" a "} {" b "}" => divide a b

lemma assoc_point (p1 p2 p3 : Point) :
    groupLaw a p1 (groupLaw a p2 p3) = groupLaw a (groupLaw a p1 p2) p3 := by
  unfold groupLaw
  simp
  simp_rw [divide_divides]
  sorry

notation

/--
((y_3 - y_2) / (x_3 - x_2) * ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3) +
                  (y_2 - (y_3 - y_2) / (x_3 - x_2) * x_2) -
                y_1) ^
              2 /
            ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3 - x_1) ^ 2 -
          a -
        x_1 -
      ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3) =
    (y_3 -
                ((y_2 - y_1) / (x_2 - x_1) * ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) +
                  (y_1 - (y_2 - y_1) / (x_2 - x_1) * x_1))) ^
              2 /
            (x_3 - ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2)) ^ 2 -
          a -
        ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) -
      x_3 ∧
  ((y_3 - y_2) / (x_3 - x_2) * ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3) +
              (y_2 - (y_3 - y_2) / (x_3 - x_2) * x_2) -
            y_1) /
          ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3 - x_1) *
        (((y_3 - y_2) / (x_3 - x_2) * ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3) +
                      (y_2 - (y_3 - y_2) / (x_3 - x_2) * x_2) -
                    y_1) ^
                  2 /
                ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3 - x_1) ^ 2 -
              a -
            x_1 -
          ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3)) +
      (y_1 -
        ((y_3 - y_2) / (x_3 - x_2) * ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3) +
                (y_2 - (y_3 - y_2) / (x_3 - x_2) * x_2) -
              y_1) /
            ((y_3 - y_2) ^ 2 / (x_3 - x_2) ^ 2 - a - x_2 - x_3 - x_1) *
          x_1) =
    (y_3 -
            ((y_2 - y_1) / (x_2 - x_1) * ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) +
              (y_1 - (y_2 - y_1) / (x_2 - x_1) * x_1))) /
          (x_3 - ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2)) *
        ((y_3 -
                    ((y_2 - y_1) / (x_2 - x_1) * ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) +
                      (y_1 - (y_2 - y_1) / (x_2 - x_1) * x_1))) ^
                  2 /
                (x_3 - ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2)) ^ 2 -
              a -
            ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) -
          x_3) +
      ((y_2 - y_1) / (x_2 - x_1) * ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) +
          (y_1 - (y_2 - y_1) / (x_2 - x_1) * x_1) -
        (y_3 -
              ((y_2 - y_1) / (x_2 - x_1) * ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2) +
                (y_1 - (y_2 - y_1) / (x_2 - x_1) * x_1))) /
            (x_3 - ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2)) *
          ((y_2 - y_1) ^ 2 / (x_2 - x_1) ^ 2 - a - x_1 - x_2))
-/
