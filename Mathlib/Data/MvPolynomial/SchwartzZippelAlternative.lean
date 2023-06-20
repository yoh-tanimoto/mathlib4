
import Mathlib

/-!
A WIP alternative approach to schwartz zippel using "An Alternative Proof of The Schwartz-Zippel Lemma [https://eccc.weizmann.ac.il/report/2010/096/download/]"
-/

open MvPolynomial


def MvPolynomial.highest_degree_monomials {F σ : Type} [Field F] (p : MvPolynomial σ F) :
  MvPolynomial σ F := sorry

lemma MvPolynomial.highest_degree_monomials_homogeneous {F σ : Type} [Field F]
  (p : MvPolynomial σ F) : MvPolynomial.IsHomogeneous p.highest_degree_monomials (p.totalDegree) := sorry

/--
Proof. Assume on way of contradiction that for every y ∈ Fm, g(y) = 0. Then, there necessarily
exist 1 ≤ i ≤ m and a1, . . . , ai−1 ∈ F such that g(yi, . . . , ym) .
= f (a1, . . . , ai−1, yi, . . . , ym) 6 ≡ 0,
but for every a ∈ F it holds that g(a, yi+1, . . . , ym) ≡ 0. Note that g is of degree at most d. For
every a ∈ F, we have (yi − a)|g, so g’s degree is at least |F|, which is a contradiction. Moreover,
if g is homogeneous, then g(~0) = 0.
-/
lemma lemma_3_1 (F : Type) [Field F] [DecidableEq F] [Fintype F]
    (m d : ℕ)
    (g : MvPolynomial (Fin m) F) (hp : g ≠ 0)
    (hg : MvPolynomial.IsHomogeneous g d)
    (degree_pos : 0 < d )
    (degree_lt_card_F  : d < (Fintype.card F)) :
    ∃ y, MvPolynomial.eval y g ≠ 0 := by
  by_contra y_eval
  push_neg at y_eval
  sorry

/--
Let us assume m ≥ 2, 1 ≤ d < |F|. The proof is by reduction to the case m = 1. Write
f = g + h, where g ≠ 0 is homogeneous of degree d, and h contains only monomials of degree
strictly smaller than d. Let y ≠ 0 ∈ F^m be such that g(y) ≠ 0. Note that Fm can be partitioned
into |F|^{m−1} parallel lines, where each line is of the form { x + ty | t ∈ F} for some x ∈ F^m. For
any x ∈ F^m, the restriction f (x + ty) is a univariate polynomial in t of degree at most d.
Moreover, it is not identically 0! The reason is that the coefficient of td is g(y). Thus, the
number of zeros on each of the lines is at most d, and the total number of zeros of f is at most
d |F|^{m−1}.
-/


lemma schwartz_zippel (F : Type) [Field F] [DecidableEq F] [Fintype F]
    (m : ℕ)
    (p : MvPolynomial (Fin m) F) (hp : p ≠ 0)
    (degree_pos : 0 < p.totalDegree )
    (degree_lt_card_F  : p.totalDegree < (Fintype.card F))
    :
    (Finset.filter
      (fun f => MvPolynomial.eval f p = 0)
      (Finset.univ : Finset (Fin m -> F))).card * (Fintype.card F)
      ≤ (p.totalDegree) * (Fintype.card F) ^ (m) := by
  let g := p.highest_degree_monomials

  have hy : ∃ y : Fin m → F, y ≠ 0 ∧ MvPolynomial.eval y p ≠ 0
  sorry
