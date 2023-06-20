
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
-- import Mathlib.Data.Polynomial.Degree
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Embedding.Basic
import Mathlib.Algebra.Hom.Ring
import Mathlib.Tactic.ClearExcept
import Mathlib.Data.MvPolynomial.Equiv





-- open_locale classical

-- example (A B : Type) (f g : A -> B) (h :  f = g) (x : A) : f x = g x :=
-- begin
--   exact congr_fun h x
-- end

/--
Given a finite type and a finset , returns the finite set of all functions with range contained in
that finset
-/
noncomputable def function_finset (A : Type) (B : Type) [Fintype A] (S : Finset B) : Finset (A -> B) :=
  -- library_search
  sorry
  -- (finset.univ : finset (A → S)).map ⟨fun f z => f z,
  -- by
  --   intros f₁ f₂ hf,
  --   funext,
  --   have := congr_fun hf x,
  --   simp at this,
  --   ext,
  --   assumption,⟩
  -- (finset.pi (finset.univ : finset (fin n)) (λ _, S)).card

-- def function_finset_filter_slkadj (B : Type) (S : Finset B) (n : ℕ) (f : (Fin (Nat.succ n) -> B) -> Prop) [DecidablePred f] :
--   Finset.card
--       (Finset.filter (fun g => f (g ∘ Fin.succ)) (function_finset (Fin n) S))
--     =
--   Finset.card
--       (Finset.filter (fun g => f g) (function_finset (Fin (Nat.succ n)) S)) * S.card := by sorry


-- Following the wikipedia proof
-- I don't think that the wikipedia proof technique of starting at n=1 is necessary, so I start at n = 0
lemma schwartz_zippel (F : Type) [Field F] [DecidableEq F] (n : ℕ)
  (p : MvPolynomial (Fin (n)) F) (hp : p ≠ 0) (S : Finset F) :
  (Finset.filter (fun f => MvPolynomial.eval f p = 0) (function_finset (Fin (n)) F S)).card * S.card
    ≤ (p.totalDegree) * S.card ^ (n)
:= by
  revert p hp S
  induction n with
  | zero =>
    intros p hp S
    convert Nat.zero_le (MvPolynomial.totalDegree p * Finset.card S ^ Nat.zero)
    simp
    left
    convert Finset.filter_False (function_finset (Fin 0) F S)
    simp
    -- left
    -- Because p is a polynomial over an empty set of variables, it is constant
    have p_const : (p : MvPolynomial (Fin Nat.zero) F)
        = ((MvPolynomial.C (p.coeff 0)) : MvPolynomial (Fin Nat.zero) F) := by
        ext m
        have m0 : m = 0 := by
          ext a
          by_contra
          exact Fin.elim0 a
        rw [m0]
        simp
    rw [p_const]
    simp only [Nat.zero_eq, MvPolynomial.eval_C, iff_false, ne_eq]
    contrapose! hp
    rw [hp] at p_const
    rw [p_const]
    simp only [Nat.zero_eq, map_zero]
    done
    -- Now, assume that the theorem holds for all polynomials in n variables.
  | succ n ih =>
    intros p hp S
    -- We can then consider p to be a polynomial in x_1
    let p' : Polynomial (MvPolynomial (Fin n) F) := MvPolynomial.finSuccEquiv F n p
    -- since p is not identically zero, there is some i such that p_i' is not identically zero
    -- take the largest such i
    let i := p'.natDegree
    let p_i' := Polynomial.coeff p' i

    have h0 : (p'.coeff i).totalDegree + i ≤ (p.totalDegree) := by

      sorry

    have h1 : Polynomial.coeff p' i ≠ 0 := by
      sorry


    replace ih := ih p_i' h1 S
    -- Pr[p(r_1, r_2 ..., r_n) = 0 | p'_i(r_2, ..., r_n) ≠ 0 ] ≤ i / S.card

    have h2 :
      (Finset.card
        (Finset.filter
          (fun (r : Fin (n+1) → F) ↦
            (MvPolynomial.eval (r : Fin (n+1) → F )) p ≠ 0
            ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (n+1)) F S)
        ))
      *
      S.card
      ≤
      i *
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (n+1)) F S))) := by

      sorry

    calc
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      * Finset.card S
      =
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (Nat.succ n)) F S))
      )
      * Finset.card S := by
        sorry
      _ = (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (Nat.succ n)) F S))
      )
      * Finset.card S := by sorry
      _ =
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      * Finset.card S
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (Nat.succ n)) F S))
      * Finset.card S := by sorry
      _ =
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      * Finset.card S
      +
      i *
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (n+1)) F S))) := by sorry
      _ ≤
      (MvPolynomial.totalDegree p_i' * Finset.card S ^ n)
      * Finset.card S
      +
      i *
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (n+1)) F S))) := by
        -- sorry
        -- simp
        -- congr 2

        apply add_le_add_right
        -- need to rewrite LHS to have ... * S.card * S.card
        exact ih
        -- sorry
      _ ≤
      MvPolynomial.totalDegree p * Finset.card S ^ Nat.succ n := by sorry
    -- sorry
