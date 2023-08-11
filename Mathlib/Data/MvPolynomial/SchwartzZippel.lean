
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
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Polynomial.RingDivision




-- open_locale classical

-- example (A B : Type) (f g : A -> B) (h :  f = g) (x : A) : f x = g x :=
-- begin
--   exact congr_fun h x
-- end

/--
Given a finite type and a finset , returns the finite set of all functions with range contained in
that finset
-/
def function_finset (A : Type) (B : Type) [DecidableEq A] [Fintype A] (S : Finset B) : Finset (A -> B) :=
  Fintype.piFinset (fun _ => S)




lemma forall_cons_eval
  {n: ℕ}
  {S: F → Prop}
  (a: F)
  (b: Fin n → F) :
    ∀ n' : Fin (n+1), S ((@Fin.cons n (fun _ => F) (a : F) b n') : F)
    ↔
    ∀ (n' : Fin n), S (b n')
      ∧
    S a := by
  simp only
  apply?


lemma Fin.elim_succ {F: Type}
  {n: ℕ}
  {S: F → Prop}
  (a: F)
  (b: Fin n → F)
  (hab1: ∀ (n' : Fin n), S (b n'))
  (hab2: S a)
  (n': Fin (n + 1)) :
    S ((@Fin.cons n (fun _ => F) (a : F) b n') : F) := by
  apply?

@[simp]
lemma Fin.cons_mem_piFinset_iff {n : ℕ} (a : (Fin n → F)) (b: F)  (S : Finset F) :
    @Fin.cons _ (fun _ => F) b a ∈ Fintype.piFinset (fun _ => S)
    ↔
    a ∈ Fintype.piFinset (fun _ => S)
    ∧
    b ∈ S := by
  simp only [Fintype.mem_piFinset]
  simp_rw [forall_cons_eval]



@[simp]
lemma Fin.cons_comp_succ {n : ℕ} (a : (Fin n → F)) (b : F) :
    @Fin.cons _ (fun _ => F) b a ∘ Fin.succ = a := by
  apply Eq.refl

lemma and_or_and_not_iff (p q : Prop) : ((p ∧ q) ∨ (p ∧ ¬ q)) ↔ p := by
  tauto

lemma and_and_and_not_iff (p q : Prop) : ((p ∧ q) ∧ (p ∧ ¬ q)) ↔ false := by
  tauto

lemma mk_prod_of_proj (A B : Type) (ab : A × B) : (ab.fst, ab.snd) = ab := by
  exact rfl

-- set_option maxHeartbeats 0

-- lemma Finset.card_product_sum_left {α β : Type} [Fintype α] (r : Finset (α × β)) :
--     Finset.card r = ∑ a in α, Finset.card (r.filter (r.fst = a)) := by
--   sorry

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

    -- have h2 :
    --   (Finset.card
    --     (Finset.filter
    --       (fun (r : Fin (n+1) → F) ↦
    --         (MvPolynomial.eval (r : Fin (n+1) → F )) p ≠ 0
    --         ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
    --       (function_finset (Fin (n+1)) F S)
    --     ))
    --   *
    --   S.card
    --   ≤
    --   i *
    --   (Finset.card
    --     (Finset.filter
    --       (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
    --       (function_finset (Fin (n+1)) F S))) := by

    --   sorry

    have h_p_i'_deg_le : MvPolynomial.totalDegree p_i' ≤ (MvPolynomial.totalDegree p - i) := by

      sorry


    -- Pr[B] ≤ (d - i)/|S|
    have h_first_half :
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      ≤
      (MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n := by
      calc
      _ ≤ (MvPolynomial.totalDegree p_i') * (Finset.card S) ^ n := by
        convert ih
        rw [mul_comm, <-Finset.card_product]
        apply Eq.symm
        -- -- Potential golf: apply ext next
        -- convert Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F))
        -- rw [Finset.map_filter]
        -- simp only [
        --   Equiv.piFinSucc_symm_apply, Finset.mem_map_equiv, Function.comp_apply, Prod.forall]
        -- done
        -- --
        apply Finset.card_congr
          (fun ab _ => (@Fin.cons _ (fun _ => F)) ab.fst ab.snd )
        · intro ab ha
          rcases ab with ⟨a, b⟩
          rw [Finset.mem_product, Finset.mem_filter] at ha
          rcases ha with ⟨a_mem_S, b_mem_ffS, eval_b_zero⟩
          rw [Finset.mem_filter]
          simp only []
          unfold function_finset
          rw [Fin.cons_mem_piFinset_iff]
          constructor
          · constructor
            · exact b_mem_ffS
            · exact a_mem_S
          · rw [Fin.cons_comp_succ]
            exact eval_b_zero
        · intros ab1 ab2 _ _ hmkeq
          simp only [Fin.cons_eq_cons] at hmkeq
          rcases hmkeq with ⟨abfst, absnd⟩
          exact Prod.ext abfst absnd
        · unfold function_finset
          intros b hb
          use (Equiv.piFinSucc n F).toFun b
          rw [exists_prop]
          constructor
          · simp only [Equiv.toFun_as_coe_apply, Equiv.piFinSucc_apply, Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset]
            simp only [Finset.mem_filter, Fintype.mem_piFinset] at hb
            rcases hb with ⟨hb, hb'⟩
            constructor
            · exact hb 0
            · constructor
              · intro a
                apply hb
              · exact hb'
          · simp only [Equiv.toFun_as_coe_apply, Equiv.piFinSucc_apply]
            -- The below is a simp lemma, so why does the above simp not close?
            refine Fin.cons_self_tail b
      _ ≤ _ := by
        apply Nat.mul_le_mul_right
        exact h_p_i'_deg_le
    save
    have h_second_half :
      Finset.card
          (Finset.filter
            (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
            (function_finset (Fin (Nat.succ n)) F S))
      ≤
      (i) * (Finset.card S) ^ n := by
      -- Use polynomial.card_roots or card_roots'
      clear h_first_half
      -- rw [←Finset.card_congr
      --     (fun (ab : F × (Fin n → F)) _ => mk_fin_succ_function ab.snd ab.fst)]
      rw [←Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F))]
      rw [Finset.map_filter]
      rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_finset_product_right _
            (s := (Finset.filter (fun r ↦ (MvPolynomial.eval (r)) p_i' ≠ 0)
              (function_finset (Fin (n)) F S)))
            (t := fun r => Finset.filter (fun f => (MvPolynomial.eval ((Equiv.piFinSucc n F).invFun (f, r))) p = 0) S)]
      -- Note that ((Equiv.piFinSucc n F).invFun (f, r)) can be more simply written with Fin.cons
      · unfold function_finset
        simp_rw [←Finset.card_eq_sum_ones]
        apply le_trans (Finset.sum_le_sum (g := fun _ => i) _)
        · rw [Finset.sum_const, smul_eq_mul, mul_comm]
          apply Nat.mul_le_mul_left
          apply le_trans (Finset.card_filter_le _ _)
          apply le_of_eq
          rw [Fintype.card_piFinset]
          simp only [Finset.prod_const, Finset.card_fin]
        · intros b hb
          simp only [Equiv.invFun_as_coe, Equiv.piFinSucc_symm_apply]
          -- Diamond!
          apply le_trans _ (Polynomial.card_roots' (p'))
          sorry
      · -- Note Polynomial.coeff_natDegree, MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, are triggering but I don't want them
        unfold function_finset
        simp only [
          Equiv.piFinSucc_symm_apply, Finset.mem_map_equiv, Fintype.mem_piFinset, Function.comp_apply, Fin.cons_comp_succ,
          Prod.forall, Finset.mem_filter, Equiv.invFun_as_coe]
        intros a b
        -- TODO write unfold_projs tactic in Lean 4

        constructor
        · intro hfr
          rcases hfr with ⟨hfr1, hfr2, hfr3⟩
          constructor
          · constructor
            · intro n'
              refine hfr1 (Fin.succ n')
            · exact hfr3
          · constructor
            · refine hfr1 0
            · exact hfr2
        · intro hab
          rcases hab with ⟨⟨hab1, hab1'⟩, hab2, hab3⟩
          rw [←Fintype.mem_piFinset]
          simp only [Fin.cons_mem_piFinset_iff]
          constructor
          · simp [hab1, hab2]
            -- intro n'
            -- clear hab3 hab1' h_p_i'_deg_le ih h1 h0 p_i' i p' hp p
            -- apply @Fin.elim_succ F n (· ∈ S) a b hab1 hab2 n'
          · exact { left := hab3, right := hab1' }



    calc
      -- Pr[A]
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      * Finset.card S
      =
      -- Pr [A ∩ B] + Pr [A ∩ Bᶜ]
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
        congr
        rw [<-Finset.card_union_add_card_inter]
        rw [Finset.filter_union_right]
        -- todo note filter_or is the symm of this. Golf that proof.
        -- Also if filter and exists, maybe so should filter_inter_right
        rw [<-Finset.filter_and]
        simp only [ne_eq, and_or_and_not_iff, and_and_and_not_iff]
        simp only [Finset.filter_False, Finset.card_empty, add_zero]
      -- Pr [B] + Pr [A ∩ Bᶜ]
      _ ≤ (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (Nat.succ n)) F S))
      )
      * Finset.card S := by
        apply Nat.mul_le_mul_right
        rw [add_le_add_iff_right]
        apply Finset.card_le_of_subset
        apply Finset.monotone_filter_right
        rw [Pi.le_def]
        intro i
        aesop
      --
      _ ≤ ((MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n
          +
          (i) * (Finset.card S) ^ n
          )
      * Finset.card S := by
        apply Nat.mul_le_mul_right
        apply add_le_add
        exact h_first_half
        exact h_second_half
      -- -- Pr [B] + Pr [A ∩ Bᶜ]
      -- _ =
      -- Finset.card
      --   (Finset.filter
      --     (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
      --     (function_finset (Fin (Nat.succ n)) F S))
      -- * Finset.card S
      -- +
      -- Finset.card
      --   (Finset.filter
      --     (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
      --     (function_finset (Fin (Nat.succ n)) F S))
      -- * Finset.card S := by
      --   rw [add_mul]
      --   done
      -- -- Pr [B] + Pr [A | Bᶜ]
      -- -- _ ≤
      -- -- Finset.card
      -- --   (Finset.filter
      -- --     (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
      -- --     (function_finset (Fin (Nat.succ n)) F S))
      -- -- * Finset.card S
      -- -- +
      -- -- i *
      -- -- (Finset.card
      -- --   (Finset.filter
      -- --     (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
      -- --     (function_finset (Fin (n+1)) F S))) := by
      -- --   rw [add_le_add_iff_left]


      -- --   sorry
      -- -- todo
      -- _ ≤
      -- (MvPolynomial.totalDegree p_i' * Finset.card S ^ n)
      -- * Finset.card S
      -- +
      -- i *
      -- (Finset.card
      --   (Finset.filter
      --     (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
      --     (function_finset (Fin (n+1)) F S))) := by
      --   -- sorry
      --   -- simp
      --   -- congr 2

      --   apply add_le_add_right
      --   -- need to rewrite LHS to have ... * S.card * S.card
      --   exact ih
      --   -- sorry
      _ ≤
      MvPolynomial.totalDegree p * Finset.card S ^ Nat.succ n := by
        rw [Nat.pow_succ]
        rw [←mul_assoc]
        apply Nat.mul_le_mul_right
        rw [<-add_mul]
        apply Nat.mul_le_mul_right
        apply le_of_eq
        apply Nat.sub_add_cancel
        apply le_of_add_le_right h0
