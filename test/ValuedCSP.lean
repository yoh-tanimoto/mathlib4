import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Curry

/-!
# VCSP examples

This file shows two simple examples of General-Valued Constraint Satisfaction Problems (see 
[ValuedCSP definition](Mathlib/Combinatorics/Optimization/ValuedCSP.lean)).
The first example is an optimization problem. The second example is a decision problem.
-/

def valuedCspTermOfUnary {D C : Type} [OrderedAddCommMonoid C]
    {Γ : ValuedCsp D C} {ι : Type*} {f : D → C}
    (ok : ⟨1, Function.OfArity.uncurry f⟩ ∈ Γ) (i : ι) : Γ.Term ι :=
  ⟨1, Function.OfArity.uncurry f, ok, ![i]⟩

def valuedCspTermOfBinary {D C : Type} [OrderedAddCommMonoid C]
    {Γ : ValuedCsp D C} {ι : Type*} {f : D → D → C}
    (ok : ⟨2, Function.OfArity.uncurry f⟩ ∈ Γ) (i j : ι) : Γ.Term ι :=
  ⟨2, Function.OfArity.uncurry f, ok, ![i, j]⟩

-- Example: minimize `|x| + |y|` where `x` and `y` are rational numbers

private def absRat : (Fin 1 → ℚ) → ℚ := Function.OfArity.uncurry Abs.abs

private def exampleAbs : Σ (n : ℕ), (Fin n → ℚ) → ℚ := ⟨1, absRat⟩

private def exampleFiniteValuedCsp : ValuedCsp ℚ ℚ := {exampleAbs}

private lemma abs_in : ⟨1, absRat⟩ ∈ exampleFiniteValuedCsp := rfl

private def exampleFiniteValuedInstance : exampleFiniteValuedCsp.Instance (Fin 2) :=
  Multiset.ofList [valuedCspTermOfUnary abs_in 0, valuedCspTermOfUnary abs_in 1]

#eval exampleFiniteValuedInstance.evalSolution ![(3 : ℚ), (-2 : ℚ)]

example : exampleFiniteValuedInstance.IsOptimumSolution ![(0 : ℚ), (0 : ℚ)] := by
  unfold ValuedCsp.Instance.IsOptimumSolution
  unfold exampleFiniteValuedCsp
  intro s
  convert_to 0 ≤ exampleFiniteValuedInstance.evalSolution s
  rw [ValuedCsp.Instance.evalSolution, exampleFiniteValuedInstance]
  convert_to 0 ≤ |s 0| + |s 1|
  · simp [valuedCspTermOfUnary, ValuedCsp.Term.evalSolution, Function.OfArity.uncurry]
  positivity

-- Crisp domain

private def Bool_add_le_add_left (a b : Bool) :
  (a = false ∨ b = true) → ∀ (c : Bool), (((c || a) = false) ∨ ((c || b) = true)) :=
by simp

-- Upside down !!
instance crispCodomain : LinearOrderedAddCommMonoid Bool where
  __ := Bool.linearOrder
  add (a b : Bool) := a || b
  add_assoc := Bool.or_assoc
  zero := false
  zero_add (_ : Bool) := rfl
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  add_le_add_left := Bool_add_le_add_left

-- Example: `B ≠ A ≠ C ≠ D ≠ B ≠ C` with three available labels (i.e., 3-coloring of K₄⁻)

private def beqBool : (Fin 2 → Fin 3) → Bool := Function.OfArity.uncurry BEq.beq

private def exampleEquality : Σ (n : ℕ), (Fin n → Fin 3) → Bool := ⟨2, beqBool⟩

private def exampleCrispCsp : ValuedCsp (Fin 3) Bool := {exampleEquality}

private lemma beq_in : ⟨2, beqBool⟩ ∈ exampleCrispCsp := rfl

private def exampleTermAB : exampleCrispCsp.Term (Fin 4) :=
  valuedCspTermOfBinary beq_in 0 1

private def exampleTermBC : exampleCrispCsp.Term (Fin 4) :=
  valuedCspTermOfBinary beq_in 1 2

private def exampleTermCA : exampleCrispCsp.Term (Fin 4) :=
  valuedCspTermOfBinary beq_in 2 0

private def exampleTermBD : exampleCrispCsp.Term (Fin 4) :=
  valuedCspTermOfBinary beq_in 1 3

private def exampleTermCD : exampleCrispCsp.Term (Fin 4) :=
  valuedCspTermOfBinary beq_in 2 3

private def exampleCrispCspInstance : exampleCrispCsp.Instance (Fin 4) :=
  Multiset.ofList [exampleTermAB, exampleTermBC, exampleTermCA, exampleTermBD, exampleTermCD]

private def exampleSolutionCorrect0 : Fin 4 → Fin 3 :=   ![0, 1, 2, 0]
private def exampleSolutionCorrect1 : Fin 4 → Fin 3 :=   ![1, 2, 3, 1]
private def exampleSolutionCorrect2 : Fin 4 → Fin 3 :=   ![2, 0, 1, 2]
private def exampleSolutionCorrect3 : Fin 4 → Fin 3 :=   ![0, 2, 1, 0]
private def exampleSolutionCorrect4 : Fin 4 → Fin 3 :=   ![1, 0, 2, 1]
private def exampleSolutionCorrect5 : Fin 4 → Fin 3 :=   ![1, 0, 2, 1]
private def exampleSolutionIncorrect0 : Fin 4 → Fin 3 := ![0, 0, 0, 0]
private def exampleSolutionIncorrect1 : Fin 4 → Fin 3 := ![1, 0, 0, 0]
private def exampleSolutionIncorrect2 : Fin 4 → Fin 3 := ![0, 2, 0, 0]
private def exampleSolutionIncorrect3 : Fin 4 → Fin 3 := ![0, 1, 0, 2]
private def exampleSolutionIncorrect4 : Fin 4 → Fin 3 := ![2, 2, 0, 1]
private def exampleSolutionIncorrect5 : Fin 4 → Fin 3 := ![0, 1, 2, 1]
private def exampleSolutionIncorrect6 : Fin 4 → Fin 3 := ![1, 0, 0, 1]
private def exampleSolutionIncorrect7 : Fin 4 → Fin 3 := ![2, 2, 0, 2]

#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect0 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect1 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect2 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect3 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect4 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect5 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect0 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect1 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect2 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect3 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect4 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect5 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect6 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect7 -- `true` means WRONG here

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect0 := by
  intro _
  apply Bool.false_le
