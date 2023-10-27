import Mathlib.Data.MvPolynomial.SchwartzZippel
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.FieldTheory.Finite.GaloisField


example (a b : GaloisField 2 1) : (a + b) * (a + b) = a * a + b * b := by
  ring_nf




structure Probabilistic (p : Prop) where
  (sampleSpaceSize : Nat)
  (witnessBound : Nat)
  (check : Fin sampleSpaceSize -> Prop)
  (dec: DecidablePred check)
  (correct : witnessBound ≤
    Finset.card (Finset.filter check Finset.univ))


inductive ArithExpr (n : Nat) where
  | const : ℤ -> ArithExpr n
  | var : Fin n -> ArithExpr n
  | add : ArithExpr n -> ArithExpr n -> ArithExpr n
  | sub : ArithExpr n -> ArithExpr n -> ArithExpr n
  | mul : ArithExpr n -> ArithExpr n -> ArithExpr n

noncomputable def ArithExpr.toMvPolynomial {n : Nat}
    (a : ArithExpr n) : MvPolynomial (Fin n) ℤ :=
  match a with
  | ArithExpr.const c => MvPolynomial.C c
  | ArithExpr.var i => MvPolynomial.X i
  | ArithExpr.add a b => ArithExpr.toMvPolynomial a
                          + ArithExpr.toMvPolynomial b
  | ArithExpr.sub a b => ArithExpr.toMvPolynomial a
                          - ArithExpr.toMvPolynomial b
  | ArithExpr.mul a b => ArithExpr.toMvPolynomial a
                          * ArithExpr.toMvPolynomial b

def encoding (n : Nat) (p : ArithExpr n) : Nat :=
  sorry

def Sha256 (n : Nat) (i : Nat) : ℤ :=
  sorry

axiom schwartz_zippel_derandomization (n : Nat)
    (p q : ArithExpr n)
    (hp : encoding n p ≤ 2^64)
    (hq : encoding n q ≤ 2^64)
    (hdp : p.toMvPolynomial.totalDegree ≤ 128)
    (hdq : q.toMvPolynomial.totalDegree ≤ 128) :
  let idx := (Nat.pair n
                (Nat.pair (encoding n p) (encoding n q)));
  p = q
    <->
  MvPolynomial.eval
    (fun i : Fin n => Sha256 idx i)
    p.toMvPolynomial
  =
  MvPolynomial.eval
    (fun i : Fin n => Sha256 idx i)
    q.toMvPolynomial
