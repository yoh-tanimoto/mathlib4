import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition 1.1: A function a: R^d -> R is short range localizing if (i) a(x) > 0, (ii) decay condition, (iii) ratio bound on b, (iv) convolution bound on b, (v) b is eventually decreasing.
-/
open Real MeasureTheory Filter Topology

variable {d : ℕ}

/-- Semi-discrete convolution of two functions on `ℝ^d`. -/
def semiDiscreteConvolution (f g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑' y : Fin d → ℤ, f (x - (fun i => (y i : ℝ))) * g (fun i => (y i : ℝ))

/-- Iterated semi-discrete convolution. -/
def iteratedSemiDiscreteConvolution (f : (Fin d → ℝ) → ℝ) : ℕ → (Fin d → ℝ) → ℝ
| 0 => fun _ => 0 -- Or should it be delta? The user says "n-fold convolution". Usually n=1 is f.
| 1 => f
| (n + 1) => semiDiscreteConvolution (iteratedSemiDiscreteConvolution f n) f

-- The user's text implies n starts at 1? "b*b*...*b (n times)".
-- If n=1, it's b. If n=2, it's b*b.
-- My definition above:
-- 0 -> 0 (wrong?)
-- 1 -> f
-- 2 -> semiDiscreteConvolution (1) f = f * f. Correct.
-- So I should adjust the 0 case or just ignore it.
-- Actually, usually convolution power 0 is the identity (Dirac delta), but here we are in functions.
-- The user condition (iv) says "for all n". Presumably n >= 1.

structure ShortRangeLocalizing (d : ℕ) (a : (Fin d → ℝ) → ℝ) : Prop where
  pos : ∀ x, 0 < a x
  decay : ∃ δ > 0, ∃ c_δ ≥ 0, ∀ x, a x ≤ c_δ * (1 + ‖x‖)^(-(2 : ℝ) * (d + δ))
  -- We need to define b to state the other conditions.
  -- It's better to define b separately or use a let binding in the structure, but structure fields can't depend on let bindings easily.
  -- I'll define b inside the structure as a field or just write it out.
  -- But b depends on δ. The δ is existentially quantified in (ii).
  -- This suggests δ should be a parameter or a field.
  -- The user says "For δ as above...". This implies δ is fixed for the function a.
  -- So maybe the structure should existentially quantify δ?
  -- "A function a is short range localizing if ... (ii) ... for some δ ... (iii) For δ as above ..."
  -- This means there EXISTS a δ such that (ii), (iii), (iv) hold.
  -- So the structure should be:
  -- exists δ, (ii) and (iii) and (iv) and (v).
  -- Or I can bundle δ.
  -- Let's bundle δ.

structure ShortRangeLocalizingData (d : ℕ) (a : (Fin d → ℝ) → ℝ) where
  δ : ℝ
  hδ : 0 < δ
  c_δ : ℝ
  hc_δ : 0 ≤ c_δ
  decay : ∀ x, a x ≤ c_δ * (1 + ‖x‖)^(-(2 : ℝ) * (d + δ))
  K : ℝ
  -- b def:
  b := fun x => (1 + ‖x‖)^(d + δ) * a x
  bound_ratio : ∀ x y, ‖y‖ ≤ 2 * Real.sqrt d → b (x + y) / b x ≤ K
  c : ℝ
  ε : ℝ
  hε : 0 < ε
  conv_bound : ∀ n ≥ 1, ∀ x, iteratedSemiDiscreteConvolution b n x ≤ c^n * b (ε • x)
  M₀ : ℕ
  eventually_decreasing : ∀ x x', M₀ ≤ ‖x‖ → ‖x‖ ≤ ‖x'‖ → b x' ≤ b x

def IsShortRangeLocalizing (d : ℕ) (a : (Fin d → ℝ) → ℝ) : Prop :=
  Nonempty (ShortRangeLocalizingData d a)

/-
Lemma 1.2: Let b be as in Definition 1.1. Then, for M_tilde sufficiently large, b(M_tilde * x / 3) <= b(x) for all x in Z^d.
-/
theorem b_scaling (d : ℕ) (a : (Fin d → ℝ) → ℝ) (h : IsShortRangeLocalizing d a) :
    let data := h.some
  ∃ (M : ℝ), (0 < M ∧ ∀ M_tilde : ℕ, M < M_tilde → ∀ x : Fin d → ℤ,
    data.b (((M_tilde : ℝ) / 3) • (fun i => (x i : ℝ))) ≤ data.b (fun i => (x i : ℝ))) := by
  sorry
