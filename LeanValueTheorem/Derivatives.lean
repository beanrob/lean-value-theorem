import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals


-- Defintion for f' being the derivative of f : D → ℝ at a
def is_deriv_at (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (a : ℝ) : Prop :=
  a ∈ D →
  is_lim_fun_abv {h : ℝ | a + h ∈ D} (fun h => (f (a + h) - f (a)) / h ) (f' a) 0

-- Defintion for f' being the derivative of f : D → ℝ on a set A
def is_deriv (D : Set ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ a ∈ A, is_deriv_at D f f' a

-- Proof that a function has zero derivative if and only if it is constant
lemma fun_with_zero_deriv
  (I : Set ℝ) (hI : is_interval I)
  (f : ℝ → ℝ) :
  is_deriv I f 0 I ↔ is_const_fun I f := sorry
