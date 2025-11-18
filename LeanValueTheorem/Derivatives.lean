import Mathlib.Data.Real.Basic
import LeanValueTheorem.Misc
import LeanValueTheorem.Limits
import LeanValueTheorem.Intervals


-- Defintion for f' being the derivative of f at a
def is_deriv (f : ℝ → ℝ) (f' : ℝ → ℝ) (a : ℝ) : Prop :=
  is_lim_fun_abv (fun h => (f (a + h) - f (a)) / h ) (f' a) 0

-- Defintion for f' being the derivative of f on a set A
def is_deriv_on (f : ℝ → ℝ) (f' : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ a ∈ A, is_deriv f f' a

def deriv_on_point (S : Set ℝ) (f : S → ℝ) (x : ℝ) : ℝ := sorry

def is_deriv_on_set (S : Set ℝ) (f : S → ℝ) : Prop := sorry

-- Proof that a function has zero derivative if and only if it is constant
lemma fun_with_zero_deriv
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ) (hf : is_deriv_on_set I f)
  (hfIx : ∀ x ∈ I, deriv_on_point I f x = (0 : ℝ)) :
  is_const_fun I f := sorry
