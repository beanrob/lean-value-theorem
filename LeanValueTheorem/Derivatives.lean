import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals

def is_const_fun (f : ℝ → ℝ) (s : Set ℝ) : Prop := sorry

def deriv_on_point (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) : ℝ := sorry

def is_deriv_on_set (f : ℝ → ℝ) (s : Set ℝ) : Prop := sorry

lemma fun_with_zero_deriv
  (I : Set ℝ) (hI : is_interval I)
  (f : ℝ → ℝ) (hf : is_deriv_on_set f I)
  (hfIx : ∀ x ∈ I, deriv_on_point f I x = (0 : ℝ)) :
  is_const_fun f I := sorry


-- Rolles theorem
-- Mean Value theorem
