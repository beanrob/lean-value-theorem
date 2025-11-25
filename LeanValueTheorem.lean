-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals
import LeanValueTheorem.Limits

variable {a b : ℝ} {f f' : ℝ → ℝ} {I : Set ℝ}

theorem rolle (hfc : is_cont_on f (cci a b)) (hff' : is_deriv I f f' (ooi a b))
 (hfab : f a = f b) : ∃ c ∈ ooi a b, f' c = 0 := sorry

theorem mvt (hfc : is_cont_on f (cci a b) ) (hff' : is_deriv I f f' (ooi a b)) :
 ∃ c ∈ ooi a b, f' c = (f a - f b) / (b - a) := sorry
