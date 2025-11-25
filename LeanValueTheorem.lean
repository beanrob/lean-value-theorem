-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals

variable {a b : ℝ} {I : Set ℝ} {f f' : ℝ → ℝ}

theorem rolle (hI : I = ooi a b) (hfc : is_cont_on_set I hI f) (hff' : is_deriv_on f f' (ooi a b))
 (hfab : f a = f b) : ∃ c ∈ ooi a b, f' c = 0 := sorry

theorem mvt (hfc : is_cont_on_set I hI f) (hff' : is_deriv_on f f' (ooi a b)) :
 ∃ c ∈ ooi a b, f' c = (f a - f b) / (b - a) := sorry
