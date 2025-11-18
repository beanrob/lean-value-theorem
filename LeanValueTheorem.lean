-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals
import LeanValueTheorem.Limits

theorem rolle (hfc : is_cont (cci a b) f) (hff' : is_deriv_on f f' (ooi a b))
 (hab : f a = f b) : ∃ c ∈ Ioo a b, f' c = 0 := by

-- theorem mvt ... := by
