import LeanValueTheorem.Intervals

-- Temp import for triangle inequality!!!
import Mathlib.Algebra.Order.Group.Unbundled.Abs


-- Definition for f : D → ℝ being a constant function
def is_const_fun (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ D ∧ y ∈ D → f x = f y
