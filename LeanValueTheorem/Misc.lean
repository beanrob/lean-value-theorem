import LeanValueTheorem.Intervals

-- Temp import for triangle inequality!!!
import Mathlib.Algebra.Order.Group.Unbundled.Abs


-- Definition for f : D → ℝ being a constant function
def is_const_fun (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ D ∧ y ∈ D → f x = f y

lemma const_closed_const_open (a b : ℝ) (f : ℝ → ℝ) :
 is_const_fun (cci a b) f → is_const_fun (ooi a b) f := by
 intro h
 unfold is_const_fun at h
 unfold is_const_fun
 refine fun x y a ↦ ?_
 apply h
 cases a; expose_names
 apply open_in_closed at left
 apply open_in_closed at right
 exact ⟨left, right⟩
