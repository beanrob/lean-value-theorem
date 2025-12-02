import LeanValueTheorem.Intervals


-- Definition for f : D → ℝ being a constant function
def is_const_fun (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ D ∧ y ∈ D → f x = f y

-- Definition for a being a
def is_fun_min (I : Set ℝ) {hI : is_interval I} (f : ℝ → ℝ) (a : ℝ) : Prop := sorry
def is_fun_max (I : Set ℝ) {hI : is_interval I} (f : ℝ → ℝ) (b : ℝ) : Prop := sorry
