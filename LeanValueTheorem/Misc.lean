import LeanValueTheorem.Intervals


-- Definition for f : D → ℝ being a constant function
def is_const_fun (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ D ∧ y ∈ D → f x = f y

-- Definition for a being a
def is_fun_min (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (a : I) : Prop :=
  ∀ x : I, f a <= f x

def is_fun_max (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (b : I) : Prop :=
  ∀ x : I, f b >= f x
