import LeanValueTheorem.Intervals


-- Definition for f being a constant function
def is_const_fun (I : Set ℝ) (f : I → ℝ) : Prop :=
  ∀ x y : I, f x = f y

-- Definition for a being a
def is_fun_min (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (a : I) : Prop :=
  ∀ x : I, f a <= f x

def is_fun_max (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (b : I) : Prop :=
  ∀ x : I, f b >= f x
