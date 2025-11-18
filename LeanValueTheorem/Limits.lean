import Mathlib.Data.Real.Basic

-- A is the limit of the sequence a_n
def is_lim (a : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, N > 0 ∧ (∀ n, n ≥ N → abs (a n - A) < ε)

-- L is the limit of the function f at c
def is_lim_fun (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - c) < δ → abs (f x - L) < ε

-- L is the limit of f(x) as x tends to c from above
def is_lim_fun_abv (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x > c, x - c < δ → abs (f x - L) < ε
