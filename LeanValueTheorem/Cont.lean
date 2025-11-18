import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals

def is_cont_at (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (a : I) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ x : I, abs (x.val - a.val) < δ → abs (f x - f a) < ε

def is_cont (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) : Prop :=
  ∀ a : I, is_cont_at I hI f a
