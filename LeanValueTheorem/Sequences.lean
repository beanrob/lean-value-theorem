import Mathlib.Data.Real.Basic


def is_sequence (f : ℕ → ℝ) : Prop :=
  true

def is_sequence_non_positive (f : ℕ → ℝ) : Prop :=
  ∀ a : ℕ, f a < 0

def is_sequence_non_negative (f : ℕ → ℝ) : Prop :=
  ∀ a : ℕ, f a > 0
