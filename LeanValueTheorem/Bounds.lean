import Mathlib.Data.Real.Basic
import LeanValueTheorem.Cont


def upper_bound (f : ℝ → ℝ) (I : Set ℝ) (u : ℝ) : Prop :=
  ∀ x ∈ I, f x ≤ u

def least_upper_bound (f : ℝ → ℝ) (I : Set ℝ) (U : ℝ) : Prop :=
  (upper_bound f I U) ∧ (∀ u : ℝ, upper_bound f I u → U ≤ u)

def lower_bound (f : ℝ → ℝ) (I : Set ℝ) (l : ℝ) : Prop :=
  ∀ x ∈ I, l ≤ f x

def greatest_lower_bound (f : ℝ → ℝ) (I : Set ℝ) (L : ℝ) : Prop :=
  (lower_bound f I L) ∧ (∀ l : ℝ, lower_bound f I l → l ≤ L)

def is_bounded (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∃ U : ℝ, least_upper_bound f I U) ∧ (∃ L : ℝ, greatest_lower_bound f I L)

theorem cont_closed_imp_bounded (f : ℝ → ℝ) (a b : ℝ) :
 is_cont f (cci a b) → is_bounded f (cci a b) := by
  sorry

theorem cont_closed_attains_bounds (f : ℝ → ℝ) (a b : ℝ) (cont : is_cont f (cci a b)) :
 (∃ x ∈ (cci a b),    least_upper_bound f (cci a b) (f x)) ∧
 (∃ x ∈ (cci a b), greatest_lower_bound f (cci a b) (f x)) := by
 sorry
