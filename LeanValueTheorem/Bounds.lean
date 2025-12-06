import Mathlib.Data.Real.Basic
import LeanValueTheorem.Cont

def upper_bound (f: ℝ → ℝ) (I : Set ℝ) (u : ℝ) : Prop :=
  ∀ x ∈ I, f x ≤ u

def least_upper_bound (f : ℝ → ℝ) (I : Set ℝ) (U : ℝ) : Prop :=
  ∀ u : ℝ, upper_bound f I u → U ≤ u

def lower_bound (f: ℝ → ℝ) (I : Set ℝ) (l : ℝ) : Prop :=
  ∀ x ∈ I, l ≤ f x

def greatest_lower_bound (f : ℝ → ℝ) (I : Set ℝ) (L : ℝ) : Prop :=
  ∀ l : ℝ, lower_bound f I l → l ≤ L

def is_bounded (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∃ U : ℝ, least_upper_bound f I U) ∧ (∃ L : ℝ, greatest_lower_bound f I L)

theorem cont_imp_bounded (f : ℝ → ℝ) (I : Set ℝ) : is_cont f I → is_bounded f I := by
  sorry

theorem cont_attains_bounds (f : ℝ → ℝ) (I : Set ℝ) {cont : is_cont f I} :
  (∃ a : ℝ,    least_upper_bound f I a → ∃ x ∈ I, f x = a) ∧
  (∃ b : ℝ, greatest_lower_bound f I b → ∃ x ∈ I, f x = b) := by
    have boundedness := cont_imp_bounded f I cont
    unfold is_bounded at boundedness
    obtain ⟨hupper, hlower⟩ := boundedness
    obtain ⟨U, hupper⟩ := hupper 
    obtain ⟨L, hlower⟩ := hlower 
    constructor
    · use U
      intro hupper
      by_contra h
      apply forall_not_of_not_exists at h
      -- ...
      sorry
    · use L
      intro hlower
      by_contra h
      apply forall_not_of_not_exists at h
      -- ...
      sorry
