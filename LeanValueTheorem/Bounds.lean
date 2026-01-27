import Mathlib.Data.Real.Basic
import LeanValueTheorem.Cont

#check upperBounds
#check lowerBounds
#check BddAbove
#check BddBelow


def upper_bound (f : ℝ → ℝ) (I : Set ℝ) (u : ℝ) : Prop :=
  ∀ x ∈ I, f x ≤ u

def least_upper_bound (f : ℝ → ℝ) (I : Set ℝ) (U : ℝ) : Prop :=
  (upper_bound f I U) ∧ (∀ u : ℝ, upper_bound f I u → U ≤ u)

def lower_bound (f : ℝ → ℝ) (I : Set ℝ) (l : ℝ) : Prop :=
  ∀ x ∈ I, l ≤ f x

def greatest_lower_bound (f : ℝ → ℝ) (I : Set ℝ) (L : ℝ) : Prop :=
  (lower_bound f I L) ∧ (∀ l : ℝ, lower_bound f I l → l ≤ L)

def is_bounded (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∃ U : ℝ, upper_bound f I U) ∧ (∃ L : ℝ, lower_bound f I L)

def is_unbounded (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ n : ℝ, ∃ x ∈ I, |f x| > n

lemma not_unbounded_iff_bounded (f : ℝ → ℝ) (I : Set ℝ) :
  ¬ (is_unbounded f I) ↔ (is_bounded f I) := by

  constructor
  · intro h
    unfold is_unbounded at h
    simp at h
    rcases h with ⟨B, hIB⟩

    have upper (x : ℝ) (hx : x ∈ I) : f x ≤ B := le_trans (le_abs_self (f x)) (hIB x hx)
    have lower (x : ℝ) (hx : x ∈ I) : -B ≤ f x := (abs_le.mp (hIB x hx)).1
    exact ⟨⟨B, upper⟩, ⟨-B, lower⟩⟩

  · intro h
    unfold is_bounded at h
    rw [exists_and_exists_comm] at h
    rcases h with ⟨a, b, ha, hb⟩
    unfold is_unbounded
    simp
    refine ⟨max a (-b), ?_⟩
    intro x hx
    by_cases hfp : f x ≥ 0
    · rw [abs_of_nonneg hfp]
      exact le_trans (ha x hx) (le_max_left a (-b))
    · simp at hfp
      rw [abs_of_neg hfp]
      exact le_trans (neg_le_neg (hb x hx)) (le_max_right a (-b))


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


theorem cont_closed_imp_bounded (f : ℝ → ℝ) (a b : ℝ) (hfc : is_cont f (cci a b)) :
  is_bounded f (cci a b) := by

  by_contra h
  have co (p q : Prop) : (p → q) → (¬q → ¬p) := by exact fun a_2 a_3 a ↦ a_3 (a_2 a)
  have hunbf := co
    (¬is_unbounded f (cci a b))
    (is_bounded f (cci a b))
    (not_unbounded_iff_bounded f (cci a b)).mp h

  unfold is_unbounded at hunbf
  simp at hunbf

  sorry



theorem cont_closed_attains_bounds (f : ℝ → ℝ) (a b : ℝ) (cont : is_cont f (cci a b)) :
  (∃ x ∈ (cci a b),    least_upper_bound f (cci a b) (f x)) ∧
  (∃ x ∈ (cci a b), greatest_lower_bound f (cci a b) (f x)) := by
  sorry
