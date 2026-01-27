import Mathlib.Data.Real.Basic
import LeanValueTheorem.Cont


theorem cont_closed_imp_bounded (f : ℝ → ℝ) (a b : ℝ) (hfc : is_cont f (cci a b)) :
  BddAbove (f '' (cci a b)) ∧ BddBelow (f '' (cci a b)) := by

  by_contra h
  rw [not_and_or] at h
  cases h with
  | inl hl =>
    unfold BddAbove upperBounds at hl
    simp at hl
    rw [Set.not_nonempty_iff_eq_empty] at hl
    rw [←Set.compl_univ_iff] at hl
    have ex (n : ℝ) : n ∈ Set.univ := by trivial
    rw [←hl] at ex
    simp at ex
    sorry

  | inr hr =>
    unfold BddBelow lowerBounds at hr
    simp at hr
    rw [Set.not_nonempty_iff_eq_empty] at hr
    rw [←Set.compl_univ_iff] at hr
    have ex (n : ℝ) : n ∈ Set.univ := by trivial
    rw [←hr] at ex
    simp at ex
    sorry


theorem cont_closed_attains_bounds (f : ℝ → ℝ) (a b : ℝ) (cont : is_cont f (cci a b)) :
  (∃ x ∈ (cci a b), IsLUB (f '' (cci a b)) (f x)) ∧
  (∃ x ∈ (cci a b), IsGLB (f '' (cci a b))  (f x)) := by

  have boundedness := cont_closed_imp_bounded f a b cont
  unfold BddAbove BddBelow at boundedness
  obtain ⟨hupper, hlower⟩ := boundedness
  obtain ⟨U, hupper⟩ := hupper
  obtain ⟨L, hlower⟩ := hlower
  constructor
  · use U
    by_contra h
    -- apply forall_not_of_not_exists at h
    -- ...
    sorry

  · use L
    by_contra h
    -- apply forall_not_of_not_exists at h
    -- ...
    sorry
