-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Tactic
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals
import LeanValueTheorem.Limits

variable {a b : ℝ} {f f' : ℝ → ℝ} {I : Set ℝ}

theorem rolle (hfc : is_cont f (cci a b)) (hff' : is_deriv I f f' (ooi a b))
 (hfba : f b = f a) : ∃ c ∈ (ooi a b), f' c = 0 := sorry

theorem mvt {hab : a < b} (hfc : is_cont f (cci a b)) (hff' : is_deriv I f f' (ooi a b)) :
 ∃ c ∈ ooi a b, f' c = (f b - f a) / (b - a) := by
 let r : ℝ := (f b - f a) / (b - a)
 let g : ℝ → ℝ := fun x => f x - r * x
 let g' : ℝ → ℝ := fun x => f' x - r
 have hgc : is_cont g (cci a b) := by
  sorry
 have hgg' : is_deriv I g g' (ooi a b) := by
  have hx' : is_deriv I (fun x => x) (fun x => 1) (ooi a b) := by sorry
  sorry
 have hgba : g b = g a := by
  unfold g
  rw [sub_eq_iff_eq_add']
  rw [← add_sub_assoc]
  rw [add_comm]
  rw [add_sub_assoc]
  rw [← sub_eq_iff_eq_add']
  rw [← mul_sub]
  unfold r
  have hz (a b : ℝ) : a / b * b = a := by sorry
  rw [hz]
 have hgr : ∃ c ∈ (ooi a b), g' c = 0 := by
  exact rolle hgc hgg' hgba
 have hfr : ∃ c ∈ (ooi a b), f' c = r := by
  unfold g' at hgr
  sorry
 exact hfr
