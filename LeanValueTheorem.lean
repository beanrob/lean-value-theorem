-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Tactic
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals
import LeanValueTheorem.Limits

variable {a b : ℝ} {f f' : ℝ → ℝ} {I : Set ℝ}

theorem rolle {hfc : is_cont f (cci a b)} {hff' : is_deriv I f f' (ooi a b)}
 {hfba : f b = f a} : ∃ c ∈ (ooi a b), f' c = 0 := by sorry

theorem mvt {hab : a < b} {hfc : is_cont f (cci a b)} {hff' : is_deriv I f f' (ooi a b)} :
 ∃ c ∈ ooi a b, f' c = (f b - f a) / (b - a) := by
 let r : ℝ := (f b - f a) / (b - a)
 let g : ℝ → ℝ := fun x => f x - r * x
 let g' : ℝ → ℝ := fun x => f' x - r
 have hrx : is_cont (fun x => -(r * x)) (cci a b) := by
  have hprod: (fun x => -(r * x)) = (fun x => -r) * (fun x => x) := by sorry
  rw [hprod]
  apply cont_on_prod (fun x => -r) (fun x => x) (cci a b)
  sorry
  sorry
 have hgc : is_cont g (cci a b) := by
  apply cont_on_sum f (fun x ↦ -(r * x)) (cci a b)
  · exact hfc
  · exact hrx
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
  have habb (a b : ℝ) : a / b * b = a := by sorry
  rw [habb]
 have hg'r : ∃ c ∈ (ooi a b), g' c = 0 := by
  apply rolle
  · exact hgc
  · exact hgg'
  · exact hgba
 have hf'r : ∃ c ∈ (ooi a b), f' c = r := by
  unfold g' at hg'r
  obtain ⟨c, hf'r⟩ := hg'r
  sorry
 exact hf'r
