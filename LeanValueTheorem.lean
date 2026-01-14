-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import LeanValueTheorem.Bounds
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals
import LeanValueTheorem.Limits
import LeanValueTheorem.Misc
import LeanValueTheorem.Sequences

variable {a b : ℝ} {f f' : ℝ → ℝ} {I : Set ℝ}

theorem rolle {hab : a < b} {hfc : is_cont f (cci a b)} {hff' : is_deriv (ooi a b) f f' (ooi a b)}
 {hfba : f b = f a} : ∃ c ∈ (ooi a b), f' c = 0 := by
 by_cases h : is_const_fun (cci a b) f
 -- First suppose f is a constant function
 · have hzero : is_deriv (ooi a b) f 0 (ooi a b) := by
    refine const_zero_deriv (ooi a b) f ?_
    exact const_closed_imp_const_open a b f h
   have hf'zero : ∀ c ∈ (ooi a b), f' c = 0 := by
    apply deriv_unique (ooi a b) f f' 0 (ooi a b)
    exact ⟨hff', hzero⟩
   obtain ⟨c,hc⟩ := non_empty a b hab
   exact ⟨c, hc, hf'zero c hc⟩
 -- Now suppose f is not constant
 ·  obtain ⟨c, hc⟩ := not_const_imp_diff a b f hab h
    have hbound:
    (∃ c ∈ (ooi a b), least_upper_bound f (cci a b) (f c)) ∨
    (∃ c ∈ (ooi a b), greatest_lower_bound f (cci a b) (f c)) := by
     by_cases h1 : f c < f a
     · have hmin : ∃ c ∈ (ooi a b), least_upper_bound f (cci a b) (f c) := by
        sorry
       exact Or.symm (Or.inr hmin)
     · rw [not_lt] at h1
       have hlt : f a < f c := by
        cases hc; expose_names; exact Std.lt_of_le_of_ne h1 (Ne.symm right)
       have hmax : ∃ c ∈ (ooi a b), greatest_lower_bound f (cci a b) (f c) := by
        sorry
       exact Or.inr hmax
    cases hbound; expose_names
    · obtain ⟨d, hd⟩ := h_1
      let diff : ℝ → ℝ := fun x => (f (d + x) - f d) / x
      cases hd; expose_names
      unfold least_upper_bound at right
      cases right; expose_names
      unfold upper_bound at left_1
      have hxp : ∀ x, d + x ∈ (ooi a b) ∧ x > 0 → diff x ≤ 0 := by
       unfold diff
       refine fun x a ↦ ?_
       cases a; expose_names
       have hxp_1 : f (d + x) - f d ≤ 0 := by
        apply open_in_closed at left_2
        exact tsub_nonpos.mpr (left_1 (d + x) left_2)
       apply div_nonpos_of_nonpos_of_nonneg
       exact hxp_1
       exact Std.le_of_lt right_1
      have hxn : ∀ x, d + x ∈ (ooi a b) ∧ x < 0 → diff x ≥ 0 := by
       unfold diff
       refine fun x a ↦ ?_
       cases a; expose_names
       have hxn_1 : f (d + x) - f d ≤ 0 := by
        apply open_in_closed at left_2
        exact tsub_nonpos.mpr (left_1 (d + x) left_2)
       apply div_nonneg_of_nonpos
       exact hxn_1
       exact Std.le_of_lt right_1
      have hlim : is_lim_fun (ooi a b) diff 0 0 := by
       unfold is_lim_fun
       sorry
      sorry
    · expose_names
      obtain ⟨d, hd⟩ := h_1
      sorry



theorem mvt {hab : a < b} {hfc : is_cont f (cci a b)} {hff' : is_deriv (ooi a b) f f' (ooi a b)} :
 ∃ c ∈ ooi a b, f' c = (f b - f a) / (b - a) := by
 let r : ℝ := (f b - f a) / (b - a)
 let g : ℝ → ℝ := fun x => f x - r * x
 let g' : ℝ → ℝ := fun x => f' x - r
 have hext : (fun x => -(r * x)) = (fun x => -r * x) := by
   funext
   rw [neg_mul]
 have hrx : is_cont (fun x => -(r * x)) (cci a b) := by
  rw [hext]
  apply cont_on_prod (fun x => -r) (fun x => x) (cci a b)
  · exact const_cont (-r) (cci a b)
  · exact id_cont (cci a b)
 have hgc : is_cont g (cci a b) := by
  apply cont_on_sum f (fun x ↦ -(r * x)) (cci a b)
  · exact hfc
  · exact hrx
 have hgg' : is_deriv (ooi a b) g g' (ooi a b) := by
  exact g_deriv (ooi a b) r f f' hff'
 have hgba : g b = g a:= by
  unfold g
  rw [sub_eq_iff_eq_add']
  rw [← add_sub_assoc]
  rw [add_comm]
  rw [add_sub_assoc]
  rw [← sub_eq_iff_eq_add']
  rw [← mul_sub]
  unfold r
  have hbaz : b - a ≠ 0 := by
   apply sub_ne_zero_of_ne
   exact Ne.symm (ne_of_lt hab)
  exact Eq.symm (div_mul_cancel₀ (f b - f a) hbaz)
 have hg'r : ∃ c ∈ (ooi a b), g' c = 0 := by
  apply rolle
  · exact hab
  · exact hgc
  · exact hgg'
  · exact hgba
 unfold g' at hg'r
 obtain ⟨c,hc⟩ := hg'r
 rw [sub_eq_zero] at hc
 exact Exists.intro c hc
