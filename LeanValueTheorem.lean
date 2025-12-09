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
    exact const_closed_const_open a b f h
   have hf'zero : ∀ c ∈ (ooi a b), f' c = 0 := by
    apply deriv_unique (ooi a b) f f' 0 (ooi a b) --still need to prove deriv_unique
    exact ⟨hff', hzero⟩
   obtain ⟨c,hc⟩ := non_empty a b hab
   exact ⟨c, hc, hf'zero c hc⟩
 -- Now suppose f is not constant
 ·  obtain ⟨c, hc⟩ := not_const_imp_diff a b f h
    have hcdiff : f c < f a ∨ f c > f a := by
     apply lt_or_gt_of_ne
     apply hc.right
    have hbound:
    (∃ c ∈ (ooi a b), least_upper_bound f (cci a b) c) ∨
    (∃ c ∈ (ooi a b), greatest_lower_bound f (cci a b) c) := by sorry

    sorry



theorem mvt {hab : a < b} {hfc : is_cont f (cci a b)} {hff' : is_deriv (ooi a b) f f' (ooi a b)} :
 ∃ c ∈ ooi a b, f' c = (f b - f a) / (b - a) := by
 let r : ℝ := (f b - f a) / (b - a)
 let g : ℝ → ℝ := fun x => f x - r * x
 let g' : ℝ → ℝ := fun x => f' x - r
 have hext : (fun x => -(r * x)) = (fun x => -r * x) := by --these are probably unnecessary
   funext
   rw [neg_mul]
 have hgext : g = (fun x => f x + -r * x) := by
   funext
   unfold g
   rw [sub_eq_add_neg]
   rw [neg_mul]
 have hrx : is_cont (fun x => -(r * x)) (cci a b) := by
  rw [hext]
  apply cont_on_prod (fun x => -r) (fun x => x) (cci a b)
  · sorry --need to prove constant functions and f(x) = x are continuous
  · sorry
 have hgc : is_cont g (cci a b) := by
  apply cont_on_sum f (fun x ↦ -(r * x)) (cci a b)
  · exact hfc
  · exact hrx
 have hgg' : is_deriv (ooi a b) g g' (ooi a b) := by
  rw [hgext]
  unfold g'
  have hrx' : is_deriv (ooi a b) (fun x => -(r*x)) (fun x => -r) (ooi a b) := by sorry
  --refine sum_rule I f f' (ooi a b) hff' I (fun x => -(r*x)) (fun x => -r) (ooi a b) hrx'
  sorry --this is annoying, we might need to tweak sum_rule a bit
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
