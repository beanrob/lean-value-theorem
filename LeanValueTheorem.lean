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
    refine const_zero_deriv (ooi a b) f (ooi a b) ?_
    exact const_closed_imp_const_open a b f h
   have hf'zero : ∀ c ∈ (ooi a b), f' c = 0 := by
    apply deriv_unique (ooi a b) f f' 0 (ooi a b)
    exact ⟨hff', hzero⟩
   obtain ⟨c,hc⟩ := non_empty a b (ne_of_lt hab)
   exact ⟨c, hc, hf'zero c hc⟩
 -- Now suppose f is not constant
 ·  obtain ⟨c, hc⟩ := not_const_imp_diff a b f hab h
    have hcbounds :
    (∃ c ∈ (cci a b), least_upper_bound f (cci a b) (f c)) ∧
    (∃ c ∈ (cci a b), greatest_lower_bound f (cci a b) (f c)) := by
     exact cont_closed_attains_bounds f a b hfc
    -- Prove that f attains its bounds within the open interval
    have hbound:
    (∃ c ∈ (ooi a b), least_upper_bound f (cci a b) (f c)) ∨
    (∃ c ∈ (ooi a b), greatest_lower_bound f (cci a b) (f c)) := by
     by_cases h1 : f c < f a
     · have hmin : ∃ c ∈ (ooi a b), greatest_lower_bound f (cci a b) (f c) := by
        obtain ⟨c, hc⟩ := hcbounds.right; expose_names
        have hfcleqfc1 : f c ≤ f c_1 := by
         cases hc; expose_names
         unfold greatest_lower_bound at right
         cases right; expose_names
         unfold lower_bound at left_1
         exact left_1 c_1 hc_1.left
        have hfclessfa : f c < f a := by
         exact Std.lt_of_le_of_lt hfcleqfc1 h1
        have hfcnotfa : f c ≠ f a := by
         exact ne_of_lt hfclessfa
        have hfcnotfb : f c ≠ f b := by
         exact Ne.symm (ne_of_eq_of_ne hfba (id (Ne.symm hfcnotfa)))
        have hcnota : c ≠ a := by
         exact fun a_1 ↦ hfcnotfa (congrArg f a_1)
        have hcnotb : c ≠ b := by
         exact fun a ↦ hfcnotfb (congrArg f a)
        have hcopen : c ∈ ooi a b := by
         exact closed_not_bounds_open a b c hcnota hcnotb hc.left
        have hcand : (c ∈ ooi a b) ∧ greatest_lower_bound f (cci a b) (f c) := by
         exact And.imp_left (fun a ↦ hcopen) hc
        exact Exists.intro c hcand
       exact Or.inr hmin
     · rw [not_lt] at h1
       have hlt : f a < f c := by
        cases hc; expose_names; exact Std.lt_of_le_of_ne h1 (Ne.symm right)
       have hmax : ∃ c ∈ (ooi a b), least_upper_bound f (cci a b) (f c) := by
        obtain ⟨c, hc⟩ := hcbounds.left; expose_names
        have hfcgeqfc1 : f c_1 ≤ f c := by
         cases hc; expose_names
         unfold least_upper_bound at right
         cases right; expose_names
         unfold upper_bound at left_1
         exact left_1 c_1 hc_1.left
        have hfcgreaterfa : f a < f c:= by
         exact Std.lt_of_lt_of_le hlt hfcgeqfc1
        have hfcnotfa : f c ≠ f a := by
         exact Ne.symm (ne_of_lt hfcgreaterfa)
        have hfcnotfb : f c ≠ f b := by
         exact Ne.symm (ne_of_eq_of_ne hfba (id (Ne.symm hfcnotfa)))
        have hcnota : c ≠ a := by
         exact fun a_1 ↦ hfcnotfa (congrArg f a_1)
        have hcnotb : c ≠ b := by
         exact fun a ↦ hfcnotfb (congrArg f a)
        have hcopen : c ∈ ooi a b := by
         exact closed_not_bounds_open a b c hcnota hcnotb hc.left
        have hcand : (c ∈ ooi a b) ∧ least_upper_bound f (cci a b) (f c) := by
         exact And.imp_left (fun a ↦ hcopen) hc
        exact Exists.intro c hcand
       exact Or.symm (Or.inr hmax)
    -- Now prove that f'(c) = 0 at the bounds
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
       sorry
      have hderiv : is_deriv_at (ooi a b) f 0 d := by
       unfold diff at hlim
       unfold is_deriv_at
       refine fun a ↦ ?_
       expose_names
       sorry
      have hfderiv : is_deriv_at (ooi a b) f (f' d) d := by exact hff' d left
      have hunique: f' d = 0 := by
       exact deriv_at_deriv (ooi a b) 0 d f f' left hff' hderiv
      have hand : (d ∈ (ooi a b)) ∧ (f' d = 0) := by exact And.symm ⟨hunique, left⟩
      exact Exists.intro d hand
    · expose_names
      obtain ⟨d, hd⟩ := h_1
      sorry -- should be basically identical to above



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
