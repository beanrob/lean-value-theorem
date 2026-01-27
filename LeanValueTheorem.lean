-- This module serves as the root of the `LeanValueTheorem` library.
-- Import modules here that should be built as part of the library.
import LeanValueTheorem.Bounds
import LeanValueTheorem.Cont
import LeanValueTheorem.Derivatives
import LeanValueTheorem.Intervals
import LeanValueTheorem.Limits
import LeanValueTheorem.Misc
import LeanValueTheorem.Sequences

variable {a b : ℝ} {f f' : ℝ → ℝ}



-- Proof of Rolle's theorem

theorem rolle {hab : a < b} {hfc : is_cont f (cci a b)} {hff' : is_deriv (ooi a b) f f' (ooi a b)}
 {hfba : f b = f a} : ∃ c ∈ (ooi a b), f' c = 0 := by
 have hab' := ne_of_lt hab -- useful for some interval stuff
 by_cases h : is_const_fun (cci a b) f

 -- First suppose f is a constant function
 · have hzero : is_deriv (ooi a b) f 0 (ooi a b) := by
    refine const_zero_deriv (ooi a b) f (ooi a b) ?_
    exact const_closed_imp_const_open a b f h
   have hf'zero := fun c a_1 ↦ deriv_at_deriv (ooi a b) 0 c f f' a_1 hff' (hzero c a_1)
   obtain ⟨c,hc⟩ := non_empty a b hab'
   exact ⟨c, hc, hf'zero c hc⟩


 -- Now suppose f is not constant
 ·  obtain ⟨c, hc⟩ := not_const_imp_diff a b f hab h
    have hcbounds := cont_closed_attains_bounds f a b hfc

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
        have hfclessfa := Std.lt_of_le_of_lt hfcleqfc1 h1
        have hfcnotfa := ne_of_lt hfclessfa
        have hfcnotfb := Ne.symm (ne_of_eq_of_ne hfba (id (Ne.symm hfcnotfa)))
        have hcnota := fun a_1 ↦ hfcnotfa (congrArg f a_1)
        have hcnotb := fun a ↦ hfcnotfb (congrArg f a)
        have hcopen := closed_not_bounds_open a b c hcnota hcnotb hc.left
        exact Exists.intro c (And.imp_left (fun a ↦ hcopen) hc)
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
        have hfcgreaterfa := Std.lt_of_lt_of_le hlt hfcgeqfc1
        have hfcnotfa := Ne.symm (ne_of_lt hfcgreaterfa)
        have hfcnotfb := Ne.symm (ne_of_eq_of_ne hfba (id (Ne.symm hfcnotfa)))
        have hcnota := fun a_1 ↦ hfcnotfa (congrArg f a_1)
        have hcnotb := fun a ↦ hfcnotfb (congrArg f a)
        have hcopen := closed_not_bounds_open a b c hcnota hcnotb hc.left
        exact Exists.intro c (And.imp_left (fun a ↦ hcopen) hc)
       exact Or.symm (Or.inr hmax)

    -- Now prove that f'(c) = 0 at the bounds

    -- f is not constant so it has either a LUB or GLB in the open interval; we split these cases
    cases hbound;

    · expose_names; obtain ⟨d, hd⟩ := h_1
      let diff : ℝ → ℝ := fun x => (f (d + x) - f d) / x
      cases hd; expose_names
      unfold least_upper_bound at right
      cases right; expose_names
      unfold upper_bound at left_1

      -- diff is non-positive when h > 0 and non-negative when h < 0
      have hxp : ∀ x ∈ {h | d + h ∈ ooi a b ∧ h > 0}, diff x ≤ 0 := by
       unfold diff
       refine fun x a ↦ ?_
       cases a; expose_names
       have hxp_1 : f (d + x) - f d ≤ 0 := by
        apply open_in_closed at left_2
        exact tsub_nonpos.mpr (left_1 (d + x) left_2)
       apply div_nonpos_of_nonpos_of_nonneg
       · exact hxp_1
       · exact Std.le_of_lt right_1

      have hxn : ∀ x ∈ {h | d + h ∈ ooi a b ∧ h < 0}, diff x ≥ 0 := by
       unfold diff
       refine fun x a ↦ ?_
       cases a; expose_names
       have hxn_1 : f (d + x) - f d ≤ 0 := by
        apply open_in_closed at left_2
        exact tsub_nonpos.mpr (left_1 (d + x) left_2)
       apply div_nonneg_of_nonpos
       · exact hxn_1
       · exact Std.le_of_lt right_1

      -- why we define diff - if we can prove this limit is 0 then we have the result
      have hset := hunionrw (ooi a b) d
      have hlimderiv (l : ℝ) : is_lim_fun ({h | d + h ∈ ooi a b ∧ h < 0}
                                 ∪ {h | d + h ∈ ooi a b ∧ h > 0}) diff 0 l
                            ↔ is_deriv_at (ooi a b) f l d := by
       rw [iff_def]; and_intros
       · unfold is_deriv_at
         refine fun y ↦ ?_
         refine fun z ↦ ?_
         rw [hset] at y
         exact y
       · unfold is_deriv_at
         refine fun y ↦ ?_
         apply y at left
         rw [hset]
         exact left

       -- The following rewrites are proven in the Misc file
      have hopen := openrw1 a b d hab
      have hopen1 := openrw2 a b d hab left
      have hopen2 := openrw3 a b d hab left

      -- if limsup exists it must be non-positive, if liminf exists it must be non-negative
      have hlimsup (l : ℝ) : is_lim_fun {h | d + h ∈ ooi a b ∧ h > 0} diff 0 l → l ≤ 0 := by
       refine fun z ↦ ?_
       rw [hopen1] at z
       rw [hopen1] at hxp
       have h1 : ¬(0 = b - d) := by
        rw [← ne_eq]
        rw [ne_comm]
        rw [sub_ne_zero]
        rw [ne_comm]
        exact (bounds_not_in_open a b d left).right
       have h2 := (bounds_in_closed 0 (b - d)).left
       exact fun_non_positive 0 l 0 (b - d) diff h1 h2 z hxp
      have hliminf (l : ℝ) : is_lim_fun {h | d + h ∈ ooi a b ∧ h < 0} diff 0 l → l ≥ 0 := by
       refine fun z ↦ ?_
       rw [hopen2] at z
       rw [hopen2] at hxn
       have h1 : ¬(a - d = 0) := by
        rw [← ne_eq]
        rw [sub_ne_zero]
        rw [ne_comm]
        exact (bounds_not_in_open a b d left).left
       have h2 := (bounds_in_closed (a - d) 0).right
       exact fun_non_negative 0 l (a - d) 0 diff h1 h2 z hxn

      -- the derivative of f exists at d, it follows that the limit of diff as h tends to 0 exists
      have hderivexists : ∃ l, is_deriv_at (ooi a b) f l d := by
       exact ⟨(f' d), (hff' d left)⟩
      have hlimexists := (exists_congr hlimderiv).mpr hderivexists

      -- of course if the limit exists then so do liminf and limsup
      have hlimsupexists := lim_exists_on_subset ({h | d + h ∈ ooi a b ∧ h < 0}
                                                ∪ {h | d + h ∈ ooi a b ∧ h > 0})
           {h | d + h ∈ ooi a b ∧ h > 0} diff 0 Set.subset_union_right hlimexists
      have hliminfexists := lim_exists_on_subset ({h | d + h ∈ ooi a b ∧ h < 0}
                                                ∪ {h | d + h ∈ ooi a b ∧ h > 0})
           {h | d + h ∈ ooi a b ∧ h < 0} diff 0 Set.subset_union_left hlimexists
      obtain ⟨n, hn⟩ := hlimsupexists
      obtain ⟨m, hm⟩ := hliminfexists

      -- if the limit exists then it must equal zero
      have hlimzero (l : ℝ): is_lim_fun ({h | d + h ∈ ooi a b ∧ h < 0}
                                   ∪ {h | d + h ∈ ooi a b ∧ h > 0}) diff 0 l → l = 0 := by
       refine fun z ↦ ?_
       have : l = m ∧ l = n := by
        refine lim_union (a - d) 0 0 (b - d) diff 0 l m n ?_ ?_ ?_ ?_ ?_ ?_
        · rw [← ne_eq]
          rw [sub_ne_zero]
          rw [ne_comm]
          exact (bounds_not_in_open a b d left).left
        · rw [← ne_eq]
          rw [ne_comm]
          rw [sub_ne_zero]
          rw [ne_comm]
          exact (bounds_not_in_open a b d left).right
        · rw [hopen2] at hm; exact hm
        · rw [hopen1] at hn; exact hn
        · rw [hopen2] at z; rw [hopen1] at z; exact z
        · exact ⟨(bounds_in_closed (a - d) 0).right, (bounds_in_closed 0 (b - d)).left⟩
       have hn' := hlimsup n hn
       have hm' := hliminf m hm
       cases this; expose_names
       have := le_of_eq_of_le right_1 (hlimsup n hn)
       have := le_of_le_of_eq (hliminf m hm) (id (Eq.symm left_2)); expose_names
       apply le_antisymm
       · exact this_1
       · exact this

      -- so the limit is zero
      have hlim : is_lim_fun ({h | d + h ∈ ooi a b ∧ h < 0}
                            ∪ {h | d + h ∈ ooi a b ∧ h > 0}) diff 0 0 := by
       obtain ⟨l, hl⟩ := hlimexists
       apply hlimzero at l; expose_names
       let htemp := hl
       apply l at htemp
       rw [htemp] at hl
       exact hl

      -- so the derivative at d is zero
      have hderiv : is_deriv_at (ooi a b) f 0 d := by
       unfold diff at hlim
       unfold is_deriv_at
       refine fun a ↦ ?_
       rw [hset] at hlim
       exact hlim
      have hfderiv := hff' d left
      have hunique := deriv_at_deriv (ooi a b) 0 d f f' left hff' hderiv
      exact Exists.intro d (And.symm ⟨hunique, left⟩)



      -- now the second case; the proof is practically identical but with some inequalities reversed
    · expose_names
      obtain ⟨d, hd⟩ := h_1
      let diff : ℝ → ℝ := fun x => (f (d + x) - f d) / x
      cases hd; expose_names
      unfold least_upper_bound at right
      cases right; expose_names
      unfold upper_bound at left_1
      have hxp : ∀ x ∈ {h | d + h ∈ ooi a b ∧ h > 0}, diff x ≥ 0 := by
       unfold diff
       refine fun x a ↦ ?_
       cases a; expose_names
       have hxp_1 : f (d + x) - f d ≥ 0 := by
        apply open_in_closed at left_2
        exact sub_nonneg_of_le (left_1 (d + x) left_2)
       apply div_nonneg
       · exact hxp_1
       · exact Std.le_of_lt right_1
      have hxn : ∀ x ∈ {h | d + h ∈ ooi a b ∧ h < 0}, diff x ≤ 0 := by
       unfold diff
       refine fun x a ↦ ?_
       cases a; expose_names
       have hxn_1 : f (d + x) - f d ≥ 0 := by
        apply open_in_closed at left_2
        exact sub_nonneg_of_le (left_1 (d + x) left_2)
       apply div_nonpos_of_nonneg_of_nonpos
       · exact hxn_1
       · exact Std.le_of_lt right_1
      have hset := hunionrw (ooi a b) d
      have hlimderiv (l : ℝ) : is_lim_fun ({h | d + h ∈ ooi a b ∧ h < 0}
                                 ∪ {h | d + h ∈ ooi a b ∧ h > 0}) diff 0 l
                     ↔ is_deriv_at (ooi a b) f l d := by
       rw [iff_def]; and_intros
       · unfold is_deriv_at
         refine fun y ↦ ?_
         refine fun z ↦ ?_
         rw [hset] at y
         exact y
       · unfold is_deriv_at
         refine fun y ↦ ?_
         apply y at left
         rw [hset]
         exact left
      have hopen := openrw1 a b d hab
      have hopen1 := openrw2 a b d hab left
      have hopen2 := openrw3 a b d hab left
      have hlimsup (l : ℝ) : is_lim_fun {h | d + h ∈ ooi a b ∧ h > 0} diff 0 l → l ≥ 0 := by
       refine fun z ↦ ?_
       rw [hopen1] at z
       rw [hopen1] at hxp
       have h1 : ¬(0 = b - d) := by
        rw [← ne_eq]
        rw [ne_comm]
        rw [sub_ne_zero]
        rw [ne_comm]
        exact (bounds_not_in_open a b d left).right
       have h2 := (bounds_in_closed 0 (b - d)).left
       exact fun_non_negative 0 l 0 (b - d) diff h1 h2 z hxp
      have hliminf (l : ℝ) : is_lim_fun {h | d + h ∈ ooi a b ∧ h < 0} diff 0 l → l ≤ 0 := by
       refine fun z ↦ ?_
       rw [hopen2] at z
       rw [hopen2] at hxn
       have h1 : ¬(a - d = 0) := by
        rw [← ne_eq]
        rw [sub_ne_zero]
        rw [ne_comm]
        exact (bounds_not_in_open a b d left).left
       have h2 := (bounds_in_closed (a - d) 0).right
       exact fun_non_positive 0 l (a - d) 0 diff h1 h2 z hxn
      have hderivexists : ∃ l, is_deriv_at (ooi a b) f l d := by
       exact ⟨(f' d), (hff' d left)⟩
      have hlimexists := (exists_congr hlimderiv).mpr hderivexists
      have hlimsupexists := lim_exists_on_subset ({h | d + h ∈ ooi a b ∧ h < 0}
                                                ∪ {h | d + h ∈ ooi a b ∧ h > 0})
           {h | d + h ∈ ooi a b ∧ h > 0} diff 0 Set.subset_union_right hlimexists
      have hliminfexists := lim_exists_on_subset ({h | d + h ∈ ooi a b ∧ h < 0}
                                                ∪ {h | d + h ∈ ooi a b ∧ h > 0})
           {h | d + h ∈ ooi a b ∧ h < 0} diff 0 Set.subset_union_left hlimexists
      obtain ⟨n, hn⟩ := hlimsupexists
      obtain ⟨m, hm⟩ := hliminfexists
      have hlimzero (l : ℝ): is_lim_fun ({h | d + h ∈ ooi a b ∧ h < 0}
                                   ∪ {h | d + h ∈ ooi a b ∧ h > 0}) diff 0 l → l = 0 := by
       refine fun z ↦ ?_
       have : l = m ∧ l = n := by
        refine lim_union (a - d) 0 0 (b - d) diff 0 l m n ?_ ?_ ?_ ?_ ?_ ?_
        · rw [← ne_eq]
          rw [sub_ne_zero]
          rw [ne_comm]
          exact (bounds_not_in_open a b d left).left
        · rw [← ne_eq]
          rw [ne_comm]
          rw [sub_ne_zero]
          rw [ne_comm]
          exact (bounds_not_in_open a b d left).right
        · rw [hopen2] at hm; exact hm
        · rw [hopen1] at hn; exact hn
        · rw [hopen2] at z; rw [hopen1] at z; exact z
        · exact ⟨(bounds_in_closed (a - d) 0).right, (bounds_in_closed 0 (b - d)).left⟩
       have hn' := hlimsup n hn
       have hm' := hliminf m hm
       cases this; expose_names
       have := le_of_eq_of_le left_2 (hliminf m hm)
       have := le_of_le_of_eq (hlimsup n hn) (id (Eq.symm right_1)) ; expose_names
       apply le_antisymm
       · exact this_1
       · exact this
      have hlim : is_lim_fun ({h | d + h ∈ ooi a b ∧ h < 0}
                            ∪ {h | d + h ∈ ooi a b ∧ h > 0}) diff 0 0 := by
       obtain ⟨l, hl⟩ := hlimexists
       apply hlimzero at l; expose_names
       let htemp := hl
       apply l at htemp
       rw [htemp] at hl
       exact hl
      have hderiv : is_deriv_at (ooi a b) f 0 d := by
       unfold diff at hlim
       unfold is_deriv_at
       refine fun a ↦ ?_
       rw [hset] at hlim
       exact hlim
      have hfderiv := hff' d left
      have hunique := deriv_at_deriv (ooi a b) 0 d f f' left hff' hderiv
      exact Exists.intro d (And.symm ⟨hunique, left⟩)



-- Proof of the mean value theorem

theorem mvt {hab : a < b} {hfc : is_cont f (cci a b)} {hff' : is_deriv (ooi a b) f f' (ooi a b)} :
 ∃ c ∈ ooi a b, f' c = (f b - f a) / (b - a) := by

 -- We define a new function g with g(a) = g(b) and apply Rolle's theorem
 let r : ℝ := (f b - f a) / (b - a)
 let g : ℝ → ℝ := fun x => f x - r * x
 let g' : ℝ → ℝ := fun x => f' x - r

 -- Useful rewrite
 have hext : (fun x => -(r * x)) = (fun x => -r * x) := by
   funext
   rw [neg_mul]

 -- Prove g is continuous
 have hrx : is_cont (fun x => -(r * x)) (cci a b) := by
  rw [hext]
  apply cont_on_prod (fun x => -r) (fun x => x) (cci a b)
  · exact const_cont (-r) (cci a b)
  · exact id_cont (cci a b)
 have hgc : is_cont g (cci a b) := by
  apply cont_on_sum f (fun x ↦ -(r * x)) (cci a b)
  · exact hfc
  · exact hrx

 -- Prove g' is the derivative of g - the work for this is done in the Derivatives file
 have hgg' := g_deriv (ooi a b) r f f' hff'

 -- Prove g(a) = g(b)
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

 -- Finally apply Rolle's theorem to g
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
