import LeanValueTheorem.Intervals

-- Definition for f : D → ℝ being a constant function
def is_const_fun (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ D ∧ y ∈ D → f x = f y

-- If f is constant on [a,b] then it is constant on (a,b)
lemma const_closed_imp_const_open (a b : ℝ) (f : ℝ → ℝ) :
 is_const_fun (cci a b) f → is_const_fun (ooi a b) f := by
 intro h
 unfold is_const_fun at h
 unfold is_const_fun
 refine fun x y a ↦ ?_
 apply h
 cases a; expose_names
 apply open_in_closed at left
 apply open_in_closed at right
 exact ⟨left, right⟩

-- f is constant on the closed interval [a,b] if and only if f(x) = f(a) for all x in [a,b]
lemma closed_const (a b : ℝ) (f : ℝ → ℝ) {hab : a < b} :
 is_const_fun (cci a b) f ↔ ∀ x ∈ (cci a b), f x = f a := by
 rw [iff_def]
 and_intros
 · intro h
   unfold is_const_fun at h
   have ha : a ∈ (cci a b) := by
    have hz : a ≤ a := by exact Std.IsPreorder.le_refl a
    have hb : a ≤ b := by exact Std.le_of_lt hab
    exact Set.mem_sep (min_le_left a b) (le_max_left a b)
   refine fun x a ↦ ?_
   apply h
   exact ⟨a, ha⟩
 · intro h
   unfold is_const_fun
   refine fun x y a ↦ ?_
   cases a; expose_names
   apply h at left
   apply h at right
   apply Eq.trans left
   exact Eq.symm right

-- If f is NOT constant on [a,b] then f(x) differs from f(a) for some x in [a,b]
lemma not_const_imp_diff (a b : ℝ) (f : ℝ → ℝ) (hab : a < b) :
 ¬is_const_fun (cci a b) f → ∃ x : ℝ, x ∈ (cci a b) ∧ f x ≠ f a := by
 contrapose
 intro h
 rw [not_not]
 rw [closed_const]
 · rw [not_exists] at h
   refine fun x a ↦ ?_
   apply h at x
   rw [not_and_not_right] at x
   exact x a
 · exact hab

-- Some rewrites to be used in the proof of Rolle's theorem

lemma hunionrw (I : Set ℝ) (d : ℝ) :
 ({h | d + h ∈ I ∧ h < 0} ∪ {h | d + h ∈ I ∧ h > 0})
                                 = {h | d + h ∈ I ∧ h ≠ 0} := by
 repeat rw [Set.setOf_and]
 rw [← Set.inter_union_distrib_left {a_1 | d + a_1 ∈ I} {a | a < 0} {a | a > 0}]
 rw [← Set.setOf_or]
 simp

lemma openrw1 (a b d : ℝ) (hab : a < b) : {h | d + h ∈ ooi a b} = ooi (a - d) (b - d) := by
       unfold ooi
       rw [min_sub_sub_right a b d]
       rw [max_sub_sub_right a b d]
       rw [min_eq_left_of_lt hab]
       rw [max_eq_right_of_lt hab]
       refine Set.setOf_inj.mpr ?_
       funext; expose_names
       simp
       rw[iff_def]
       and_intros
       · refine fun c ↦ ?_
         and_intros
         · cases c; expose_names
           exact sub_left_lt_of_lt_add left
         · cases c; expose_names
           exact lt_tsub_iff_left.mpr right
       · refine fun c ↦ ?_
         and_intros
         · cases c; expose_names
           exact lt_add_of_tsub_lt_left left
         · cases c; expose_names
           exact lt_tsub_iff_left.mp right

lemma openrw2 (a b d : ℝ) (hab : a < b) (hd : d ∈ ooi a b) :
 {h | d + h ∈ ooi a b ∧ h > 0} = ooi 0 (b - d) := by
       rw [Set.setOf_and]
       rw [openrw1 a b d hab]
       unfold ooi
       rw [← Set.setOf_and]
       rw [min_sub_sub_right]
       rw [min_eq_left_of_lt hab]
       rw [max_sub_sub_right]
       rw [max_eq_right_of_lt hab]
       have had: a - d < 0 := by
        unfold ooi at hd
        rw [min_eq_left_of_lt hab] at hd
        rw [Set.mem_setOf] at hd
        apply sub_neg_of_lt hd.left
       have hbd: b - d > 0 := by
        unfold ooi at hd
        rw [max_eq_right_of_lt hab] at hd
        rw [Set.mem_setOf] at hd
        refine sub_pos.mpr hd.right
       rw [show
           {a_1 | (a - d < a_1 ∧ a_1 < b - d) ∧ a_1 > 0} = fun a_1 ↦
             (a - d < a_1 ∧ a_1 < b - d) ∧ a_1 > 0
           from rfl]
       rw [show
           {x | min 0 (b - d) < x ∧ x < max 0 (b - d)} = fun x ↦
             min 0 (b - d) < x ∧ x < max 0 (b - d)
           from rfl]
       funext; expose_names
       rw [and_assoc]
       nth_rw 2 [and_comm]
       rw [← and_assoc]
       rw [← max_lt_iff]
       rw [max_eq_right (le_of_lt had)]
       rw [min_eq_left (le_of_lt hbd)]
       rw [max_eq_right (le_of_lt hbd)]

lemma openrw3 (a b d : ℝ) (hab : a < b) (hd : d ∈ ooi a b) :
 {h | d + h ∈ ooi a b ∧ h < 0} = ooi (a - d) 0 := by
       rw [Set.setOf_and]
       rw [openrw1 a b d hab]
       unfold ooi
       rw [← Set.setOf_and]
       rw [min_sub_sub_right]
       rw [min_eq_left_of_lt hab]
       rw [max_sub_sub_right]
       rw [max_eq_right_of_lt hab]
       have had: a - d < 0 := by
        unfold ooi at hd
        rw [min_eq_left_of_lt hab] at hd
        rw [Set.mem_setOf] at hd
        apply sub_neg_of_lt hd.left
       have hbd: b - d > 0 := by
        unfold ooi at hd
        rw [max_eq_right_of_lt hab] at hd
        rw [Set.mem_setOf] at hd
        refine sub_pos.mpr hd.right
       rw [show
           {a_1 | (a - d < a_1 ∧ a_1 < b - d) ∧ a_1 < 0} = fun a_1 ↦
             (a - d < a_1 ∧ a_1 < b - d) ∧ a_1 < 0
           from rfl]
       rw [show
           {x | min (a - d) 0 < x ∧ x < max (a - d) 0} = fun x ↦
             min (a - d) 0 < x ∧ x < max (a - d) 0
           from rfl]
       funext; expose_names
       rw [and_assoc]
       rw [← lt_inf_iff]
       rw [max_eq_right (le_of_lt had)]
       rw [inf_comm (b - d) 0]
       rw [min_eq_left (le_of_lt hbd)]
       rw [min_eq_left (le_of_lt had)]

-- These two are used for uniqueness of limits/derivatives
lemma openrw4 (a b d : ℝ) (hab : a < b) (hd : d ∈ ooi a b) :
 {h | d + h ∈ ooi a b ∧ h ≠ 0} = ooi (a - d) (b - d) \ {0} := by
 rw [Set.setOf_and]
 rw [openrw1 a b d hab]
 exact rfl

lemma openrw5 (a b d : ℝ) (hab : a < b) (hd : d ∈ ooi a b) :
 ooi a b \ {d} = ooi a d ∪ ooi d b := by
 unfold ooi
 unfold ooi at hd
 rw [min_eq_left_of_lt hab] at hd
 rw [max_eq_right_of_lt hab] at hd
 rw [show (d ∈ {x | a < x ∧ x < b}) = (a < d ∧ d < b) from rfl] at hd
 rw [min_eq_left_of_lt hab]
 rw [max_eq_right_of_lt hab]
 rw [min_eq_left_of_lt hd.left]
 rw [max_eq_right_of_lt hd.left]
 rw [min_eq_left_of_lt hd.right]
 rw [max_eq_right_of_lt hd.right]
 sorry
