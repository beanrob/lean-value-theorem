import LeanValueTheorem.Bolzano_Weierstrass

theorem cont_closed_imp_bounded (f : ℝ → ℝ) (a b : ℝ) (hfc : is_cont f (cci a b)) :
  BddAbove (f '' (cci a b)) ∧ BddBelow (f '' (cci a b)) := by

  by_contra h
  rw [not_and_or] at h

  -- unboundedness
  have ex (n : ℝ) : ∃ x ∈ cci a b, n < |f x| := by
    cases h with
    | inl hl =>
      unfold BddAbove upperBounds at hl
      simp at hl
      rw [Set.not_nonempty_iff_eq_empty] at hl
      rw [←Set.compl_univ_iff] at hl
      have part : n ∈ Set.univ := by trivial
      rw [←hl] at part
      simp at part
      rcases part with ⟨x, hx, x_prop⟩
      refine ⟨x, hx, lt_of_lt_of_le x_prop (le_abs_self (f x))⟩
    | inr hr =>
      unfold BddBelow lowerBounds at hr
      simp at hr
      rw [Set.not_nonempty_iff_eq_empty] at hr
      rw [←Set.compl_univ_iff] at hr
      have part : -n ∈ Set.univ := by trivial
      rw [←hr] at part
      simp at part
      rcases part with ⟨x, hx, x_prop⟩
      refine ⟨x, hx, lt_of_lt_of_le (by simpa using (neg_lt_neg x_prop)) (neg_le_abs (f x))⟩

  -- get sequence that diverges and converges at the same time
  set g : ℕ → ℝ := fun n => Classical.choose (ex n) with hg
  have g_bounds (n : ℕ) := (Classical.choose_spec (ex n)).1
  have fx_bounds (n : ℝ) := (Classical.choose_spec (ex n)).2

  have hgb : BddAbove (g '' Set.univ) := by
    unfold BddAbove upperBounds
    simp
    rw [Set.nonempty_def, ←Set.eq_mem_setOf]
    use max a b
    intro x
    rw [hg]
    exact (g_bounds x).right

  have hgl : BddBelow (g '' Set.univ) := by
    unfold BddBelow lowerBounds
    simp
    rw [Set.nonempty_def, ←Set.eq_mem_setOf]
    use min a b
    intro x
    rw [hg]
    exact (g_bounds x).left

  rcases Bolzano.Bolzano_weierstrass g (by trivial) hgb hgl with ⟨k, mono, lim, hgk_lim⟩

  -- show the limit of subseqeuence lies in cci a b
  have gk_bounds (n : ℕ) : (fun n ↦ g (k n)) n ∈ cci a b := by simpa using g_bounds (k n)
  have gk_lim := sequence_in_closed (fun n => g (k n)) lim a b gk_bounds hgk_lim

  -- use continuity to show f ∘ g ∘ k → f
  have cont_at := hfc lim gk_lim
  unfold is_cont is_cont_at is_cont_at_seq at cont_at
  have f_lim := cont_at.right gk_lim (fun n => g (k n)) gk_bounds hgk_lim
  rcases f_lim 1 (by norm_num) with ⟨N, hf_prop⟩

  -- contradict unboundedness with convergence
  have nat (x : ℝ) : ∃n : ℕ, x < n := by exact exists_nat_gt x
  rcases nat (max N (1 + |f lim|)) with ⟨n, hxn⟩
  have this1 := fx_bounds (k n)
  have maxN := by simpa only [max_comm] using (le_max_right (1 + |f lim|) N )

  have this2 := lt_of_le_of_lt maxN hxn
  norm_cast at this2
  have this3 := hf_prop (n) (le_of_lt this2)
  simp at this3

  have this4 := abs_sub_le (f (g (k n))) (f lim) 0
  simp at this4
  have this5 := le_add_of_le_add_right this4 (le_of_lt this3)
  have maxf := by simpa only [max_comm] using (le_max_left (1 + |f lim|) N )

  have hn_to_hkn : (n : ℝ) ≤ (k n : ℝ) := by exact_mod_cast (mono.id_le n)
  have this6 := lt_trans (lt_of_lt_of_le (lt_of_le_of_lt maxf hxn) hn_to_hkn) this1
  exact (not_lt_of_ge this5) this6

lemma bounded_has_LUB_and_GLB (f : ℝ → ℝ) (I : Set ℝ) (hI : I ≠ ∅) (hBA : BddAbove (f '' I))
 (hBB : BddBelow (f '' I)) : (∃ U, IsLUB (f '' I) U) ∧ (∃ L, IsGLB (f '' I) L) := by
 constructor
 · refine Real.exists_isLUB ?_ hBA
   refine Set.Nonempty.image f ?_
   rw [Set.nonempty_iff_ne_empty]
   exact hI
 · refine Real.exists_isGLB ?_ hBB
   refine Set.Nonempty.image f ?_
   rw [Set.nonempty_iff_ne_empty]
   exact hI

theorem cont_closed_attains_bounds (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
                                   (cont : is_cont f (cci a b)) :
  (∃ x ∈ (cci a b), IsLUB (f '' (cci a b)) (f x)) ∧
  (∃ x ∈ (cci a b), IsGLB (f '' (cci a b))  (f x)) := by

  have nonempty : (cci a b) ≠ ∅ := by
   have := ne_of_lt hab
   apply non_empty_closed a b at this
   exact Ne.symm ((fun {α} {s} ↦ Set.nonempty_iff_empty_ne.mp) this)
  have boundedness := cont_closed_imp_bounded f a b cont
  have bounds := bounded_has_LUB_and_GLB f (cci a b) nonempty boundedness.left boundedness.right
  obtain ⟨hupper, hlower⟩ := bounds
  obtain ⟨U, hupper⟩ := hupper
  obtain ⟨L, hlower⟩ := hlower
  constructor

  -- upper bound first
  · have : ∃ x ∈ cci a b, f x = U := by

     -- suppose there is no x with f x = U
     by_contra h
     rw [not_exists] at h
     have hfneU : ∀ x ∈ cci a b, f x ≠ U := by
      refine fun x z ↦ ?_
      specialize h x
      rw [not_and] at h
      exact h z

     -- then f is strictly less than U
     have : ∀ x ∈ cci a b, f x < U := by
      have Uupper := Set.mem_of_mem_inter_left hupper
      unfold upperBounds at Uupper
      refine fun x z ↦ ?_
      have := Set.mem_image_of_mem f z
      exact Std.lt_of_le_of_ne (Uupper this) (hfneU x z)

     -- define a new function g
     let g : ℝ → ℝ := fun x => 1 / (U - f x)

     -- g is positive
     have hgpos : ∀ x ∈ cci a b, g x > 0 := by
      unfold g
      refine fun x z ↦ ?_
      simp
      exact this x z

     -- prove g is continuous
     have hgcont : is_cont g (cci a b) := by
      refine @cont_on_quot (fun x ↦ 1) (fun x ↦ U - f x) (cci a b) ?_ ?_ ?_
      · exact fun x a ↦ sub_ne_zero_of_ne fun a_1 ↦ hfneU x a (id (Eq.symm a_1))
      · exact const_cont 1 (cci a b)
      · refine @cont_on_sum (fun x ↦ U) (fun x ↦ -f x) (cci a b) ?_ ?_
        · exact const_cont U (cci a b)
        · have : (fun x ↦ -f x) = (fun x ↦ (-1 * f x)) := by
           funext; expose_names
           exact neg_eq_neg_one_mul (f x)
          rw [this]
          exact cont_on_scalar_prod f (cci a b) (-1) cont

     -- so g is bounded (we only use the upper bound)
     have hgbounded := cont_closed_imp_bounded g a b hgcont
     have gbounds := bounded_has_LUB_and_GLB g (cci a b) nonempty
                                             hgbounded.left hgbounded.right
     obtain ⟨K, hK⟩ := gbounds.left

     -- the upper bound of g is positive
     have hKpos : K > 0 := by
      have Kupper := Set.mem_of_mem_inter_left hK
      unfold upperBounds at Kupper
      have := non_empty_closed a b (ne_of_lt hab)
      obtain ⟨c, hc⟩ := this
      have := Set.mem_image_of_mem g hc
      apply Kupper at this
      exact Std.lt_of_lt_of_le (hgpos c hc) this

     -- g is less than or equal to K
     have : ∀ x ∈ cci a b, g x ≤ K := by
      have Kupper := Set.mem_of_mem_inter_left hK
      unfold upperBounds at Kupper
      refine fun x z ↦ ?_
      exact Kupper (Set.mem_image_of_mem g z)

     -- rearrange
     unfold g at this
     have : ∀ x ∈ cci a b, 1 ≤ K * (U - f x) := by
      refine fun x z ↦ ?_
      specialize this x z
      rw [div_le_iff₀ ?_] at this
      · exact this
      · expose_names; exact sub_pos.mpr (this_1 x z)
     have : ∀ x ∈ cci a b, f x ≤ U - 1 / K := by
      refine fun x z ↦ ?_
      specialize this x z
      rw [mul_sub] at this
      rw [le_sub_comm] at this
      rw [← le_div_iff₀' hKpos] at this
      rw [sub_div] at this
      rw [mul_div_cancel_left₀ U (Ne.symm (ne_of_lt hKpos))] at this
      exact this

     -- U - 1 / K is an upper bound of f
     have lessUpper: (U - 1 / K) ∈ upperBounds (f '' cci a b):= by
      have : ∀ y ∈ (f '' cci a b), y ≤ (U - 1 / K) := by
       refine fun y z ↦ ?_
       rw [Set.mem_image] at z
       obtain ⟨x, ⟨hx1, hx2⟩⟩ := z
       apply this at hx1
       exact le_of_eq_of_le (id (Eq.symm hx2)) hx1
      exact this

     -- since U - 1 / K is strictly less than U we get a contradiction
     have := sub_lt_self U (one_div_pos.mpr hKpos)
     unfold IsLUB at hupper
     rw [← isLUB_le_iff hupper] at lessUpper
     rw [lt_iff_not_ge] at this
     exact this lessUpper

    obtain ⟨x, hx⟩ := this
    rw [← hx.right] at hupper
    use x
    exact ⟨hx.left, hupper⟩

    -- now the same thing but for the lower bound
  · have : ∃ x ∈ cci a b, f x = L := by
     by_contra h
     rw [not_exists] at h
     have hfneL : ∀ x ∈ cci a b, f x ≠ L := by
      refine fun x z ↦ ?_
      specialize h x
      rw [not_and] at h
      exact h z
     have : ∀ x ∈ cci a b, f x > L := by
      have Llower := Set.mem_of_mem_inter_left hlower
      unfold lowerBounds at Llower
      refine fun x z ↦ ?_
      have := Set.mem_image_of_mem f z
      exact Std.lt_of_le_of_ne (Llower this) fun a ↦ hfneL x z (id (Eq.symm a))
     let g : ℝ → ℝ := fun x => 1 / (L - f x)
     have hgneg : ∀ x ∈ cci a b, g x < 0 := by
      unfold g
      refine fun x z ↦ ?_
      simp
      exact this x z
     have hgcont : is_cont g (cci a b) := by
      refine @cont_on_quot (fun x ↦ 1) (fun x ↦ L - f x) (cci a b) ?_ ?_ ?_
      · exact fun x a ↦ sub_ne_zero_of_ne fun a_1 ↦ hfneL x a (id (Eq.symm a_1))
      · exact const_cont 1 (cci a b)
      · refine @cont_on_sum (fun x ↦ L) (fun x ↦ -f x) (cci a b) ?_ ?_
        · exact const_cont L (cci a b)
        · have : (fun x ↦ -f x) = (fun x ↦ (-1 * f x)) := by
           funext; expose_names
           exact neg_eq_neg_one_mul (f x)
          rw [this]
          exact cont_on_scalar_prod f (cci a b) (-1) cont
     have hgbounded := cont_closed_imp_bounded g a b hgcont
     have gbounds := bounded_has_LUB_and_GLB g (cci a b) nonempty
                                             hgbounded.left hgbounded.right
     obtain ⟨K, hK⟩ := gbounds.right
     have hKneg : K < 0 := by
      have Klower := Set.mem_of_mem_inter_left hK
      unfold lowerBounds at Klower
      have := non_empty_closed a b (ne_of_lt hab)
      obtain ⟨c, hc⟩ := this
      have := Set.mem_image_of_mem g hc
      apply Klower at this
      exact Std.lt_of_le_of_lt this (hgneg c hc)
     have : ∀ x ∈ cci a b, g x ≥ K := by
      have Klower := Set.mem_of_mem_inter_left hK
      unfold upperBounds at Klower
      refine fun x z ↦ ?_
      exact Klower (Set.mem_image_of_mem g z)
     unfold g at this
     have : ∀ x ∈ cci a b, 1 ≤ K * (L - f x) := by
      refine fun x z ↦ ?_
      specialize this x z
      have : L - f x < 0 := by expose_names; exact sub_neg.mpr (this_1 x z)
      expose_names; exact (le_div_iff_of_neg this).mp this_2
     have : ∀ x ∈ cci a b, f x ≥ L - 1 / K := by
      refine fun x z ↦ ?_
      specialize this x z
      rw [mul_sub] at this
      rw [le_sub_comm] at this
      rw [← div_le_iff_of_neg' hKneg] at this
      rw [sub_div] at this
      rw [mul_div_cancel_left₀ L (Ne.symm (ne_of_gt hKneg))] at this
      exact this
     have greaterLower: (L - 1 / K) ∈ lowerBounds (f '' cci a b):= by
      have : ∀ y ∈ (f '' cci a b), y ≥ (L - 1 / K) := by
       refine fun y z ↦ ?_
       rw [Set.mem_image] at z
       obtain ⟨x, ⟨hx1, hx2⟩⟩ := z
       apply this at hx1
       exact le_of_le_of_eq hx1 hx2
      exact this
     have : L < L - 1 / K := by
      refine lt_tsub_comm.mp ?_
      rw [sub_self]
      exact one_div_neg.mpr hKneg
     unfold IsGLB at hlower
     rw [← le_isGLB_iff hlower] at greaterLower
     rw [lt_iff_not_ge] at this
     exact this greaterLower
    obtain ⟨x, hx⟩ := this
    rw [← hx.right] at hlower
    use x
    exact ⟨hx.left, hlower⟩
