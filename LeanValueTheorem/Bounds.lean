import LeanValueTheorem.Sequences
import LeanValueTheorem.Cont
import Mathlib.Data.Real.Basic

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Data.Real.Archimedean

lemma sequence_in_closed (f : ℕ → ℝ) (l a b : ℝ) (hfab : ∀ n : ℕ, f n ∈ cci a b)
  (hfl : is_lim_seq f l) : (l ∈ cci a b) := by sorry

lemma supremeum_neary_attained
  (S : ℝ) (A : Set ℝ) (han : Set.Nonempty A) (hab : BddAbove A) (hS : IsLUB A S) :
  (∀ ε > 0, ∃ a ∈ A, S - ε < a ∧ a ≤ S) := by

  unfold IsLUB IsLeast upperBounds lowerBounds at hS
  rcases hS with ⟨hl, hr⟩
  simp at hl hr

  have left_proof : ∀ε > 0, ∃ a ∈ A, S - ε < a := by
    by_contra h
    simp at h
    rcases h with ⟨x, hx, hg⟩
    exact (not_le_of_gt (sub_lt_self S hx)) (hr hg)

  intro ε hε
  rcases left_proof ε hε with ⟨a, ha, left⟩
  exact ⟨a, ha, left, hl ha⟩


lemma weierstrass_criterion (f : ℕ → ℝ) (hf : is_sequence f)
  (hfi : ∀ n n1 : ℕ, n ≤ n1 → f n ≤ f n1) (hb : BddAbove (f '' Set.univ)) :
  (∃a : ℝ, is_lim_seq f a) := by

  set A := (f '' Set.univ) with hA
  have hAn : A.Nonempty := ⟨f 1, Set.mem_image_of_mem f trivial⟩
  have sup_well_defined := isLUB_csSup (s := A) hAn hb

  use sSup A
  intro ε hε
  have near_sup := supremeum_neary_attained (sSup A) A hAn hb sup_well_defined ε hε

  rcases near_sup with ⟨fN, fnI, fN_prop⟩
  rcases fnI with ⟨N, hN_univ, rfl⟩

  use N
  intro n hn

  have lemma_res := lt_of_lt_of_le (fN_prop.left) (hfi N n hn)
  have fn_mem : f n ∈ (f '' Set.univ) := by exact Set.mem_image_of_mem f hN_univ
  have fn_le_sup := le_csSup (s := A) hb fn_mem
  rw [abs_sub_comm]
  rw [abs_of_nonneg (sub_nonneg_of_le fn_le_sup)]
  exact sub_lt_comm.mp lemma_res


lemma bolanzo_weierstrass (f : ℕ → ℝ) (ha : is_sequence f)
  (hfba : BddAbove (f '' Set.univ)) (hfbb : BddBelow (f '' Set.univ)) :
  ∃ k : ℕ → ℕ, (StrictMono k ∧ ∃ a : ℝ, is_lim_seq (fun n => f (k n)) a) := by sorry


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

  rcases bolanzo_weierstrass g (by trivial) hgb hgl with ⟨k, mono, lim, hgk_lim⟩

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
