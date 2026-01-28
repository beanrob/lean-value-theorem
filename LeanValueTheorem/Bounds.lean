import LeanValueTheorem.Sequences
import LeanValueTheorem.Cont
import Mathlib.Data.Real.Basic

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Data.Real.Archimedean

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
  (∃k : ℕ → ℕ, ∃ a : ℝ, is_lim_seq (fun n => f (k n)) a) := by sorry


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
