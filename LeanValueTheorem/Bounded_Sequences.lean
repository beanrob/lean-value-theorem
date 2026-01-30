import LeanValueTheorem.Cont
import Mathlib.Data.Real.Archimedean


lemma sequence_in_closed (f : ℕ → ℝ) (l a b : ℝ) (hfab : ∀ n : ℕ, f n ∈ cci a b)
  (hfl : is_lim_seq f l) : (l ∈ cci a b) := by

  constructor
  · by_contra! h
    set ε : ℝ :=  (min a b - l) / 2 with hε_sub
    have hε : ε > 0 := div_pos (sub_pos.mpr h) (by norm_num)

    rcases hfl ε hε with ⟨N, hf_prop⟩
    have (n : ℕ) : f n - l > 0 := sub_pos.mpr (lt_of_lt_of_le h (hfab n).left)

    have proof (n : ℕ) (hn : n ≥ N) := by
      have this2 := by simpa [abs_of_pos (this n)] using (hf_prop n hn)
      have side1 := (hfab n).left
      have side2 := by
        calc
          f n < l + ((min a b - l) / 2) := lt_add_of_tsub_lt_left this2
          _ = (min a b + l) / 2 := by ring1
          _ < min a b := by simpa [add_comm] using add_div_two_lt_right.mpr h
      exact (not_le_of_gt side2) side1
    exact proof (N+1) (by norm_num)

  · by_contra! h
    set ε : ℝ :=  (l - max a b) / 2 with hε_sub
    have hε : ε > 0 := div_pos (sub_pos.mpr h) (by norm_num)

    rcases hfl ε hε with ⟨N, hf_prop⟩
    have (n : ℕ) : l - f n > 0 := sub_pos.mpr (lt_of_le_of_lt (hfab n).right h)

    have proof (n : ℕ) (hn : n ≥ N) := by
      have this2 := by simpa [abs_sub_comm, abs_of_pos (this n)] using (hf_prop n hn)
      have side1 := (hfab n).right
      have side2 := by
        calc
          f n > l - ((l - max a b) / 2) :=  sub_lt_comm.mp this2
          _ = (l + max a b) / 2 := by ring1
          _ > max a b := by simpa [add_comm] using left_lt_add_div_two.mpr h

      exact (not_le_of_gt side2) side1
    exact proof (N+1) (by norm_num)

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

lemma infemum_nearly_attained
  (I : ℝ) (A : Set ℝ) (han : Set.Nonempty A) (hab : BddBelow A) (hS : IsGLB A I) :
  (∀ ε > 0, ∃ a ∈ A, I ≤ a ∧ a < I + ε) := by

  unfold IsGLB IsGreatest upperBounds lowerBounds at hS
  rcases hS with ⟨hl, hr⟩
  simp at hl hr

  have left_proof : ∀ε > 0, ∃ a ∈ A,  a < I + ε := by
    by_contra h
    simp at h
    rcases h with ⟨x, hx, hg⟩
    exact (not_le_of_gt (lt_add_of_pos_right I hx)) (hr hg)

  intro ε hε
  rcases left_proof ε hε with ⟨a, ha, left⟩
  exact ⟨a, ha, hl ha, left⟩



lemma weierstrass_criterion_inc (f : ℕ → ℝ) (hf : is_sequence f)
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

lemma weierstrass_criterion_dec (f : ℕ → ℝ) (hf : is_sequence f)
  (hfi : ∀ n n1 : ℕ, n ≤ n1 → f n ≥ f n1) (hb : BddBelow (f '' Set.univ)) :
  (∃a : ℝ, is_lim_seq f a) := by

  set A := (f '' Set.univ) with hA
  have hAn : A.Nonempty := ⟨f 1, Set.mem_image_of_mem f trivial⟩
  have inf_well_defined := isGLB_csInf (s := A) hAn hb

  use sInf A
  intro ε hε
  have near_inf := infemum_nearly_attained (sInf A) A hAn hb inf_well_defined ε hε

  rcases near_inf with ⟨fN, fnI, fN_prop⟩
  rcases fnI with ⟨N, hN_univ, rfl⟩

  use N
  intro n hn

  have lemma_res := lt_of_le_of_lt (hfi N n hn) (fN_prop.right)
  have fn_mem : f n ∈ (f '' Set.univ) := by exact Set.mem_image_of_mem f hN_univ
  have inf_le_fn := csInf_le (s := A) hb fn_mem
  rw [abs_of_nonneg (sub_nonneg_of_le inf_le_fn)]
  exact sub_left_lt_of_lt_add lemma_res
