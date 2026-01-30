import LeanValueTheorem.Bounded_Sequences
import Mathlib.Data.Finite.Defs

noncomputable section

namespace Bolanzo

def in_left_prop (x : ℝ) (pair : ℝ × ℝ) := pair.1 ≤ x ∧ x ≤ (pair.1 + pair.2) / 2
def left_int (pair : ℝ × ℝ) : ℝ × ℝ := (pair.1, (pair.1 + pair.2) / 2)
def right_int (pair : ℝ × ℝ) : ℝ × ℝ := ((pair.1 + pair.2) / 2, pair.2)

open Classical in
def ab_pair (f : ℕ → ℝ) (L U : ℝ) : ℕ → ℝ × ℝ := fun
    | Nat.zero => ⟨L, U⟩
    | Nat.succ k =>
      if Set.Finite {(n : ℕ) | in_left_prop (f n) (ab_pair f L U k)}
      then right_int (ab_pair f L U k)
      else left_int (ab_pair f L U k)




lemma bolanzo_weierstrass (f : ℕ → ℝ) (ha : is_sequence f)
  (hfba : BddAbove (f '' Set.univ)) (hfbb : BddBelow (f '' Set.univ)) :
  ∃ k : ℕ → ℕ, (StrictMono k ∧ ∃ a : ℝ, is_lim_seq (fun n => f (k n)) a) := by

  unfold BddAbove upperBounds at hfba
  unfold BddBelow lowerBounds at hfbb

  simp at hfba hfbb
  rcases hfba with ⟨U, bounded_above⟩
  rcases hfbb with ⟨L, bounded_below⟩
  simp at bounded_above bounded_below

  have hLU (n : ℕ) : L ≤ U := le_trans (bounded_below n) (bounded_above n)

  set a : ℕ → ℝ := fun n => (ab_pair f L U n).1 with hasub
  set b : ℕ → ℝ := fun n => (ab_pair f L U n).2 with hbsub

  have rw1 (a b : ℝ) : (a, b).1 = a := by exact rfl
  have rw2 (a b : ℝ) : (a, b).2 = b := by exact rfl

  have ab_pair_0 (f : ℕ → ℝ) (L U : ℝ) : ab_pair f L U 0 = (L, U) := by
    unfold ab_pair; exact rfl
  have ha_val_0 : a 0 = L := by unfold a ab_pair; rw [rw1]
  have hb_val_0 : b 0 = U := by unfold b ab_pair; rw [rw2]



  have ha_vals (n : ℕ) : a (n+1) = a n ∨ a (n+1) = (a n + b n) / 2 := by
    unfold a b
    by_cases hfn : {n_1 | in_left_prop (f n_1) (ab_pair f L U n)}.Finite
    · right
      conv_lhs => simp [ab_pair]
      simp only [hfn, if_true, right_int]
    · left
      conv_lhs => simp [ab_pair]
      simp only [hfn, if_false, left_int]

  have hb_vals (n : ℕ) : (b (n+1) = (a n + b n) / 2) ∨ (b (n+1) = b n) := by
    unfold a b
    by_cases hfn : {n_1 | in_left_prop (f n_1) (ab_pair f L U n)}.Finite
    · right
      conv_lhs => simp [ab_pair]
      simp only [hfn, if_true, right_int]
    · left
      conv_lhs => simp [ab_pair]
      simp only [hfn, if_false, left_int]

  have h_aseq_le_bseq (n : ℕ) : a n ≤ b n := by sorry

  have a_inc1 (n : ℕ) : a n ≤ a (n+1) := by
    cases n with
    | zero =>
      rw [ha_val_0]
      unfold a ab_pair
      by_cases hfn : {n | in_left_prop (f n) (ab_pair f L U 0)}.Finite
      · simp only [hfn, if_true, right_int]
        rw [ab_pair_0, rw1, rw2]
        exact left_le_add_div_two (hLU 1)
      · simp only [hfn, if_false, left_int]
        rw [ab_pair_0, rw1]
    | succ n =>
      unfold a
      unfold a b at ha_vals
      cases ha_vals (n+1) with
      | inl ha_vals_l => rw [ha_vals_l]
      | inr ha_vals_r => rw [ha_vals_r]; exact left_le_add_div_two (h_aseq_le_bseq (n+1))


  have b_dec1 (n : ℕ) : b n ≥ b (n+1) := by
    cases n with
    | zero =>
      rw [hb_val_0]
      unfold b ab_pair
      by_cases hfn : {n | in_left_prop (f n) (ab_pair f L U 0)}.Finite
      · simp only [hfn, if_true, right_int]
        rw [ab_pair_0, rw2]
      · simp only [hfn, if_false, left_int]
        rw [ab_pair_0, rw1, rw2]
        exact add_div_two_le_right (hLU 1)
    | succ n =>
      unfold b
      unfold a b at hb_vals
      cases hb_vals (n+1) with
      | inl hb_vals_l => rw [hb_vals_l]; exact add_div_two_le_right (h_aseq_le_bseq (n+1))
      | inr hb_vals_r => rw [hb_vals_r]


  have a_inc2 (n n1 : ℕ) (hnn1 : n ≤ n1) : a n ≤ a n1 := by
    set t := n1 - n with htsub
    have hn1 : n1 = n + t := by exact Eq.symm (Nat.add_sub_of_le hnn1)
    rw [hn1]

    induction t with
    | zero => simp only [add_zero, le_refl]
    | succ k ih => exact le_trans ih (a_inc1 (n+k))

  have b_dec2 (n n1 : ℕ) (hnn1 : n ≤ n1) : b n ≥ b n1 := by
    set t := n1 - n with htsub
    have hn1 : n1 = n + t := by exact Eq.symm (Nat.add_sub_of_le hnn1)
    rw [hn1]

    induction t with
    | zero => simp only [add_zero, le_refl]
    | succ k ih => exact ge_trans ih (b_dec1 (n+k))


  have a_bounded : BddAbove (a '' Set.univ) := by
    unfold BddAbove upperBounds
    rw [@Set.nonempty_def]
    simp
    use U
    intro n
    simpa [hb_val_0] using (le_trans (h_aseq_le_bseq n) (b_dec2 0 n (Nat.zero_le n)))

  have b_bounded : BddBelow (b '' Set.univ) := by
    unfold BddBelow lowerBounds
    rw [@Set.nonempty_def]
    simp
    use L
    intro n
    simpa [ha_val_0] using (le_trans (a_inc2 0 n (Nat.zero_le n)) (h_aseq_le_bseq n))

  rcases weierstrass_criterion_inc a (by trivial) a_inc2 a_bounded with ⟨a_1, a_prop⟩
  rcases weierstrass_criterion_dec b (by trivial) b_dec2 b_bounded with ⟨b_1, b_prop⟩

  sorry



end Bolanzo
end
