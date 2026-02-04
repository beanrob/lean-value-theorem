import LeanValueTheorem.Bounded_Sequences
import LeanValueTheorem.Misc
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

noncomputable section

namespace Bolzano

lemma rw1 (a b : ℝ) : (a, b).1 = a := by simp only
lemma rw2 (a b : ℝ) : (a, b).2 = b := by simp only

def in_left_prop (x : ℝ) (pair : ℝ × ℝ) := pair.1 ≤ x ∧ x ≤ (pair.1 + pair.2) / 2
def in_right_prop (x : ℝ) (pair : ℝ × ℝ) := (pair.1 + pair.2) / 2 ≤ x ∧ x ≤ pair.2

lemma split_prop (x : ℝ) (pair : ℝ × ℝ) (hxp : pair.1 ≤ x ∧ x ≤ pair.2) :
  (in_left_prop x pair) ∨ (in_right_prop x pair) := by
  unfold in_left_prop in_right_prop
  by_cases hx : x ≤ (pair.1 + pair.2) / 2
  · left
    exact ⟨hxp.1, hx⟩
  · right
    rw [not_le] at hx
    exact ⟨le_of_lt hx, hxp.2⟩

def left_int (pair : ℝ × ℝ) : ℝ × ℝ := (pair.1, (pair.1 + pair.2) / 2)
def right_int (pair : ℝ × ℝ) : ℝ × ℝ := ((pair.1 + pair.2) / 2, pair.2)

open Classical in
def ab_pair (f : ℕ → ℝ) (L U : ℝ) : ℕ → ℝ × ℝ := fun
    | Nat.zero => ⟨L, U⟩
    | Nat.succ k =>
      if Set.Finite {(n : ℕ) | in_left_prop (f n) (ab_pair f L U k)}
      then right_int (ab_pair f L U k)
      else left_int (ab_pair f L U k)

def a (f : ℕ → ℝ) (L U : ℝ) : ℕ → ℝ := fun n => (ab_pair f L U n).1
def b (f : ℕ → ℝ) (L U : ℝ) : ℕ → ℝ := fun n => (ab_pair f L U n).2

lemma ab_pair_0 (f : ℕ → ℝ) (L U : ℝ) : ab_pair f L U 0 = (L, U) := by
    unfold ab_pair; exact rfl

lemma ha_val_0 (f : ℕ → ℝ) (L U : ℝ) : a f L U 0 = L := by
  unfold a
  rw [ab_pair_0]

lemma hb_val_0 (f : ℕ → ℝ) (L U : ℝ) : b f L U 0 = U := by
  unfold b
  rw [ab_pair_0]

lemma ha_vals (f : ℕ → ℝ) (L U : ℝ) (n : ℕ) :
  a f L U (n+1) = a f L U n ∨
  a f L U (n+1) = ((a f L U n) + (b f L U n)) / 2 := by

    unfold a b
    by_cases hfn : {n_1 | in_left_prop (f n_1) (ab_pair f L U n)}.Finite
    · right
      conv_lhs => simp [ab_pair]
      simp only [hfn, if_true, right_int]
    · left
      conv_lhs => simp [ab_pair]
      simp only [hfn, if_false, left_int]


lemma hb_vals (f : ℕ → ℝ) (L U : ℝ) (n : ℕ) :
  b f L U (n+1) = ((a f L U n) + (b f L U n)) / 2 ∨
  b f L U (n+1) = (b f L U n) := by

  unfold a b
  by_cases hfn : {n_1 | in_left_prop (f n_1) (ab_pair f L U n)}.Finite
  · right
    conv_lhs => simp [ab_pair]
    simp only [hfn, if_true, right_int]
  · left
    conv_lhs => simp [ab_pair]
    simp only [hfn, if_false, left_int]

lemma h_aseq_le_bseq (f : ℕ → ℝ) (L U : ℝ) (hLU : L ≤ U) (n : ℕ) :
  a f L U n ≤ b f L U n := by

  induction n with
  | zero => rw [ha_val_0, hb_val_0]; exact hLU
  | succ k ih =>
    unfold a b
    unfold a b at ih
    have aval := (by simpa [a, b] using ha_vals f L U k)
    have bval := (by simpa [a, b] using hb_vals f L U k)
    cases aval with
    | inl avall =>
      cases bval with
      | inl bvall => rw [avall, bvall]; exact left_le_add_div_two ih
      | inr bvalr => rw [avall, bvalr]; exact ih
    | inr avalr =>
      cases bval with
      | inl bvall => rw [avalr, bvall]
      | inr bvalr => rw [avalr, bvalr]; exact add_div_two_le_right ih

lemma a_inc1 (f : ℕ → ℝ) (L U : ℝ) (n : ℕ) (hLU : L ≤ U) : a f L U n ≤ a f L U (n+1) := by
    cases n with
    | zero =>
      rw [ha_val_0]
      unfold a ab_pair
      by_cases hfn : {n | in_left_prop (f n) (ab_pair f L U 0)}.Finite
      · simp only [hfn, if_true, right_int]
        rw [ab_pair_0]
        exact left_le_add_div_two hLU
      · simp only [hfn, if_false, left_int]
        rw [ab_pair_0, rw1]
    | succ n =>
      unfold a
      have := (by simpa [a, b] using ha_vals f L U (n+1))
      cases this with
      | inl ha_vals_l => rw [ha_vals_l]
      | inr ha_vals_r =>
        rw [ha_vals_r]
        exact left_le_add_div_two (h_aseq_le_bseq f L U hLU (n+1))

lemma b_dec1 (f : ℕ → ℝ) (L U : ℝ) (n : ℕ) (hLU : L ≤ U) : b f L U n ≥ b f L U (n+1) := by
  cases n with
  | zero =>
    rw [hb_val_0]
    unfold b ab_pair
    by_cases hfn : {n | in_left_prop (f n) (ab_pair f L U 0)}.Finite
    · simp only [hfn, if_true, right_int]
      rw [ab_pair_0, rw2]
    · simp only [hfn, if_false, left_int]
      rw [ab_pair_0, rw1, rw2]
      exact add_div_two_le_right hLU
  | succ n =>
    unfold b
    have := (by simpa [a, b] using hb_vals f L U (n+1))
    cases this with
    | inl hb_vals_l =>
      rw [hb_vals_l]
      exact add_div_two_le_right (h_aseq_le_bseq f L U hLU (n+1))
    | inr hb_vals_r => rw [hb_vals_r]

lemma a_inc2 (f : ℕ → ℝ) (L U : ℝ) (hLU : L ≤ U) (n n1 : ℕ) (hnn1 : n ≤ n1) :
  a f L U n ≤ a f L U n1 := by
  set t := n1 - n with htsub
  have hn1 : n1 = n + t := by exact Eq.symm (Nat.add_sub_of_le hnn1)
  rw [hn1]

  induction t with
  | zero => simp only [add_zero, le_refl]
  | succ k ih => exact le_trans ih (a_inc1 f L U (n+k) hLU)


lemma b_dec2 (f : ℕ → ℝ) (L U : ℝ) (hLU : L ≤ U) (n n1 : ℕ) (hnn1 : n ≤ n1) :
  b f L U n ≥ b f L U n1 := by

  set t := n1 - n with htsub
  have hn1 : n1 = n + t := by exact Eq.symm (Nat.add_sub_of_le hnn1)
  rw [hn1]

  induction t with
  | zero => simp only [add_zero, le_refl]
  | succ k ih => exact ge_trans ih (b_dec1 f L U (n+k) hLU)

lemma a_bounded_abv (f : ℕ → ℝ) (L U : ℝ) (hLU : L ≤ U) :
  BddAbove (a f L U '' Set.univ) := by

  unfold BddAbove upperBounds
  rw [@Set.nonempty_def]
  simp
  use U
  intro n
  have := le_trans (h_aseq_le_bseq f L U hLU n) (b_dec2 f L U hLU 0 n (Nat.zero_le n) )
  simpa [hb_val_0] using this

lemma b_bounded_bel (f : ℕ → ℝ) (L U : ℝ) (hLU : L ≤ U) :
  BddBelow (b f L U '' Set.univ) := by

  unfold BddBelow lowerBounds
  rw [@Set.nonempty_def]
  simp
  use L
  intro n
  have := le_trans (a_inc2 f L U hLU 0 n (Nat.zero_le n)) (h_aseq_le_bseq f L U hLU n)
  simpa [ha_val_0] using this

lemma inf_seq_point_ab (f : ℕ → ℝ) (L U : ℝ) (hfLU : ∀ n : ℕ, L ≤ f n ∧ f n ≤ U) :
  ∀p : ℕ, ¬{n | (a f L U p) ≤ f n ∧ f n ≤ (b f L U p)}.Finite := by

  intro p
  induction p with
  | zero =>
    rw [ha_val_0, hb_val_0]
    simp only [hfLU, and_self, Set.setOf_true]
    exact Set.infinite_univ

  | succ p_1 ih =>
    unfold a b ab_pair
    set pair := (ab_pair f L U p_1) with pair_sub
    unfold a b at ih
    rw [←pair_sub] at ih

    by_cases hfn : Set.Finite {(n : ℕ) | in_left_prop (f n) pair}
    · intro hcontra
      simp [hfn, right_int] at hcontra
      simp [in_left_prop] at hfn

      have split_set : {n | pair.1 ≤ f n ∧ f n ≤ pair.2} ⊆
        {n | pair.1 ≤ f n ∧ f n ≤ (pair.1 + pair.2) / 2} ∪
        {n | (pair.1 + pair.2) / 2 ≤ f n ∧ f n ≤ pair.2} := by
        intro n hn
        rw [Set.mem_setOf_eq] at hn
        have split_pair :=  split_prop (f n) pair hn
        exact split_pair.elim (fun l => Or.inl l) (fun r => Or.inr r)

      have hUnionFin := hfn.union hcontra
      exact ih (hUnionFin.subset split_set)

    · simp [hfn, left_int]
      exact hfn

lemma diff_a_b (f : ℕ → ℝ) (L U : ℝ) (k : ℕ) :
  (b f L U (k+1)) - (a f L U (k+1)) = ((b f L U k) - (a f L U k)) / 2 := by

  unfold a b
  conv_lhs => unfold ab_pair
  by_cases hn : {n | in_left_prop (f n) (ab_pair f L U k)}.Finite
  · simp [hn]
    unfold right_int
    rw [rw2, rw1]
    have (a b : ℝ) :  b - ((a + b) / 2) = (b - a) / 2 := by ring
    rw [this]
  · simp [hn]
    unfold left_int
    rw [rw1, rw2]
    have (a b : ℝ) :  ((a + b) / 2) - a = (b - a) / 2 := by ring
    rw [this]

lemma diff2_a_b (f : ℕ → ℝ) (L U : ℝ) (k : ℕ) :
  (b f L U (k+1)) - (a f L U (k+1)) = (U - L) / (2 ^ (k + 1)) := by

  induction k with
  | zero =>
    simp
    have := diff_a_b f L U 0
    rw [ha_val_0, hb_val_0] at this
    exact this

  | succ kk ih =>
    have step := diff_a_b f L U (kk+1)
    have : ((U - L) / 2 ^ (kk + 1) / 2) = (U - L) / 2 ^ (kk + 1 + 1) := by ring
    rw [ih, this] at step
    exact step


-- lemma lim_b_sub_a (f : ℕ → ℝ) (L U : ℝ) :
--   is_lim_seq (fun n => (b f L U n) - (a f L U n)) 0 := by

--   unfold is_lim_seq
--   intro ε hε
--   rcases exists_nat_gt ((U - L) / ε) with ⟨N, hN⟩
--   use N
--   intro n hn
--   unfold a_seq b_seq
--   simp
--   have boun : b f L U n - a f L U n ≤ (U - L) / (2 ^ n) := by
--     cases n with
--     | zero => simp [ha_val_0, hb_val_0]
--     | succ kn => exact le_of_eq (diff2_a_b f L U (kn))

--   rw [abs_of_nonneg]
--   have : (U - L) / 2 ^ n < ε := by




theorem Bolzano_weierstrass (f : ℕ → ℝ) (ha : is_sequence f)
  (hfba : BddAbove (f '' Set.univ)) (hfbb : BddBelow (f '' Set.univ)) :
  ∃ k : ℕ → ℕ, (StrictMono k ∧ ∃ a : ℝ, is_lim_seq (fun n => f (k n)) a) := by

  unfold BddAbove upperBounds at hfba
  unfold BddBelow lowerBounds at hfbb

  simp at hfba hfbb
  rcases hfba with ⟨U, bounded_above⟩
  rcases hfbb with ⟨L, bounded_below⟩
  simp at bounded_above bounded_below

  have hLU (n : ℕ) : L ≤ U := le_trans (bounded_below n) (bounded_above n)
  set a_seq := a f L U with a_sub
  set b_seq := b f L U with b_sub
  have a_inc := a_inc2 f L U (hLU 1)
  have b_dec := b_dec2 f L U (hLU 1)
  have a_boun := a_bounded_abv f L U (hLU 1)
  have b_boun := b_bounded_bel f L U (hLU 1)

  rw [←a_sub] at a_inc a_boun
  rw [←b_sub] at b_dec b_boun

  rcases weierstrass_criterion_inc a_seq (by trivial) a_inc a_boun with ⟨a_1, a_prop⟩
  rcases weierstrass_criterion_dec b_seq (by trivial) b_dec b_boun with ⟨b_1, b_prop⟩

  have hfLU (n : ℕ) : L ≤ f n ∧ f n ≤ U := ⟨bounded_below n, bounded_above n⟩

  have hk_exis (last_k p : ℕ) : ∃n : ℕ, a_seq p ≤ f n ∧ f n ≤ b_seq p ∧ last_k < n := by
      have hinf := inf_seq_point_ab f L U hfLU p
      rw [←a_sub, ←b_sub] at hinf
      by_contra h

      have hbound :
        ∀ n : ℕ, (a_seq p ≤ f n ∧ f n ≤ b_seq p) → n ≤ last_k := by
        intro n hn
        by_contra ha
        exact h ⟨n, hn.1, hn.2, Nat.gt_of_not_le ha⟩

      have hSub :
        {n : ℕ | a_seq p ≤ f n ∧ f n ≤ b_seq p} ⊆
        {n : ℕ | n ≤ last_k} := by
        intro n hn
        exact hbound n hn

      have hSubFin : Set.Finite {n : ℕ | a_seq p ≤ f n ∧ f n ≤ b_seq p} := by
        exact Set.Finite.subset (Set.finite_le_nat last_k) hbound

      exact hinf hSubFin

  set good_k_n := fun (k_p p : ℕ) => Classical.choose (hk_exis k_p p) with valsub
  have prop_big_n (k_p p : ℕ) := Classical.choose_spec (hk_exis k_p p)

  have prop_big_n2 (k_p p : ℕ) :
    a_seq p ≤ f (good_k_n k_p p) ∧
    f (good_k_n k_p p) ≤ b_seq p ∧
    k_p < (good_k_n k_p p) := by
    exact prop_big_n k_p p


  set k : ℕ → ℕ := fun n =>
    Nat.rec (motive := fun _ => ℕ) 1 (fun n kn => (good_k_n kn (n+1))) n
    with ksub

  have k_zero : k 0 = 1 := by rw [ksub]; simp
  have k_succ (n : ℕ) : k (n+1) = good_k_n (k n) (n + 1) := by rw [ksub]
  use k

  have k_inc (n : ℕ) : k n < k (n+1) := by
    rw [k_succ n]
    exact (prop_big_n2 (k n) (n+1)).2.2

  constructor
  · unfold StrictMono
    intro a b hab
    rcases Nat.exists_eq_add_of_lt hab with ⟨t', rfl⟩
    induction t' with
    | zero => simp; exact k_inc a
    | succ kt ih =>
      exact lt_trans (by simpa [Nat.add_assoc] using ih) (k_inc (a + (kt+1)))

  · use a_1
    have hfkn_boun : ∀ n : ℕ, a_seq n ≤ f (k n) ∧ f (k n) ≤ b_seq n := by
      intro n
      induction n with
      | zero =>
        unfold a_seq b_seq
        rw [ha_val_0, hb_val_0, k_zero]
        exact hfLU 1
      | succ kn ih =>
        rw [k_succ kn]
        constructor
        · exact (prop_big_n2 (k kn) (kn + 1)).1
        · exact (prop_big_n2 (k kn) (kn + 1)).2.1


    have hlim_eq : a_1 = b_1 := sorry

    have final := sandwich
      a_seq (fun n => f (k n)) b_seq a_1 b_1 (by trivial) (by trivial)
      (by trivial) a_prop b_prop hfkn_boun hlim_eq

    exact final

end Bolzano
end
