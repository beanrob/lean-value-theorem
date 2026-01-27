import Mathlib.Data.Real.Basic
import LeanValueTheorem.Cont


def upper_bound (f : ℝ → ℝ) (I : Set ℝ) (u : ℝ) : Prop :=
  ∀ x ∈ I, f x ≤ u

def least_upper_bound (f : ℝ → ℝ) (I : Set ℝ) (U : ℝ) : Prop :=
  (upper_bound f I U) ∧ (∀ u : ℝ, upper_bound f I u → U ≤ u)

def lower_bound (f : ℝ → ℝ) (I : Set ℝ) (l : ℝ) : Prop :=
  ∀ x ∈ I, l ≤ f x

def greatest_lower_bound (f : ℝ → ℝ) (I : Set ℝ) (L : ℝ) : Prop :=
  (lower_bound f I L) ∧ (∀ l : ℝ, lower_bound f I l → l ≤ L)

def is_bounded (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∃ U : ℝ, least_upper_bound f I U) ∧ (∃ L : ℝ, greatest_lower_bound f I L)

lemma lub_unique (f : ℝ → ℝ) (I : Set ℝ) (U1 U2 : ℝ)
                 (hU1 : least_upper_bound f I U1) (hU2 : least_upper_bound f I U2) :
                 U1 = U2 := by
 unfold least_upper_bound at hU1
 unfold least_upper_bound at hU2
 cases hU1; expose_names
 apply hU2.right at left
 cases hU2; expose_names
 apply right at left_1
 rw [le_antisymm_iff]
 exact ⟨left_1, left⟩

lemma glb_unique (f : ℝ → ℝ) (I : Set ℝ) (U1 U2 : ℝ)
                 (hU1 : greatest_lower_bound f I U1) (hU2 : greatest_lower_bound f I U2) :
                 U1 = U2 := by
 unfold greatest_lower_bound at hU1
 unfold greatest_lower_bound at hU2
 cases hU1; expose_names
 apply hU2.right at left
 cases hU2; expose_names
 apply right at left_1
 rw [le_antisymm_iff]
 exact ⟨left, left_1⟩

theorem cont_closed_imp_bounded (f : ℝ → ℝ) (a b : ℝ) :
 is_cont f (cci a b) → is_bounded f (cci a b) := by
 sorry

theorem cont_closed_attains_bounds (f : ℝ → ℝ) (a b : ℝ) (cont : is_cont f (cci a b)) :
 (∃ x ∈ (cci a b),    least_upper_bound f (cci a b) (f x)) ∧
 (∃ x ∈ (cci a b), greatest_lower_bound f (cci a b) (f x)) := by
 apply cont_closed_imp_bounded f a b at cont
 unfold is_bounded at cont
 and_intros
 · obtain ⟨U, hU⟩ := cont.left
   sorry
 · obtain ⟨L, hL⟩ := cont.right
   sorry
