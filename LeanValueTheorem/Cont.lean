import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals
import LeanValueTheorem.Sequences

def is_cont_at_ε_δ (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (a : I) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ x : I, abs (x.val - a.val) < δ → abs (f x - f a) < ε

def is_cont_seq (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (a : I) : Prop := sorry
-- this is annoying
-- could either somehow do "all sequences"
-- or do in declaration of def "for any sequence"

def is_cont (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) (a : I) : Prop :=
  (is_cont_at_ε_δ I hI f a) ∧ (is_cont_seq I hI f a)

def is_cont_on_set (I : Set ℝ) (hI : is_interval I) (f : I → ℝ) : Prop :=
  ∀ a : I, is_cont I hI f a

lemma cont_seq_implies_cont_ε_δ
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ) (a : I)
  {hfIa : is_cont_seq I hI f a} :
  is_cont_at_ε_δ I hI f a := sorry

lemma cont_ε_δ_implies_cont_seq
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ) (a : I)
  {hfIa : is_cont_at_ε_δ I hI f a} :
  is_cont_seq I hI f a := sorry

lemma algebra_of_cont_fcts
  (I : Set ℝ) (hI : is_interval I)
  (f g : I → ℝ) (a : I)
  {hfIa : is_cont I hI f a}
  {hgIa : is_cont I hI g a} :

  (is_cont I hI (fun x => f x + g x) a) ∧
  (is_cont I hI (fun x => f x * g x) a) ∧
  (is_cont I hI (fun x => f x / g x) a) := sorry
-- ignore constants for division case
-- might be worh splitting into 3 separate lemmas


def is_fun_min (I : Set ℝ) (hI : is_interval I) (a : ℝ) : Prop := sorry
def is_fun_max (I : Set ℝ) (hI : is_interval I) (b : ℝ) : Prop := sorry

lemma attain_of_bounds_on_cont
  (I : Set ℝ) (hI : is_interval I)
  (f : I → ℝ)
  {hfI : is_cont_on_set I hI f} :
  (∃ a : I, is_fun_min I hI a) ∧
  (∃ b : I, is_fun_max I hI b) := sorry
