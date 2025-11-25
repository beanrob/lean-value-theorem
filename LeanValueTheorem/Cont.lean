import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals
import LeanValueTheorem.Sequences
import LeanValueTheorem.Limits
import LeanValueTheorem.Misc

-- Definition for a function being continuous at one point, using ε-δ
def is_cont_at_ε_δ (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  a ∈ I → ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ x ∈ I, abs (x - a) < δ → abs (f x - f a) < ε

-- Definition for a function being continuous at one point, using sequences
def is_cont_at_seq {I : Set ℝ} (f : I → ℝ) (a : I) : Prop :=
  ∀ seq : ℕ → I, is_lim_seq_rest seq a → is_lim_seq (f ∘ seq) (f a)

-- Definition for a function being continuous at a point, using interchangability
-- of the sequential and ε-δ definitions
def is_cont_at (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  (is_cont_at_ε_δ f I a) ∧ (is_cont_at_seq f I a)

-- Definition for a function being continuous on its whole domain
def is_cont_on (f : ℝ → ℝ) (I : Set ℝ) (C : Set ℝ) {hC : C ⊆ I} : Prop :=
  ∀ a ∈ C, is_cont_at f I a

-- Definition for a function being continuous on its whole domain
def is_cont (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ a ∈ I, is_cont_at f I a
  
-- Interchangability of ε-δ definition and sequential
-- Forwards direction
lemma cont_ε_δ_imp_cont_seq
  (f : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {hfIa : is_cont_at_ε_δ f I a} :
  is_cont_at_seq f I a := sorry
-- Backwards direction
lemma cont_seq_imp_cont_ε_δ
  (f : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {hfIa : is_cont_at_seq f I a} :
  is_cont_at_ε_δ f I a := sorry

-- Algebra of continuous functions (for sums, products, and quotients)
lemma cont_sum
  (I : Set ℝ) (hI : is_interval I)
  (f g : I → ℝ) (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  (is_cont_at (fun x => f x + g x) a) := by
    unfold is_cont_at at hfIa hgIa
    obtain ⟨hf1, hf2⟩ := hfIa
    obtain ⟨hg1, hg2⟩ := hgIa
    unfold is_cont_at_seq at hf2 hg2
    unfold is_cont_at
    have seq_cont : is_cont_at_seq (fun x => f x + g x) a := by
      sorry
    sorry
  -- Need to know how to unfold assumptions and give things names
lemma cont_prod
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
  {hfIa : is_cont_at f I a}
  {hgIa : is_cont_at g I a} :
  is_cont_at (fun x => f x * g x) I a := sorry
lemma cont_quot
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
  {hfIa : is_cont_at f I a}
  {hgIa : is_cont_at g I a} :
  is_cont_at (fun x => f x / g x) I a := sorry

-- Proof that continuous functions attain their bounds
lemma cont_attains_bounds
  (f : ℝ → ℝ)
  (I : Set ℝ)
  {hfI : is_cont f I} :
  (∃ a ∈ I, is_fun_min f I a) ∧
  (∃ b ∈ I, is_fun_max f I b) := sorry
