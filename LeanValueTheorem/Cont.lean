import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals
import LeanValueTheorem.Sequences
import LeanValueTheorem.Misc

-- Definition for a function being continuous at one point, using ε-δ
def is_cont_at_ε_δ (f : ℝ → ℝ) {I : Set ℝ} (a : I) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ x ∈ I, abs (x - a) < δ → abs (f x - f a) < ε

-- Definition for a function being continuous at one point, using sequences
def is_cont_at_seq (f : ℝ → ℝ) {I : Set ℝ} (a : I) : Prop := sorry
-- this is annoying
-- could either somehow do "all sequences"
-- or do in declaration of def "for any sequence"

-- Definition for a function being continuous at a point, using interchangability
-- of the sequential and ε-δ definitions
def is_cont_at (f : ℝ → ℝ) {I : Set ℝ} (a : I) : Prop :=
  (is_cont_at_ε_δ f a) ∧ (is_cont_at_seq f a)

-- Definition for a function being continuous on its whole domain
def is_cont_on (f : ℝ → ℝ) (I : Set ℝ) (C : Set ℝ) {hC : C ⊆ I} : Prop :=
  ∀ a : C, is_cont_at f a

-- Definition for a function being continuous on its whole domain
def is_cont (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ a : I, is_cont_at f a

-- Algebra of continuous functions (for sums, products, and quotients)
lemma cont_sum
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  is_cont_at (fun x => f x + g x) a := sorry
lemma cont_prod
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  is_cont_at (fun x => f x * g x) a := sorry
lemma cont_quot
  (I : Set ℝ)
  (f g : I → ℝ) (a : I)
  {hfIa : is_cont_at f a}
  {hgIa : is_cont_at g a} :
  is_cont_at (fun x => f x / g x) a := sorry

-- Interchangability of ε-δ definition and sequential
-- Forwards direction
lemma cont_ε_δ_imp_cont_seq
  (f : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
  {hfIa : is_cont_at_ε_δ f a} :
  is_cont_at_seq f a := sorry
-- Backwards direction
lemma cont_seq_imp_cont_ε_δ
  (I : Set ℝ)
  (f : I → ℝ)
  (a : I)
  {hfIa : is_cont_at_seq f a} :
  is_cont_at_ε_δ f a := sorry

-- Proof that continuous functions attain their bounds
lemma cont_attains_bounds
  (f : ℝ → ℝ)
  (I : Set ℝ)
  {hfI : is_cont f I} :
  (∃ a : I, is_fun_min f a) ∧
  (∃ b : I, is_fun_max f b) := sorry
