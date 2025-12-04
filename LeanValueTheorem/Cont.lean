import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import LeanValueTheorem.Intervals
import LeanValueTheorem.Sequences
import LeanValueTheorem.Limits
import LeanValueTheorem.Misc

-- Definition for a function being continuous at one point, using ε-δ
def is_cont_at_ε_δ (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  a ∈ I → ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ x ∈ I, abs (x - a) < δ → abs (f x - f a) < ε

-- Definition for a function being continuous at one point, using sequences
def is_cont_at_seq (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  ∀ seq : ℕ → ℝ, is_lim_seq seq a → is_lim_seq (f ∘ seq) (f a)

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
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {hfIa : is_cont_at f I a}
  {hgIa : is_cont_at g I a} :
  (is_cont_at (fun x => f x + g x) I a) := by
    -- Define sum of functions
    let sum := fun x => f x + g x
    -- Unfold definitions so we can start working on them
    unfold is_cont_at at hfIa hgIa
    obtain ⟨_, hf⟩ := hfIa -- Only need sequential continuity
    obtain ⟨_, hg⟩ := hgIa -- so we can discard ε-δ versions
    unfold is_cont_at_seq at hf hg
    unfold is_cont_at
    -- Show sequential continuity of sum:
    have seq_cont : is_cont_at_seq sum I a := by
      unfold is_cont_at_seq
      intros seq hseq
      unfold sum
      specialize hf seq
      specialize hg seq
      have hf := hf hseq
      have hg := hg hseq
      obtain ⟨_, limit⟩ := seq_sum (f ∘ seq) (g ∘ seq) (f a) (g a) sorry sorry hf hg
      exact limit
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont


lemma cont_prod
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {hfIa : is_cont_at f I a}
  {hgIa : is_cont_at g I a} :
  is_cont_at (fun x => f x * g x) I a := by
    let prod := fun x => f x * g x
    unfold is_cont_at at hfIa hgIa
    obtain ⟨_, hf⟩ := hfIa
    obtain ⟨_, hg⟩ := hgIa
    unfold is_cont_at_seq at hf hg
    unfold is_cont_at
    have seq_cont : is_cont_at_seq prod I a := by
      unfold is_cont_at_seq
      intros seq hseq
      unfold prod
      specialize hf seq
      specialize hg seq
      have hf := hf hseq
      have hg := hg hseq
      obtain ⟨_, limit⟩ := seq_prod (f ∘ seq) (g ∘ seq) (f a) (g a) sorry sorry hf hg
      exact limit
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont


lemma cont_quot
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {hfIa : is_cont_at f I a}
  {hgIa : is_cont_at g I a} :
  is_cont_at (fun x => f x / g x) I a := by
    let quot := fun x => f x / g x
    unfold is_cont_at at hfIa hgIa
    obtain ⟨_, hf⟩ := hfIa
    obtain ⟨_, hg⟩ := hgIa
    unfold is_cont_at_seq at hf hg
    unfold is_cont_at
    have seq_cont : is_cont_at_seq quot I a := by
      unfold is_cont_at_seq
      intros seq hseq
      unfold quot
      specialize hf seq
      specialize hg seq
      have hf := hf hseq
      have hg := hg hseq
      obtain ⟨_, limit⟩ := seq_quot (f ∘ seq) (g ∘ seq) (f a) (g a) sorry sorry hf hg
      exact limit
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont


lemma reciprocal_cont
  (f : ℝ → ℝ)
  (I : Set ℝ)
  {hfI : is_cont f I} :
  is_cont (fun x => 1 / f x) I := by
    let recip := fun x : ℝ => 1 / f x
    unfold is_cont
    intros a haI
    unfold is_cont at hfI
    specialize hfI a haI
    have const_cont : is_cont_at (fun x : ℝ => (1 : ℝ)) I a := by
      unfold is_cont_at
      have e_d_cont : is_cont_at_ε_δ (fun x : ℝ => (1 : ℝ)) I a := by
        unfold is_cont_at_ε_δ
        intros haI ε hε
        use 1
        intros h1 x hxI hdiff
        simp
        exact hε
      constructor
      · exact e_d_cont
      · apply cont_ε_δ_imp_cont_seq
        exact e_d_cont
    apply cont_quot (fun x : ℝ => (1 : ℝ)) f I a
    · exact const_cont
    · exact hfI
