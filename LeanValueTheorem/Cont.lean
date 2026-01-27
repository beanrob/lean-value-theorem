import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import LeanValueTheorem.Intervals
import LeanValueTheorem.Sequences
import LeanValueTheorem.Limits
import LeanValueTheorem.Misc

-- Definition for a function being continuous at one point, using ε-δ
def is_cont_at_ε_δ (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  a ∈ I → ∀ ε : ℝ, ε > 0 → ∃ δ > 0, ∀ x ∈ I, abs (x - a) < δ → abs (f x - f a) < ε

-- Definition for a function being continuous at one point, using sequences
def is_cont_at_seq (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ) : Prop :=
  -- Old version:
  -- ∀ seq : ℕ → ℝ, is_lim_seq seq a → is_lim_seq (f ∘ seq) (f a)
  -- May need to be changed to:
  a ∈ I → ∀ seq : ℕ → ℝ, (∀ n : ℕ, seq n ∈ I) → is_lim_seq seq a → is_lim_seq (f ∘ seq) (f a)

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
  is_cont_at_seq f I a := by
    unfold is_cont_at_ε_δ at hfIa
    unfold is_cont_at_seq
    intros haI seq hseqI hseq
    unfold is_lim_seq
    intros ε hε
    unfold is_lim_seq at hseq
    specialize hfIa haI ε hε
    obtain ⟨δf, hδf, hfIa⟩ := hfIa
    specialize hseq δf hδf
    obtain ⟨Nseq, hseq⟩ := hseq
    use Nseq
    intros n hn
    specialize hseq n hn
    specialize hfIa (seq n)
    specialize hseqI n
    specialize hfIa hseqI
    specialize hfIa hseq
    simp only [Function.comp_apply]
    exact hfIa

-- Backwards direction
lemma cont_seq_imp_cont_ε_δ
  (f : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {hfIa : is_cont_at_seq f I a} :
  is_cont_at_ε_δ f I a := by
    unfold is_cont_at_ε_δ
    unfold is_cont_at_seq at hfIa
    intros haI ε hε
    specialize hfIa haI
    use ε
    constructor
    · exact hε
    ·
      simp at h
      intros x hxI hxaε
      let seq : ℕ → ℝ := fun n => x + (1/n)
      have hseqI : ∀ n : ℕ, seq n ∈ I := by
        intro n
        sorry
      have limseq : is_lim_seq seq a := by
        unfold is_lim_seq
        intros ε1 hε1
        sorry
      specialize hfIa seq hseqI limseq
      -- ...
      unfold is_lim_seq at limseq
      specialize limseq ε hε
      obtain ⟨N1, limseq⟩ := limseq
      -- ...
      unfold is_lim_seq at hfIa
      specialize hfIa ε hε
      obtain ⟨N2, hfIa⟩ := hfIa
      -- ...
      specialize limseq (N1 + N2)
      specialize hfIa   (N1 + N2)
      have sum1 : N1 + N2 ≥ N1 := by aesop
      have sum2 : N1 + N2 ≥ N2 := by aesop
      specialize limseq sum1
      specialize hfIa   sum2
      sorry

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
      intros ha seq hseqI hseq
      -- intros seq hseq
      unfold sum
      specialize hf ha seq
      specialize hg ha seq
      have hf := hf hseqI hseq
      have hg := hg hseqI hseq
      obtain ⟨_, limit⟩ :=
        seq_sum (f ∘ seq) (g ∘ seq) (f a) (g a) (by trivial) (by trivial) hf hg
      exact limit
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont

lemma cont_on_sum
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  {hfIa : is_cont f I}
  {hgIa : is_cont g I} :
  (is_cont (fun x => f x + g x) I) := by
   unfold is_cont
   apply fun a a_1 ↦ cont_sum f g I a
   · exact fun a a_1 ↦ hfIa a a_1
   · exact fun a a_1 ↦ hgIa a a_1

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
      intros ha seq hseqI hseq
      unfold prod
      specialize hf ha seq
      specialize hg ha seq
      have hf := hf hseqI hseq
      have hg := hg hseqI hseq
      obtain ⟨_, limit⟩ :=
        seq_prod (f ∘ seq) (g ∘ seq) (f a) (g a) (by trivial) (by trivial) hf hg
      exact limit
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont

lemma cont_on_prod
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  {hfIa : is_cont f I}
  {hgIa : is_cont g I} :
  is_cont (fun x => f x * g x) I := by
   unfold is_cont
   apply fun a a_1 ↦ cont_prod f g I a
   · exact fun a a_1 ↦ hfIa a a_1
   · exact fun a a_1 ↦ hgIa a a_1

lemma cont_quot
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : ℝ)
  {ha : a ∈ I}
  {hg0 : ∀ x ∈ I, g x ≠ 0}
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
      intros ha seq hseqI hseq
      unfold quot
      specialize hf ha seq
      specialize hg ha seq
      have hf := hf hseqI hseq
      have hg := hg hseqI hseq
      specialize hg0 a ha
      obtain ⟨_, limit⟩ :=
        seq_quot (f ∘ seq) (g ∘ seq) (f a) (g a) (by trivial) (by trivial) hf hg hg0
      exact limit
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont

lemma cont_on_quot
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  {hg0 : ∀ x ∈ I, g x ≠ 0}
  {hfIa : is_cont f I}
  {hgIa : is_cont g I} :
  is_cont (fun x => f x / g x) I := by
   unfold is_cont
   apply fun a a_1 ↦ cont_quot f g I a
   · intros a ha
     exact ha
   · intros a ha
     exact hg0
   · exact fun a a_1 ↦ hfIa a a_1
   · exact fun a a_1 ↦ hgIa a a_1

lemma reciprocal_cont
  (f : ℝ → ℝ)
  (I : Set ℝ)
  {hfI : is_cont f I}
  {hf0 : ∀ x ∈ I, f x ≠ 0} :
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
        simp only [gt_iff_lt, zero_lt_one, sub_self, abs_zero, true_and]
        intros x hxI hdiff
        exact hε
      constructor
      · exact e_d_cont
      · apply cont_ε_δ_imp_cont_seq
        exact e_d_cont
    apply cont_quot (fun x : ℝ => (1 : ℝ)) f I a
    · exact haI
    · exact hf0
    · exact const_cont
    · exact hfI

lemma id_cont
  (I : Set ℝ) :
  is_cont (fun x => x) I := by
    let id := fun x : ℝ => x
    unfold is_cont
    intros a haI
    unfold is_cont_at
    have seq_cont : is_cont_at_seq id I a := by
      unfold is_cont_at_seq
      aesop
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont

lemma const_cont
  (c : ℝ)
  (I : Set ℝ) :
  is_cont (fun x => c) I := by
    let const := fun x : ℝ => c
    unfold is_cont
    intros a haI
    unfold is_cont_at
    have seq_cont : is_cont_at_seq const I a := by
      unfold is_cont_at_seq
      intros seq hseq
      unfold is_lim_seq const
      intros ha seq hseqI hseq
      use 1
      aesop
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont
