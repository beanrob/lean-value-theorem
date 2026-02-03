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
def is_cont_on (f : ℝ → ℝ) (I : Set ℝ) (C : Set ℝ) : Prop :=
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
  {is_seq : is_cont_at_seq f I a} :
  is_cont_at_ε_δ f I a := by
    -- We wish to prove by contradiction
    by_contra not_ε_δ
    -- Unfold the definition and simplify
    unfold is_cont_at_ε_δ at not_ε_δ
    simp at not_ε_δ
    -- Procure the value of ε from definition
    obtain ⟨ha, ε, hε, not_ε_δ⟩ := not_ε_δ
    -- Insert a magical δ value then simplify
    specialize not_ε_δ 1 -- !!! TEMPORARY
    simp at not_ε_δ
    -- Now procure the x for which f is discontinuous
    obtain ⟨x, hxI, dx, dfx⟩ := not_ε_δ

    -- We now wish to extract the magical sequence
    unfold is_cont_at_seq at is_seq
    specialize is_seq ha
    -- We now construct some magical sequence somehow?
    -- The magical sequence MUST:
      -- Have all its outputs be members of I
      -- Have limit a
      -- Have a magical value past its convergence point where it takes value x
    let seq : ℕ → ℝ := fun n => a + 1/(n+1) -- fun n => x --
    -- Prove condition 1
    have in_I : ∀ n : ℕ, seq n ∈ I := by
      intro n
      unfold seq
      sorry
    -- Prove condition 2
    have h_seq_ε : is_lim_seq seq a := by
      unfold is_lim_seq
      intros ε hε
      sorry
    -- Now that we have the magical sequence, we insert it into the hypothesis
    -- regarding sequential continuity
    specialize is_seq seq in_I h_seq_ε
    unfold is_lim_seq at is_seq
    -- Insert the value of ε procured from the contraposed goal
    specialize is_seq ε hε
    -- Now we extract the convergence point of the sequence
    obtain ⟨Nf, is_seq⟩ := is_seq
    specialize is_seq Nf
    simp at is_seq
    unfold seq at is_seq
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

lemma cont_scalar_prod
  (f : ℝ → ℝ)
  (I : Set ℝ)
  (a m : ℝ)
  (hfIa : is_cont_at f I a) :
  is_cont_at (fun x => m * f x) I a := by
  rcases hfIa with ⟨_, hf⟩
  unfold is_cont_at_seq at hf
  have seq_scalar_prod : is_cont_at_seq (fun n => m * f n) I a := by
    intros ha seq hseqI hseq
    exact (seq_scalar_prod (f ∘ seq) (f a) m (by trivial) (hf ha seq hseqI hseq)).2
  constructor
  · apply cont_seq_imp_cont_ε_δ
    exact seq_scalar_prod
  · exact seq_scalar_prod

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
