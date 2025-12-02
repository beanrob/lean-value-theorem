import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
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
    let sum := fun x => f x + g x
    unfold is_cont_at at hfIa hgIa
    obtain ⟨_, hf⟩ := hfIa
    obtain ⟨_, hg⟩ := hgIa
    unfold is_cont_at_seq at hf hg
    unfold is_cont_at
    have seq_cont : is_cont_at_seq sum I a := by
      unfold is_cont_at_seq
      intros seq hseq
      unfold is_lim_seq
      unfold is_lim_seq at hseq
      intros ε hε
      unfold is_lim_seq at hf hg
      have hε4 : (ε/4) > 0 := by linarith
      have h2ε4ltε : 2 * (ε/4) < ε := by linarith
      -- Extract N from continuity of f
      specialize hf seq
      let hf := hf hseq
      specialize hf (ε/4) hε4
      obtain ⟨Nf, hNf, hf⟩ := hf
      -- Extract N from continuity of g
      specialize hg seq
      let hg := hg hseq
      specialize hg (ε/4) hε4
      obtain ⟨Ng, hNg, hg⟩ := hg
      -- Solve
      use Nf + Ng
      unfold sum
      simp
      constructor
      · exact Or.inr hNg
      · intros n hn
        have hnf : n ≥ Nf := by exact Nat.le_of_add_right_le hn
        have hng : n ≥ Ng := by exact Nat.le_of_add_left_le  hn
        specialize hf n hnf
        specialize hg n hng
        simp at hf hg
        have hfg   := le_of_lt (add_lt_add hf hg)
        rw [←two_mul] at hfg
        have tri   := triangle (f (seq n) - f a) (g (seq n) - g a)
        have combi := le_trans tri hfg
        have bound : |f (seq n) - f a + (g (seq n) - g a)| < ε := lt_of_le_of_lt combi h2ε4ltε
        simp [sub_eq_add_neg, add_assoc, add_left_comm] at bound
        ring_nf
        rw [add_assoc]
        exact bound
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont


lemma cont_prod
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
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
      unfold is_lim_seq
      unfold is_lim_seq at hseq
      intros ε hε
      unfold is_lim_seq at hf hg
      have hε4 : (ε/4) > 0 := by linarith
      have h2ε4ltε : 2 * (ε/4) < ε := by linarith
      -- Extract N from continuity of f
      specialize hf seq
      let hf := hf hseq
      specialize hf (ε/4) hε4
      obtain ⟨Nf, hNf, hf⟩ := hf
      -- Extract N from continuity of g
      specialize hg seq
      let hg := hg hseq
      specialize hg (ε/4) hε4
      obtain ⟨Ng, hNg, hg⟩ := hg
      -- Solve
      use Nf + Ng
      unfold prod
      simp
      constructor
      · exact Or.inr hNg
      · intros n hn
        have hnf : n ≥ Nf := by exact Nat.le_of_add_right_le hn
        have hng : n ≥ Ng := by exact Nat.le_of_add_left_le  hn
        specialize hf n hnf
        specialize hg n hng
        simp at hf hg
        -- have hfg   := le_of_lt (add_lt_add hf hg)
        -- rw [←two_mul] at hfg
        -- have tri   := triangle (f (seq n) - f a) (g (seq n) - g a)
        -- have combi := le_trans tri hfg
        -- have bound : |f (seq n) - f a + (g (seq n) - g a)| < ε := lt_of_le_of_lt combi h2ε4ltε
        -- simp [sub_eq_add_neg, add_assoc, add_left_comm] at bound
        -- ring_nf
        -- rw [add_assoc]
        -- exact bound
        sorry
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont


lemma cont_quot
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (a : I)
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
      unfold is_lim_seq
      unfold is_lim_seq at hseq
      intros ε hε
      unfold is_lim_seq at hf hg
      have hε4 : (ε/4) > 0 := by linarith
      have h2ε4ltε : 2 * (ε/4) < ε := by linarith
      -- Extract N from continuity of f
      specialize hf seq
      let hf := hf hseq
      specialize hf (ε/4) hε4
      obtain ⟨Nf, hNf, hf⟩ := hf
      -- Extract N from continuity of g
      specialize hg seq
      let hg := hg hseq
      specialize hg (ε/4) hε4
      obtain ⟨Ng, hNg, hg⟩ := hg
      -- Solve
      use Nf + Ng
      unfold quot
      simp
      constructor
      · exact Or.inr hNg
      · intros n hn
        have hnf : n ≥ Nf := by exact Nat.le_of_add_right_le hn
        have hng : n ≥ Ng := by exact Nat.le_of_add_left_le  hn
        specialize hf n hnf
        specialize hg n hng
        simp at hf hg
        -- have hfg   := le_of_lt (add_lt_add hf hg)
        -- rw [←two_mul] at hfg
        -- have tri   := triangle (f (seq n) - f a) (g (seq n) - g a)
        -- have combi := le_trans tri hfg
        -- have bound : |f (seq n) - f a + (g (seq n) - g a)| < ε := lt_of_le_of_lt combi h2ε4ltε
        -- simp [sub_eq_add_neg, add_assoc, add_left_comm] at bound
        -- ring_nf
        -- rw [add_assoc]
        -- exact bound
        sorry
    constructor
    · apply cont_seq_imp_cont_ε_δ
      exact seq_cont
    · exact seq_cont

-- Proof that continuous functions attain their bounds
