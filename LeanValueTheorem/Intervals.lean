import Mathlib.Data.Real.Basic


-- Definitions for intervals from a to b
  -- ooi = open-open interval
  -- cci = closed-closed interval
  -- oci = open-closed interval
  -- coi = closed-open interval
def ooi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x < b })
def cci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x ≤ b })
def oci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x ≤ b })
def coi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x < b })

-- Definition for whether a set is an interval
def is_interval (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = ooi a b ∨
  I = cci a b ∨
  I = oci a b ∨
  I = coi a b

-- Defintion for whether a set is an open interval
def is_open (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = ooi a b

-- Defintion for whether a set is a closed interval
def is_closed (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = cci a b

-- Proof that open intervals are open
lemma open_interval (I : Set ℝ) : is_open I → is_interval I := by
  unfold is_open
  intro h
  let ⟨a, b, h'⟩ := h
  unfold is_interval
  use a
  use b
  aesop

-- Proof that closed intervals are closed
lemma closed_interval (I : Set ℝ) : is_closed I → is_interval I := by
  unfold is_closed
  intro h
  let ⟨a, b, h'⟩ := h
  unfold is_interval
  use a
  use b
  aesop

-- Proof that if x is in an open interval then it is in the corresponding closed interval
lemma open_in_closed (a b x : ℝ) : x ∈ (ooi a b) → x ∈ (cci a b) := by
 intro h
 unfold cci
 unfold ooi at h
 simp at h
 simp
 cases h
 and_intros
 · (expose_names; exact Std.le_of_lt left)
 · (expose_names; exact Std.le_of_lt right)

-- Proof that an open interval (a,b) with a < b is non-empty
lemma non_empty (a b : ℝ) : a < b → ∃ c : ℝ, c ∈ (ooi a b) := by
 intro h
 let c : ℝ := (a + b) / 2
 have ha : a < c := by exact left_lt_add_div_two.mpr h
 have hb : c < b := by exact add_div_two_lt_right.mpr h
 have hc : c ∈ (ooi a b) := by
  unfold ooi
  exact Set.mem_sep ha hb
 exact Exists.intro c hc
