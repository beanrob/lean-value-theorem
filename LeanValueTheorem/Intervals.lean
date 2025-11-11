import Mathlib.Data.Real.Basic

def ooi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x < b })
def cci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x ≤ b })

def oci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x ≤ b })
def coi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x < b })

def is_interval (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = ooi a b ∨
  I = cci a b ∨
  I = oci a b ∨
  I = coi a b

def is_open (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = ooi a b

def is_closed (I : Set ℝ) : Prop :=
  ∃ a b : ℝ,
  I = cci a b

lemma open_interval (I : Set ℝ) : is_open I → is_interval I := by
  unfold is_open
  intro h
  let ⟨a, b, h'⟩ := h
  unfold is_interval
  use a
  use b
  aesop

lemma closed_interval (I : Set ℝ) : is_closed I → is_interval I := by
  unfold is_closed
  intro h
  let ⟨a, b, h'⟩ := h
  unfold is_interval
  use a
  use b
  aesop
