import Mathlib.Data.Real.Basic

def ooi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x < b })
def cci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x ≤ b })

def oci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x ≤ b })
def coi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x < b })

def is_interval (I : Set ℝ) : Prop := ∃ a b : ℝ,
  I = ooi a b ∨
  I = cci a b ∨
  I = oci a b ∨
  I = coi a b
