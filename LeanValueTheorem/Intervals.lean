import Mathlib.Data.Real.Basic

def ooi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x < b })
def cci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x ≤ b })

def oci : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a < x ∧ x ≤ b })
def coi : ℝ → ℝ → Set ℝ := (fun a b => { x : ℝ | a ≤ x ∧ x < b })
