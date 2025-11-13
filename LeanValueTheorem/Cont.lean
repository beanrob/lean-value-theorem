import Mathlib.Data.Real.Basic
import LeanValueTheorem.Intervals

def is_cont_at (I : Set ℝ) (hI : is_interval I) (f: I → ℝ) (a : I) : Prop := True

def is_cont (I : Set ℝ) (hI : is_interval I) (f: I → ℝ) : Prop := True
