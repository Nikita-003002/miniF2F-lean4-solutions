import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p11 (a b : ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0) (h₁ : a * b = a - b) :
    a / b + b / a - a * b = 2 := by
rcases h₀ with ⟨ha, hb⟩
calc
     a / b + b / a - a * b = (a ^ 2 + b ^ 2 - (a * b ) ^ 2) / (a * b) := by field_simp
     _ = (a ^ 2 + b ^ 2 - (a - b ) ^ 2) / (a * b) := by rw[h₁]
     _ = 2 := by field_simp [ha, hb]; ring
