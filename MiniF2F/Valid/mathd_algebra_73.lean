import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_73 (p q r x : ℂ) (h₀ : (x - p) * (x - q) = (r - p) * (r - q)) (h₁ : x ≠ r) :
  x = p + q - r := by
  have h₂: (x - r) * (x - (p + q - r)) = 0 := by
    calc
    (x - r) * (x - (p + q - r)) = (x - p) * (x - q) - (r - p) * (r - q) := by ring
    _ = (r - p) * (r - q) - (r - p) * (r - q) := by rw[h₀]
    _ = 0 := by apply sub_self
  have h₃: x - r ≠ 0 := by apply sub_ne_zero.mpr h₁
  have h₄: x - (p + q - r) = 0 := by apply (mul_eq_zero.mp h₂).resolve_left h₃
  exact eq_of_sub_eq_zero h₄
