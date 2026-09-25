import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2002_p1 (f : ℂ → ℂ) (h₀ : ∀ x, f x = (2 * x + 3) * (x - 4) + (2 * x + 3) * (x - 6))
  (h₁ : Fintype (f ⁻¹' {0})) : (∑ y ∈ (f ⁻¹' {0}).toFinset, y) = 7 / 2 := by
  have h_eq: ∀ y,  f y = 0 ↔ y = - 3 / 2 ∨ y = 5 := by
    intro y
    have h₂: (2 * y + 3) * (y - 4) + (2 * y + 3) * (y - 6) = (2 * y + 3) * (2 * y - 10) := by ring
    rw[h₀, h₂]
    constructor <;>
    intro h_roots
    rcases mul_eq_zero.mp h_roots with h | h
    · left<;> linear_combination (1 / 2) * h
    · right<;> linear_combination (1 / 2) * h
    rcases h_roots with rfl | rfl <;> norm_num
  have f_inset: (f ⁻¹' {0}).toFinset = {-3 / 2, 5} := by ext y; simp [h_eq]
  rw[f_inset, Finset.sum_pair (by norm_num)]
  norm_num
