import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2000_p15 (f : ℂ → ℂ) (h₀ : ∀ x, f (x / 3) = x ^ 2 + x + 1)
  (h₁ : Fintype (f ⁻¹' {7})) : (∑ y ∈ (f ⁻¹' {7}).toFinset, y / 3) = -1 / 9 := by
  have heq: ∀ y, f y = 7 ↔ y = -1 ∨ y = 2 / 3 := by
    intro y
    have heq: f (y * 3 / 3) = (y * 3) ^ 2 + (y * 3) + 1 := by rw[h₀ (y * 3)]
    simp at heq
    rw[heq]
    refine ⟨fun hy ↦ ?_, fun h ↦ by rcases h with rfl | rfl <;> norm_num⟩
    have hr: (y + 1) * (y - 2 / 3) = 0 := by linear_combination (1 / 9: ℂ ) * hy
    rcases mul_eq_zero.mp hr with h | h
    · left; linear_combination h
    · right; linear_combination h
  have f_inset: (f ⁻¹' {7}).toFinset = {-1, 2/3} := by ext y; simp[heq]
  rw [f_inset, Finset.sum_pair (by norm_num)]
  norm_num
