import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2002_p1 (f : ℂ → ℂ) (h₀ : ∀ x, f x = (2 * x + 3) * (x - 4) + (2 * x + 3) * (x - 6))
  (h₁ : Fintype (f ⁻¹' {0})) : (∑ y ∈ (f ⁻¹' {0}).toFinset, y) = 7 / 2 := by
  have f_inset: (f ⁻¹' {0}).toFinset = {-3 / 2, 5} := by
    ext y
    simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton, h₀]
    rw[show (2 * y + 3) * (y - 4) + (2 * y + 3) * (y - 6) = 4 * (y + 3 / 2) * (y - 5) by ring]
    simp [sub_eq_zero, add_eq_zero_iff_eq_neg]
    norm_num
  rw[f_inset, Finset.sum_pair (by norm_num)]
  norm_num
