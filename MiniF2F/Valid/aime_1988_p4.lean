import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1988_p4 (n : ℕ) (a : ℕ → ℝ) (h₀ : ∀ n, abs (a n) < 1)
  (h₁ : (∑ k ∈ Finset.range n, abs (a k)) = 19 + abs (∑ k ∈ Finset.range n, a k)) : 20 ≤ n := by
  have hn: (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr (by rintro rfl; simp at h₁)
  have H := Finset.sum_lt_sum_of_nonempty hn (fun k _ => h₀ k)
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at H
  exact_mod_cast (by linarith [abs_nonneg (∑ k ∈ Finset.range n, a k)] : (19 : ℝ) < n)
