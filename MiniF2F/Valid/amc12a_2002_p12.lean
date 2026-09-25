import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2002_p12 (f : ℝ → ℝ) (k : ℝ) (a b : ℕ) (h₀ : ∀ x, f x = x ^ 2 - 63 * x + k)
  (h₁ : f a = 0 ∧ f b = 0) (h₂ : a ≠ b) (h₃ : Nat.Prime a ∧ Nat.Prime b) : k = 122 := by
  have ha: a ^ 2 - 63 * a + k = 0 := by rw [← h₀, h₁.left]
  have hb: b ^ 2 - 63 * b + k = 0 := by rw[← h₀, h₁.right]
  have h_sum: a + b = 63 := by
    have h_eq: ((a: ℝ) - b) * (a + b - 63) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp h_eq with h | h
    · exact False.elim (h₂ <| by exact_mod_cast eq_of_sub_eq_zero h)
    · exact_mod_cast eq_of_sub_eq_zero h

  rcases h₃.1.eq_two_or_odd with rfl | _
  · norm_num at ha; linear_combination ha
  rcases h₃.2.eq_two_or_odd with rfl | _
  · norm_num at hb; linear_combination hb
  omega
