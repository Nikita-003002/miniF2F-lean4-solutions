import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have h_id: 2 * (a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)) =
    (a + b - c) * (b + c - a) * (a - b)^2 +
    (b + c - a) * (c + a - b) * (b - c)^2 +
    (c + a - b) * (a + b - c) * (c - a)^2 := by ring
  have hc : 0 ≤ a + b - c := by linarith
  have hb : 0 ≤ c + a - b := by linarith
  have ha : 0 ≤ b + c - a := by linarith
  have h_pos : 0 ≤ (a + b - c) * (b + c - a) * (a - b)^2 +
               (b + c - a) * (c + a - b) * (b - c)^2 +
               (c + a - b) * (a + b - c) * (c - a)^2 := by positivity
  linarith
