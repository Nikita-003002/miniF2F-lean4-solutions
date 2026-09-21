import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_13 (u v : ℕ) (S : Set ℕ)
  (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ 14 * n % 100 = 46) (h₁ : IsLeast S u)
  (h₂ : IsLeast (S \ {u}) v) : (u + v : ℚ) / 2 = 64 := by
  have hu: u = 39 := by
    apply le_antisymm (h₁.right (by rw[h₀]; decide))
    by_contra! h; have ⟨_, h_mod⟩ := (h₀ u).mp h₁.left
    interval_cases u <;> revert h_mod <;> decide
  have hv: v = 89 := by
    apply le_antisymm (h₂.right ⟨by rw[h₀]; decide, by norm_num [hu]⟩)
    by_contra! h; have ⟨h_in, h_neg⟩ := (Set.mem_diff _).mp h₂.left
    rw[h₀] at h_in; rw[hu] at h_neg
    interval_cases v <;> revert h_in h_neg <;> decide
  rw[hu, hv]
  ring
