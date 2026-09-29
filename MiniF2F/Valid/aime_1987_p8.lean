import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1987_p8 :
  IsGreatest { n : ℕ | 0 < n ∧ ∃! k : ℕ, (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 } 112 := by
    have h_eq: ∀ n : ℕ, (0 < n) → ∀ k : ℕ, ((8 : ℝ) / 15 < n / (n + k : ℝ) ∧ (n : ℝ) / (n + k) < 7 / 13 ↔ 8 * k < 7 * n ∧ 6 * n < 7 * k) := by
      intro n hn k
      rw [lt_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
      constructor
      · rintro ⟨h₁, h₂⟩
        constructor
        · exact_mod_cast (show (8 : ℝ) * k < 7 * n by linarith)
        · exact_mod_cast (show (6 : ℝ) * n < 7 * k by linarith)
      · rintro ⟨h₁, h₂⟩
        have h₁_r: (8 : ℝ) * k < 7 * n := by exact_mod_cast (by linarith)
        have h₂_r: (6 : ℝ) * n < 7 * k := by exact_mod_cast (by linarith)
        constructor <;> linarith

    have set_eq: {(n : ℕ) | 0 < n ∧ ∃! (k : ℕ), (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13} =
                 {n | 0 < n ∧ ∃! k, 8 * k < 7 * n ∧ 6 * n < 7 * k} := by
      ext n
      simp only [Set.mem_setOf_eq];
      apply and_congr_right
      intro hn
      simp only [h_eq n hn]

    rw [set_eq]
    refine ⟨⟨by decide, 97, by decide, fun n ↦ by omega⟩, fun n ⟨_, k, _, huniq⟩ ↦ ?_⟩
    have h1: ¬(8 * (k + 1) < 7 * n ∧ 6 * n < 7 * (k + 1)) := fun h ↦ by have := huniq _ h; omega
    have h2: ¬(8 * (k - 1) < 7 * n ∧ 6 * n < 7 * (k - 1)) := fun h ↦ by have := huniq _ h; omega
    have hk0: 0 < k := by omega
    omega
