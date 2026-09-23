import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_43 : IsGreatest { n : ℕ | 15 ^ n ∣ 942! } 233 := by
constructor
· simp only [Set.mem_setOf_eq]; norm_num
· intro n hn
  by_contra! h
  have h_le: 234 ≤ n := h
  have h_false : 15 ^ 234 ∣ 942! := by
    apply dvd_trans (pow_dvd_pow 15 h_le) hn
  norm_num at h_false
