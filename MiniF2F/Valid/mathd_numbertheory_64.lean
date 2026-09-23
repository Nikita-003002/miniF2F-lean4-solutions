import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_64 : IsLeast { x : ℕ | 30 * x ≡ 42 [MOD 47] } 39 := by
constructor
· decide
· intro y hy
  change (30 * y) % 47 = 42 % 47 at hy
  omega
