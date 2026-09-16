import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_31 (x : NNReal) (u : ℕ → NNReal) (h₀ : ∀ n, u (n + 1) = NNReal.sqrt (x + u n))
  (h₁ : Filter.Tendsto u Filter.atTop (𝓝 9)) : 9 = NNReal.sqrt (x + 9) := by
  have h₂:  Filter.Tendsto (fun n ↦ u (n + 1)) Filter.atTop (𝓝 9) :=
  h₁.comp (Filter.tendsto_add_atTop_nat 1)
  have h₃: Filter.Tendsto (fun n ↦ NNReal.sqrt (x + u n)) Filter.atTop (𝓝 9) := by
    simp_rw[← h₀]
    exact h₂
  have h_add : Filter.Tendsto (fun n ↦ x + u n) Filter.atTop (𝓝 (x + 9)) :=
    Filter.Tendsto.add tendsto_const_nhds h₁
  have hc : Continuous (fun y : NNReal ↦ NNReal.sqrt y) := NNReal.continuous_sqrt
  have h_continuous : Filter.Tendsto (fun n ↦ NNReal.sqrt (x + u n)) Filter.atTop (𝓝 (NNReal.sqrt (x + 9))) :=
    Filter.Tendsto.comp (Continuous.tendsto hc (x + 9)) h_add
  exact tendsto_nhds_unique h₃ h_continuous
