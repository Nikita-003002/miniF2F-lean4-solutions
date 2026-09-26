import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

def v_aux : ℕ → ℕ × ℕ
| 0 => (4, 7)
| n + 1 => ((v_aux n).2, ((v_aux n).1 + (v_aux n).2) % 10)

def v (n : ℕ) : ℕ := (v_aux n).1

def sum_v : ℕ → ℕ
| 0 => 0
| n + 1 => sum_v n + v n

lemma v_aux_12 (n : ℕ) : v_aux (n + 12) = v_aux n := by
  induction n with | zero => rfl | succ k ih => change v_aux (k + 12 + 1) = _; rw [v_aux, ih]; rfl

lemma v_12 (n : ℕ) : v (n + 12) = v n := by simp only [v, v_aux_12]

lemma sum_v_12 (n : ℕ) : sum_v (n + 12) = sum_v n + 60 := by
  induction n with | zero => rfl | succ k ih => change sum_v (k + 12 + 1) = _; rw [sum_v, ih, v_12, sum_v]; omega

lemma sum_v_cycles (n k : ℕ) : sum_v (n * 12 + k) = n * 60 + sum_v k := by
  induction n with | zero => simp | succ m ih =>
  have h: (m + 1) * 12 + k = (m * 12 + k) + 12 := by omega;
  rw [h, sum_v_12, ih]; omega

theorem amc12a_2002_p21 (u : ℕ → ℕ) (h₀ : u 0 = 4) (h₁ : u 1 = 7)
    (h₂ : ∀ n ≥ 0, u (n + 2) = (u n + u (n + 1)) % 10) :
    ∀ n, (∑ k ∈ Finset.range n, u k) > 10000 → 1999 ≤ n := by
    have u_eq : ∀ n, u n = v n ∧ u (n + 1) = (v_aux n).2 := by
        intro n; induction n with | zero => exact ⟨h₀, h₁⟩ | succ k ih => exact ⟨ih.2, by rw [h₂ k (by omega), ih.1, ih.2]; rfl⟩

    have sum_eq : ∀ n, ∑ k ∈ Finset.range n, u k = sum_v n := by
        intro n; induction n with | zero => rfl | succ k ih => rw [Finset.sum_range_succ, ih, (u_eq k).1]; rfl

    have sum_mono : ∀ {a b}, a ≤ b → sum_v a ≤ sum_v b := by
        intro a b h; obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        induction d with | zero => exact le_rfl | succ d ih => rw [Nat.add_succ, sum_v]; omega

    intro n hn; by_contra! h_contra
    have h_le : sum_v n ≤ 10000 := calc
        sum_v n ≤ sum_v 1998 := sum_mono (by omega)
        _ = sum_v (166 * 12 + 6) := rfl
        _ = 166 * 60 + sum_v 6 := sum_v_cycles 166 6
        _ ≤ 10000 := by decide

    rw [← sum_eq n] at h_le
    omega
