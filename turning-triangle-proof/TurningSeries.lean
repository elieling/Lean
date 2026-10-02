import Turning

/-! The exact Taylor-series / geometric-series comparison in the manuscript. -/

namespace Turning

theorem two_pow_le_even_factorial (k : ℕ) : 2 ^ k ≤ (2 * k).factorial := by
  calc
    2 ^ k = 2 ^ k * 1 := by simp
    _ ≤ 2 ^ k * k.factorial := Nat.mul_le_mul_left _ (Nat.factorial_pos k)
    _ ≤ (2 * k).factorial := Nat.two_pow_mul_factorial_le_factorial_two_mul k

/-- The geometric series converges under precisely the displayed hypothesis. -/
theorem cosh_le_geometric_series {s : ℝ} (hs : s ^ 2 / 2 < 1) :
    Real.cosh s ≤ 1 / (1 - s ^ 2 / 2) := by
  have hc := Real.hasSum_cosh s
  have hg := hasSum_geometric_of_lt_one (by positivity : 0 ≤ s ^ 2 / 2) hs
  calc
    Real.cosh s = ∑' k : ℕ, s ^ (2 * k) / ((2 * k).factorial : ℝ) := hc.tsum_eq.symm
    _ ≤ ∑' k : ℕ, (s ^ 2 / 2) ^ k := by
      apply hc.summable.tsum_le_tsum _ hg.summable
      intro k
      have hfact : (2 : ℝ) ^ k ≤ ((2 * k).factorial : ℝ) := by
        exact_mod_cast two_pow_le_even_factorial k
      rw [div_pow, ← pow_mul]
      have hpow : 0 ≤ s ^ (2 * k) := by rw [pow_mul]; positivity
      exact div_le_div_of_nonneg_left hpow (by positivity) hfact
    _ = (1 - s ^ 2 / 2)⁻¹ := hg.tsum_eq
    _ = 1 / (1 - s ^ 2 / 2) := by rw [one_div]

theorem cosh_le_eight_sevenths_by_series {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    Real.cosh s ≤ 8 / 7 := by
  have hsquare : s ^ 2 / 2 ≤ (1 : ℝ) / 8 := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs)]
  calc
    Real.cosh s ≤ 1 / (1 - s ^ 2 / 2) := cosh_le_geometric_series (by linarith)
    _ ≤ 8 / 7 := (div_le_iff₀ (by linarith)).2 (by linarith)

end Turning
