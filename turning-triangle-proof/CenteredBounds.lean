import Turning

/-!
Corrected analytic estimates for perpendicular segments whose total length is
`2 * n^2 * epsilon n`. Their half-width is smaller than the maximum offset
`legLength n`, so the equal-leg estimate in the original excerpt does not apply.
-/

namespace Turning

noncomputable def halfWidth (n : ℕ) : ℝ := (n : ℝ) ^ 2 * epsilon n

theorem halfWidth_pos {n : ℕ} (hn : 1 ≤ n) : 0 < halfWidth n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold halfWidth epsilon
  positivity

theorem legLength_le_two_halfWidth {n : ℕ} (hn : 1 ≤ n) :
    legLength n ≤ 2 * halfWidth n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  unfold legLength
  calc
    ((n : ℝ) ^ 2 + 1) / (4 * (n : ℝ) ^ 8) ≤
        (2 * (n : ℝ) ^ 2) / (4 * (n : ℝ) ^ 8) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * halfWidth n := by unfold halfWidth epsilon; ring

/-- Monotonicity of hyperbolic tangent, proved directly from `sinh_sub`. -/
theorem tanh_monotone' : Monotone Real.tanh := by
  intro a b hab
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)]
  have hs : 0 ≤ Real.sinh (b - a) := by
    simpa only [Real.sinh_zero] using
      (Real.sinh_le_sinh.mpr (sub_nonneg.mpr hab) :
        Real.sinh 0 ≤ Real.sinh (b - a))
  rw [Real.sinh_sub] at hs
  nlinarith

/-- The half-angle identity that replaces the incorrect equal-leg formula. -/
theorem tanh_half_eq (t : ℝ) :
    Real.tanh (t / 2) = Real.sinh t / (1 + Real.cosh t) := by
  have harg : 2 * (t / 2) = t := by ring
  have hs := Real.sinh_two_mul (t / 2)
  have hc := Real.cosh_two_mul (t / 2)
  rw [harg] at hs hc
  have hc' : 1 + Real.cosh t = 2 * Real.cosh (t / 2) ^ 2 := by
    nlinarith [Real.cosh_sq' (t / 2)]
  rw [Real.tanh_eq_sinh_div_cosh, hs, hc']
  field_simp [(Real.cosh_pos (t / 2)).ne']
  ring

theorem arctan_seven_fifteenths_eq :
    Real.arctan (7 / 15 : ℝ) = Real.pi / 4 - Real.arctan (4 / 11 : ℝ) := by
  have hadd := Real.arctan_add (x := (7 / 15 : ℝ)) (y := (4 / 11 : ℝ))
    (by norm_num)
  norm_num at hadd
  linarith

theorem two_pi_div_fifteen_lt_arctan_seven_fifteenths :
    2 * Real.pi / 15 < Real.arctan (7 / 15 : ℝ) := by
  rw [arctan_seven_fifteenths_eq]
  have hsmall := arctan_lt_self_of_pos (x := (4 / 11 : ℝ)) (by norm_num)
  linarith [Real.pi_gt_d2]

theorem tan_lt_seven_fifteenths {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 2 * Real.pi / 15) : Real.tan θ < 7 / 15 := by
  have ha := hθ.trans_lt two_pi_div_fifteen_lt_arctan_seven_fifteenths
  simpa only [Real.tan_arctan] using
    Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hθ0
      (Real.arctan_lt_pi_div_two (7 / 15)) ha

/-- A sufficient bound for every centered perpendicular segment. -/
theorem seven_fifteenths_mul_sinh_le_tanh {s t q : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 / 2) (htq : t / 2 ≤ q) :
    (7 / 15 : ℝ) * Real.sinh s ≤ Real.tanh q := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hc := cosh_le_eight_sevenths ht0 ht
  have hden : 0 < 1 + Real.cosh t := by linarith [Real.cosh_pos t]
  have hratio : (7 / 15 : ℝ) ≤ 1 / (1 + Real.cosh t) :=
    (le_div_iff₀ hden).2 (by linarith)
  have hst' : Real.sinh s ≤ Real.sinh t := Real.sinh_le_sinh.mpr hst
  have hnonneg : 0 ≤ Real.sinh t := by
    simpa only [Real.sinh_zero] using
      (Real.sinh_le_sinh.mpr ht0 : Real.sinh 0 ≤ Real.sinh t)
  calc
    (7 / 15 : ℝ) * Real.sinh s ≤ (7 / 15 : ℝ) * Real.sinh t :=
      mul_le_mul_of_nonneg_left hst' (by norm_num)
    _ ≤ (1 / (1 + Real.cosh t)) * Real.sinh t :=
      mul_le_mul_of_nonneg_right hratio hnonneg
    _ = Real.tanh (t / 2) := by rw [tanh_half_eq]; ring
    _ ≤ Real.tanh q := tanh_monotone' htq

/-- Endpoint inequality used to construct an intersection by continuity. -/
theorem centered_crossing_bound {s t q θ : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 / 2) (htq : t / 2 ≤ q)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 2 * Real.pi / 15) :
    Real.cosh q * Real.sinh s * Real.sin θ ≤ Real.sinh q * Real.cos θ := by
  have htan := tan_lt_seven_fifteenths hθ0 hθ
  have hbound := seven_fifteenths_mul_sinh_le_tanh hs0 hst ht htq
  have hsnonneg : 0 ≤ Real.sinh s := by
    simpa only [Real.sinh_zero] using
      (Real.sinh_le_sinh.mpr hs0 : Real.sinh 0 ≤ Real.sinh s)
  have hprod : Real.sinh s * Real.tan θ ≤ Real.tanh q := by
    have hm := mul_le_mul_of_nonneg_left htan.le hsnonneg
    nlinarith
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh,
    ← mul_div_assoc] at hprod
  have hcross := (div_le_div_iff₀ hcos (Real.cosh_pos q)).mp hprod
  nlinarith

end Turning
