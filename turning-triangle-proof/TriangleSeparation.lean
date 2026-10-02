import LocalGrid

/-!
The geometric separation step in the two-right-triangle proof.

At equal offset `s`, select points at inward distance `s` on each perpendicular.
These auxiliary equal-leg triangles fit whenever the full segment length `L`
satisfies `s ≤ L`. If their angular sectors overlap, the explicit geodesics
intersect by the intermediate value theorem. Consequently disjoint inward
segments force the strict angular gap used in the original contradiction.

This argument does not use the numerical turning bound or a previously proved
local-grid intersection theorem.
-/

namespace Turning

open Hyperboloid

/-- Overlap of the equal-leg triangle angles forces an actual intersection. -/
theorem inward_segments_intersect_of_angle_le {s θ L : ℝ}
    (hs : 0 < s) (hsL : s ≤ L) (hθ0 : 0 ≤ θ) (hθπ : θ < Real.pi / 2)
    (hangle : θ ≤ Real.arctan (Real.tanh s / Real.sinh s)) :
    ((upperLine s θ '' Set.Icc 0 L) ∩
      (lowerLine s θ '' Set.Icc 0 L)).Nonempty := by
  have hsinh : 0 < Real.sinh s := Real.sinh_pos_iff.mpr hs
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  have htan : Real.tan θ ≤ Real.tanh s / Real.sinh s := by
    have hm := Real.strictMonoOn_tan.monotoneOn
      (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], hθπ⟩)
      (Real.arctan_mem_Ioo (Real.tanh s / Real.sinh s)) hangle
    simpa only [Real.tan_arctan] using hm
  have hprod : Real.sinh s * Real.tan θ ≤ Real.tanh s := by
    have hm := (le_div_iff₀ hsinh).mp htan
    nlinarith
  rw [Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh,
    ← mul_div_assoc] at hprod
  have hend : Real.cosh s * Real.sinh s * Real.sin θ ≤
      Real.sinh s * Real.cos θ := by
    have hm := (div_le_div_iff₀ hcos (Real.cosh_pos s)).mp hprod
    nlinarith
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  obtain ⟨u, hu, heq⟩ := exists_inward_intersection hs.le hs.le hsin hend
  have huL : u ∈ Set.Icc 0 L := ⟨hu.1, hu.2.trans hsL⟩
  refine ⟨upperLine s θ u, ⟨u, huL, rfl⟩, u, huL, ?_⟩
  unfold lowerLine upperLine
  congr 1

/-- The diagram's strict separation `β₁ + β₂ < β`, without a geometric hypothesis. -/
theorem twice_triangle_angle_lt_turning_of_disjoint {s θ L : ℝ}
    (hs : 0 < s) (hsL : s ≤ L) (hθ0 : 0 ≤ θ) (hθπ : θ < Real.pi / 2)
    (hdisjoint : ¬ ((upperLine s θ '' Set.Icc 0 L) ∩
      (lowerLine s θ '' Set.Icc 0 L)).Nonempty) :
    2 * Real.arctan (Real.tanh s / Real.sinh s) < 2 * θ := by
  by_contra hnot
  have hangle : θ ≤ Real.arctan (Real.tanh s / Real.sinh s) := by linarith
  exact hdisjoint (inward_segments_intersect_of_angle_le hs hsL hθ0 hθπ hangle)

end Turning
