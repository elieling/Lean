import TurningSeries
import TriangleSeparation
import EqualLegTriangle

/-!
# The two-right-triangle proof of the turning lemma

This follows the manuscript's contradiction argument for the inward placement
specified by its figure. It uses actual equal-leg right triangles, proves the
geometric separation step, and compares the cosh Taylor series with a geometric
series. It does not invoke the earlier 7/15 intersection theorem.

The necessary correction to the manuscript is explicit: at index x the legs
are s = x*epsilon, not (n²+1)*epsilon. Auxiliary endpoints at distance s fit
inside the full inward perpendiculars because s <= (n²+1)*epsilon <= 2n²*epsilon.
The previously supplied coordinate definitions and their metric/angle proofs
are reused; no geometric fact is added as an axiom or hypothesis.
-/

namespace Turning

open Hyperboloid

theorem offset_pos {n x : ℕ} (hn : 1 ≤ n) (hx : 1 ≤ x) : 0 < offset n x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
  unfold offset epsilon
  positivity

/-- The original contradiction, with all geometric and analytic steps proved. -/
theorem lem_turning_by_triangles {n : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi) :
    ∀ x ∈ Set.Icc 1 (n ^ 2 + 1),
      (lGrid .inward n α x ∩ mGrid .inward n α x).Nonempty := by
  intro x hx
  have hn1 : 1 ≤ n := Nat.le_trans (by norm_num) hn
  let s := offset n x
  let β := Real.pi - α
  let θ := β / 2
  have hs : 0 < s := offset_pos hn1 hx.1
  have hst : s ≤ legLength n := offset_le_legLength hx.2
  have hsmall : s ≤ 1 / 2 := hst.trans (legLength_le_half hn1)
  have hfits : s ≤ 2 * halfWidth n := hst.trans (legLength_le_two_halfWidth hn1)
  have hβ : β ≤ 4 * Real.pi / 15 := by dsimp [β]; linarith
  have hθ0 : 0 ≤ θ := by dsimp [θ, β]; linarith
  have hθπ : θ < Real.pi / 2 := by dsimp [θ, β]; linarith [Real.pi_pos]

  -- Assume the two full inward perpendicular segments do not meet.
  by_contra hdisjoint
  change ¬ ((upperLine s θ '' Set.Icc 0 (2 * halfWidth n)) ∩
    (lowerLine s θ '' Set.Icc 0 (2 * halfWidth n))).Nonempty at hdisjoint

  -- β₁ and β₂ are the actual vertex angles of the reflected equal-leg triangles.
  -- Their diagonals reach the auxiliary endpoints by equalLeg_endpoint_on_ray;
  -- equalLeg_first_length, equalLeg_second_length and equalLeg_right_angle
  -- certify that they are right triangles with both legs of length s.
  let β₁ := unitTangentAngle (mirror (radialTangent 0 θ))
    (mirror (equalLegDirection s θ))
  let β₂ := unitTangentAngle (radialTangent 0 θ) (equalLegDirection s θ)
  have hβ₁ : β₁ = Real.arctan (Real.tanh s / Real.sinh s) :=
    equalLeg_reflected_angle_formula hs θ
  have hβ₂ : β₂ = Real.arctan (Real.tanh s / Real.sinh s) :=
    equalLeg_angle_formula hs θ
  have hequal : β₁ = β₂ := hβ₁.trans hβ₂.symm

  -- Taylor series, coefficient comparison, and the sum of the geometric series.
  have hcosh : Real.cosh s ≤ 8 / 7 := cosh_le_eight_sevenths_by_series hs.le hsmall
  have hrecip : (7 : ℝ) / 8 ≤ 1 / Real.cosh s :=
    (le_div_iff₀ (Real.cosh_pos s)).2 (by linarith)
  have hlower : Real.arctan (7 / 8 : ℝ) ≤ β₁ := by
    rw [hβ₁, tanh_div_sinh hs]
    exact Real.arctan_le_arctan hrecip

  -- arctan(7/8) = π/4 - arctan(1/15) > π/4 - 1/15 > 2π/9.
  have hidentity := arctan_seven_eighths_eq
  have harctan := arctan_lt_self_of_pos (x := (1 / 15 : ℝ)) (by norm_num)
  have hangle₁ : 2 * Real.pi / 9 < β₁ := by linarith [Real.pi_gt_three]
  have hangle₂ : 2 * Real.pi / 9 < β₂ := by linarith

  -- The diagram's strict angular gap follows from disjointness, not an assumption.
  have hseparation := twice_triangle_angle_lt_turning_of_disjoint
    hs hfits hθ0 hθπ hdisjoint
  have hgap : β₁ + β₂ < β := by
    rw [hβ₁, hβ₂]
    dsimp [θ] at hseparation
    linarith

  -- β > β₁+β₂ > 4π/9 > 4π/15 contradicts β ≤ 4π/15.
  have hsum : 4 * Real.pi / 9 < β₁ + β₂ := by
    convert add_lt_add hangle₁ hangle₂ using 1
    ring
  have hbad : 4 * Real.pi / 9 < 4 * Real.pi / 15 := hsum.trans (hgap.trans_le hβ)
  have horder : 4 * Real.pi / 15 ≤ 4 * Real.pi / 9 := by linarith [Real.pi_pos]
  exact (not_lt_of_ge horder) hbad

/-- The same triangle proof applies in every isometric local coordinate frame. -/
theorem lem_turning_by_triangles_isometric_copy
    (F : UpperHalfPlane ≃ᵢ UpperHalfPlane) {n : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi) :
    ∀ x ∈ Set.Icc 1 (n ^ 2 + 1),
      (F '' lGrid .inward n α x ∩ F '' mGrid .inward n α x).Nonempty := by
  intro x hx
  obtain ⟨p, hpL, hpM⟩ := lem_turning_by_triangles hn hα hαπ x hx
  exact ⟨F p, ⟨p, hpL, rfl⟩, p, hpM, rfl⟩

end Turning
