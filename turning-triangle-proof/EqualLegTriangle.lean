import HyperbolicAngles
import HyperbolicMetric
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
The actual equal-leg right triangles used in the turning argument.

For `s > 0`, take `A = ray 0 θ`, `B = ray s θ`, and `C = perp s θ s`.
The two legs have hyperbolic length `s`, and their angle at `B` is right.
The diagonal is an actual radial geodesic from `A` to `C`, not a postulated
angle: `equalLeg_endpoint_on_ray` proves that it reaches `C` at positive time.
Its tangent therefore gives the angle at `A` used below. Reflection gives the
second congruent triangle in the figure.
-/

namespace Turning.Hyperboloid

noncomputable def equalLegAngle (s : ℝ) : ℝ :=
  Real.arctan (1 / Real.cosh s)

noncomputable def equalLegDirection (s θ : ℝ) : Vec :=
  radialTangent 0 (θ - equalLegAngle s)

theorem equalLegAngle_pos (s : ℝ) : 0 < equalLegAngle s := by
  unfold equalLegAngle
  simpa only [Real.arctan_zero] using
    Real.arctan_strictMono (one_div_pos.mpr (Real.cosh_pos s))

theorem equalLegAngle_lt_half_pi (s : ℝ) : equalLegAngle s < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

theorem equalLegDirection_unit (s θ : ℝ) :
    lorentz (equalLegDirection s θ) (equalLegDirection s θ) = -1 :=
  radial_unit 0 _

theorem equalLegDirection_tangent (s θ : ℝ) :
    lorentz (ray 0 θ) (equalLegDirection s θ) = 0 := by
  simp [equalLegDirection, lorentz, ray, radialTangent]

theorem equalLeg_sin_relation (s : ℝ) :
    Real.sin (equalLegAngle s) = Real.cos (equalLegAngle s) / Real.cosh s := by
  have hc : Real.cos (equalLegAngle s) ≠ 0 :=
    ne_of_gt (Real.cos_arctan_pos _)
  have ht : Real.sin (equalLegAngle s) / Real.cos (equalLegAngle s) =
      1 / Real.cosh s := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  field_simp [hc, ne_of_gt (Real.cosh_pos s)] at ht ⊢
  nlinarith

/-- The endpoint has the same outward spatial direction as the diagonal tangent. -/
theorem equalLeg_endpoint_spatial {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    ∃ k : ℝ, 0 < k ∧
      (perp s θ s).2.1 = k * Real.cos (θ - equalLegAngle s) ∧
      (perp s θ s).2.2 = k * Real.sin (θ - equalLegAngle s) := by
  let k := Real.sinh s * Real.cosh s / Real.cos (equalLegAngle s)
  have hc : 0 < Real.cos (equalLegAngle s) := Real.cos_arctan_pos _
  have hk : 0 < k := div_pos
    (mul_pos (Real.sinh_pos_iff.mpr hs) (Real.cosh_pos s)) hc
  have hkc : k * Real.cos (equalLegAngle s) = Real.sinh s * Real.cosh s := by
    dsimp [k]
    field_simp
  have hks : k * Real.sin (equalLegAngle s) = Real.sinh s := by
    rw [equalLeg_sin_relation]
    dsimp [k]
    field_simp
  refine ⟨k, hk, ?_, ?_⟩
  · rw [Real.cos_sub]
    change Real.cosh s * Real.sinh s * Real.cos θ + Real.sinh s * Real.sin θ = _
    calc
      _ = (k * Real.cos (equalLegAngle s)) * Real.cos θ +
          (k * Real.sin (equalLegAngle s)) * Real.sin θ := by rw [hkc, hks]; ring
      _ = _ := by ring
  · rw [Real.sin_sub]
    change Real.cosh s * Real.sinh s * Real.sin θ - Real.sinh s * Real.cos θ = _
    calc
      _ = (k * Real.cos (equalLegAngle s)) * Real.sin θ -
          (k * Real.sin (equalLegAngle s)) * Real.cos θ := by rw [hkc, hks]; ring
      _ = _ := by ring

/-- The diagonal radial geodesic reaches the actual endpoint at positive time. -/
theorem equalLeg_endpoint_on_ray {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ray r (θ - equalLegAngle s) = perp s θ s := by
  obtain ⟨k, hk, hx, hy⟩ := equalLeg_endpoint_spatial hs θ
  let r := Real.arsinh k
  have hr : 0 < r := Real.arsinh_pos_iff.mpr hk
  have hsr : Real.sinh r = k := Real.sinh_arsinh k
  have hnorm : (perp s θ s).1 ^ 2 = 1 + k ^ 2 := by
    have hp := (perp_onSheet s θ s).2
    change (perp s θ s).1 * (perp s θ s).1 -
      (perp s θ s).2.1 * (perp s θ s).2.1 -
      (perp s θ s).2.2 * (perp s θ s).2.2 = 1 at hp
    rw [hx, hy] at hp
    have hid := congrArg (fun z : ℝ => k ^ 2 * z)
      (Real.sin_sq_add_cos_sq (θ - equalLegAngle s))
    dsimp only at hid
    nlinarith
  have hcr : Real.cosh r = (perp s θ s).1 := by
    have hid := Real.cosh_sq r
    rw [hsr] at hid
    nlinarith [(perp_onSheet s θ s).1, Real.cosh_pos r]
  refine ⟨r, hr, ?_⟩
  apply Prod.ext
  · exact hcr
  · apply Prod.ext
    · simpa only [ray, hsr] using hx.symm
    · simpa only [ray, hsr] using hy.symm

theorem equalLeg_diagonal_derivative (s θ : ℝ) :
    HasDerivAt (fun r => ray r (θ - equalLegAngle s)) (equalLegDirection s θ) 0 :=
  hasDerivAt_ray 0 _

/-- Angle `BAC`, obtained from the tangent of the actual diagonal geodesic. -/
theorem equalLeg_angle_at_origin (s θ : ℝ) :
    unitTangentAngle (radialTangent 0 θ) (equalLegDirection s θ) =
      equalLegAngle s := by
  have hinner : -lorentz (radialTangent 0 θ) (equalLegDirection s θ) =
      Real.cos (equalLegAngle s) := by
    simp only [equalLegDirection, lorentz, radialTangent, Real.sinh_zero,
      Real.cosh_zero, zero_mul, one_mul, zero_sub]
    calc
      _ = Real.cos θ * Real.cos (θ - equalLegAngle s) +
          Real.sin θ * Real.sin (θ - equalLegAngle s) := by ring
      _ = Real.cos (θ - (θ - equalLegAngle s)) := (Real.cos_sub _ _).symm
      _ = _ := by congr 1; ring
  unfold unitTangentAngle
  rw [hinner]
  exact Real.arccos_cos (equalLegAngle_pos s).le
    (by linarith [equalLegAngle_lt_half_pi s, Real.pi_pos])

/-- The hyperbolic right-triangle formula follows for the actual equal-leg triangle. -/
theorem equalLeg_angle_formula {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    unitTangentAngle (radialTangent 0 θ) (equalLegDirection s θ) =
      Real.arctan (Real.tanh s / Real.sinh s) := by
  rw [equalLeg_angle_at_origin, Turning.tanh_div_sinh hs]
  rfl

/-- At the foot, the direction back toward the origin is the negative radial tangent. -/
theorem equalLeg_right_angle (s θ : ℝ) :
    unitTangentAngle (-radialTangent s θ) (inward θ) = Real.pi / 2 := by
  have hinner : lorentz (-radialTangent s θ) (inward θ) = 0 := by
    dsimp [lorentz, radialTangent, inward]
    ring
  simp [unitTangentAngle, hinner]

theorem equalLeg_first_length {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    dist (toUpper (ray 0 θ) (ray_onSheet 0 θ))
      (toUpper (ray s θ) (ray_onSheet s θ)) = s := by
  rw [dist_ray]
  simp [abs_of_pos hs]

theorem equalLeg_second_length {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    dist (toUpper (ray s θ) (ray_onSheet s θ))
      (toUpper (perp s θ s) (perp_onSheet s θ s)) = s := by
  have h := dist_perp s θ 0 s
  simpa only [perp_zero, zero_sub, abs_neg, abs_of_pos hs] using h

theorem unitTangentAngle_mirror (p q : Vec) :
    unitTangentAngle (mirror p) (mirror q) = unitTangentAngle p q := by
  unfold unitTangentAngle
  rw [mirror_lorentz]

/-- Reflection supplies the equal angle in the second triangle. -/
theorem equalLeg_reflected_angle (s θ : ℝ) :
    unitTangentAngle (mirror (radialTangent 0 θ))
      (mirror (equalLegDirection s θ)) = equalLegAngle s := by
  rw [unitTangentAngle_mirror, equalLeg_angle_at_origin]

theorem equalLeg_reflected_angle_formula {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    unitTangentAngle (mirror (radialTangent 0 θ))
      (mirror (equalLegDirection s θ)) =
        Real.arctan (Real.tanh s / Real.sinh s) := by
  rw [unitTangentAngle_mirror]
  exact equalLeg_angle_formula hs θ

/-- The reflected diagonal also reaches its endpoint at positive time. -/
theorem equalLeg_reflected_endpoint_on_ray {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      ray r (-(θ - equalLegAngle s)) = mirror (perp s θ s) := by
  obtain ⟨r, hr, heq⟩ := equalLeg_endpoint_on_ray hs θ
  refine ⟨r, hr, ?_⟩
  rw [← heq]
  simp only [ray, mirror, Real.cos_neg, Real.sin_neg, mul_neg]

theorem equalLeg_reflected_right_angle (s θ : ℝ) :
    unitTangentAngle (mirror (-radialTangent s θ)) (mirror (inward θ)) =
      Real.pi / 2 := by
  rw [unitTangentAngle_mirror, equalLeg_right_angle]

end Turning.Hyperboloid
