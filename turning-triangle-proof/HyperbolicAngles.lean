import Hyperboloid

/-!
Tangent and angle certificates for the explicit centered construction. For unit
tangent vectors based at one point of the hyperboloid, the Riemannian inner
product is the negative of the Lorentz form, so their angle is its arccosine.
-/

namespace Turning.Hyperboloid

/-- This angle formula is intended for unit tangent vectors at a common point. -/
noncomputable def unitTangentAngle (v w : Vec) : ℝ := Real.arccos (-lorentz v w)

theorem ray_zero (θ : ℝ) : ray 0 θ = (1, 0, 0) := by
  simp [ray]

theorem hasDerivAt_ray (s θ : ℝ) :
    HasDerivAt (fun r => ray r θ) (radialTangent s θ) s := by
  simpa only [ray, radialTangent] using
    (Real.hasDerivAt_cosh s).prodMk
      (((Real.hasDerivAt_sinh s).mul_const (Real.cos θ)).prodMk
        ((Real.hasDerivAt_sinh s).mul_const (Real.sin θ)))

theorem hasDerivAt_perp_zero (s θ : ℝ) :
    HasDerivAt (perp s θ) (inward θ) 0 := by
  have hx := ((Real.hasDerivAt_cosh 0).mul_const (Real.sinh s * Real.cos θ)).add
    ((Real.hasDerivAt_sinh 0).mul_const (Real.sin θ))
  have hy := ((Real.hasDerivAt_cosh 0).mul_const (Real.sinh s * Real.sin θ)).sub
    ((Real.hasDerivAt_sinh 0).mul_const (Real.cos θ))
  have hpair : HasDerivAt (perp s θ)
      (Real.sinh 0 * Real.cosh s,
       Real.sinh 0 * (Real.sinh s * Real.cos θ) + Real.cosh 0 * Real.sin θ,
       Real.sinh 0 * (Real.sinh s * Real.sin θ) - Real.cosh 0 * Real.cos θ) 0 := by
    change HasDerivAt (fun u => perp s θ u) _ 0
    simpa only [perp, mul_assoc] using
      ((Real.hasDerivAt_cosh 0).mul_const (Real.cosh s)).prodMk (hx.prodMk hy)
  simpa [inward] using hpair

theorem radial_tangent_at_foot (s θ : ℝ) :
    lorentz (ray s θ) (radialTangent s θ) = 0 := by
  dsimp [lorentz, ray, radialTangent]
  ring_nf
  simp only [Real.sin_sq]
  ring

theorem perpendicular_angle (s θ : ℝ) :
    unitTangentAngle (radialTangent s θ) (inward θ) = Real.pi / 2 := by
  simp [unitTangentAngle, perpendicular]

theorem mirror_perp (s θ u : ℝ) :
    mirror (perp s θ u) = perp s (-θ) (-u) := by
  simp [mirror, perp]
  ring

theorem outgoing_inner_product (θ : ℝ) :
    -lorentz (radialTangent 0 θ) (radialTangent 0 (-θ)) = Real.cos (2 * θ) := by
  simp only [lorentz, radialTangent, Real.sinh_zero, Real.cosh_zero,
    Real.cos_neg, Real.sin_neg, zero_mul, one_mul, zero_sub]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem incoming_inner_product (θ : ℝ) :
    -lorentz (-radialTangent 0 θ) (radialTangent 0 (-θ)) = -Real.cos (2 * θ) := by
  simp only [lorentz, radialTangent, Prod.fst_neg, Prod.snd_neg,
    Real.sinh_zero, Real.cosh_zero, Real.cos_neg, Real.sin_neg,
    zero_mul, one_mul, neg_zero, zero_sub, neg_mul]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem outgoing_angle {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    unitTangentAngle (radialTangent 0 θ) (radialTangent 0 (-θ)) = 2 * θ := by
  unfold unitTangentAngle
  rw [outgoing_inner_product]
  exact Real.arccos_cos (by linarith) (by linarith)

theorem interior_angle {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    unitTangentAngle (-radialTangent 0 θ) (radialTangent 0 (-θ)) =
      Real.pi - 2 * θ := by
  unfold unitTangentAngle
  rw [incoming_inner_product, ← Real.cos_pi_sub]
  exact Real.arccos_cos (by linarith) (by linarith)

end Turning.Hyperboloid
