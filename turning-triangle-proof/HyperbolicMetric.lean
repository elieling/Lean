import Hyperboloid
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-! The coordinate hyperboloid embeds into mathlib's hyperbolic upper half-plane.
The distance identities below certify that the perpendicular parameter measures
hyperbolic arclength. -/

namespace Turning.Hyperboloid

theorem denominator_pos {p : Vec} (hp : OnSheet p) : 0 < p.1 - p.2.1 := by
  have ht := hp.1
  have hnorm := hp.2
  dsimp [lorentz] at hnorm
  by_contra h
  have hx : p.1 ≤ p.2.1 := by linarith
  have hm : 0 ≤ (p.2.1 - p.1) * (p.2.1 + p.1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg p.2.2]

noncomputable def toUpper (p : Vec) (hp : OnSheet p) : UpperHalfPlane :=
  ⟨⟨p.2.2 / (p.1 - p.2.1), 1 / (p.1 - p.2.1)⟩,
    one_div_pos.mpr (denominator_pos hp)⟩

theorem cosh_dist_toUpper (p q : Vec) (hp : OnSheet p) (hq : OnSheet q) :
    Real.cosh (dist (toUpper p hp) (toUpper q hq)) = lorentz p q := by
  have hp0 := ne_of_gt (denominator_pos hp)
  have hq0 := ne_of_gt (denominator_pos hq)
  have hp_norm : p.2.2 ^ 2 + 1 = (p.1 - p.2.1) * (p.1 + p.2.1) := by
    have h := hp.2
    dsimp [lorentz] at h
    nlinarith
  have hq_norm : q.2.2 ^ 2 + 1 = (q.1 - q.2.1) * (q.1 + q.2.1) := by
    have h := hq.2
    dsimp [lorentz] at h
    nlinarith
  have hid :
      (p.2.2 * (q.1 - q.2.1) - q.2.2 * (p.1 - p.2.1)) ^ 2 +
          (q.1 - q.2.1) ^ 2 + (p.1 - p.2.1) ^ 2 =
        2 * (p.1 - p.2.1) * (q.1 - q.2.1) * lorentz p q := by
    calc
      _ = (p.2.2 ^ 2 + 1) * (q.1 - q.2.1) ^ 2 +
          (q.2.2 ^ 2 + 1) * (p.1 - p.2.1) ^ 2 -
          2 * p.2.2 * q.2.2 * (p.1 - p.2.1) * (q.1 - q.2.1) := by ring
      _ = _ := by rw [hp_norm, hq_norm]; dsimp [lorentz]; ring
  rw [UpperHalfPlane.cosh_dist']
  dsimp [toUpper, UpperHalfPlane.re, UpperHalfPlane.im]
  calc
    _ = ((p.2.2 * (q.1 - q.2.1) - q.2.2 * (p.1 - p.2.1)) ^ 2 +
        (q.1 - q.2.1) ^ 2 + (p.1 - p.2.1) ^ 2) /
        (2 * (p.1 - p.2.1) * (q.1 - q.2.1)) := by
      field_simp
      ring
    _ = lorentz p q := by
      rw [div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) hp0) hq0)]
      simpa [mul_comm] using hid

theorem dist_toUpper_eq_abs_of_lorentz {p q : Vec} (hp : OnSheet p) (hq : OnSheet q)
    {r : ℝ} (hr : lorentz p q = Real.cosh r) :
    dist (toUpper p hp) (toUpper q hq) = |r| := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg (abs_nonneg r)
  rw [cosh_dist_toUpper, hr, Real.cosh_abs]

theorem dist_perp (s θ u v : ℝ) :
    dist (toUpper (perp s θ u) (perp_onSheet s θ u))
      (toUpper (perp s θ v) (perp_onSheet s θ v)) = |u - v| :=
  dist_toUpper_eq_abs_of_lorentz _ _ (perp_lorentz s θ u v)

theorem isometry_perp (s θ : ℝ) :
    Isometry (fun u => toUpper (perp s θ u) (perp_onSheet s θ u)) :=
  Isometry.of_dist_eq fun u v => by rw [dist_perp, Real.dist_eq]

theorem mirror_lorentz (p q : Vec) : lorentz (mirror p) (mirror q) = lorentz p q := by
  simp [lorentz, mirror]

theorem dist_mirror (p q : Vec) (hp : OnSheet p) (hq : OnSheet q) :
    dist (toUpper (mirror p) (mirror_onSheet hp))
      (toUpper (mirror q) (mirror_onSheet hq)) = dist (toUpper p hp) (toUpper q hq) := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  rw [cosh_dist_toUpper, cosh_dist_toUpper, mirror_lorentz]

theorem dist_mirror_perp (s θ u v : ℝ) :
    dist (toUpper (mirror (perp s θ u)) (mirror_onSheet (perp_onSheet s θ u)))
      (toUpper (mirror (perp s θ v)) (mirror_onSheet (perp_onSheet s θ v))) = |u - v| := by
  apply dist_toUpper_eq_abs_of_lorentz
  rw [mirror_lorentz, perp_lorentz]

theorem isometry_mirror_perp (s θ : ℝ) :
    Isometry (fun u =>
      toUpper (mirror (perp s θ u)) (mirror_onSheet (perp_onSheet s θ u))) :=
  Isometry.of_dist_eq fun u v => by rw [dist_mirror_perp, Real.dist_eq]

theorem ray_lorentz (s t θ : ℝ) :
    lorentz (ray s θ) (ray t θ) = Real.cosh (s - t) := by
  rw [Real.cosh_sub]
  dsimp [ray, lorentz]
  ring_nf
  simp only [Real.sin_sq]
  ring

theorem dist_ray (s t θ : ℝ) :
    dist (toUpper (ray s θ) (ray_onSheet s θ))
      (toUpper (ray t θ) (ray_onSheet t θ)) = |s - t| :=
  dist_toUpper_eq_abs_of_lorentz _ _ (ray_lorentz s t θ)

theorem isometry_ray (θ : ℝ) :
    Isometry (fun s => toUpper (ray s θ) (ray_onSheet s θ)) :=
  Isometry.of_dist_eq fun s t => by rw [dist_ray, Real.dist_eq]

end Turning.Hyperboloid
