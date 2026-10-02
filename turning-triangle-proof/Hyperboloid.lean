import Turning

/-!
Explicit perpendicular geodesics in the hyperboloid model. The bilinear form has
signature (+,-,-). `perp s θ u` starts on the ray of angle θ at distance s and
travels distance u in the perpendicular direction towards the angle bisector.
The segment is centered at u = 0, with parameter interval [-q,q].
-/

namespace Turning.Hyperboloid

abbrev Vec := ℝ × ℝ × ℝ

def lorentz (p q : Vec) : ℝ := p.1 * q.1 - p.2.1 * q.2.1 - p.2.2 * q.2.2

def OnSheet (p : Vec) : Prop := 0 < p.1 ∧ lorentz p p = 1

noncomputable def ray (s θ : ℝ) : Vec :=
  (Real.cosh s, Real.sinh s * Real.cos θ, Real.sinh s * Real.sin θ)

noncomputable def radialTangent (s θ : ℝ) : Vec :=
  (Real.sinh s, Real.cosh s * Real.cos θ, Real.cosh s * Real.sin θ)

noncomputable def inward (θ : ℝ) : Vec := (0, Real.sin θ, -Real.cos θ)

noncomputable def perp (s θ u : ℝ) : Vec :=
  (Real.cosh u * Real.cosh s,
   Real.cosh u * Real.sinh s * Real.cos θ + Real.sinh u * Real.sin θ,
   Real.cosh u * Real.sinh s * Real.sin θ - Real.sinh u * Real.cos θ)

def mirror (p : Vec) : Vec := (p.1, p.2.1, -p.2.2)

noncomputable def upperSegment (s θ q : ℝ) : Set Vec :=
  (perp s θ) '' Set.Icc (-q) q

noncomputable def lowerSegment (s θ q : ℝ) : Set Vec :=
  (fun u => mirror (perp s θ u)) '' Set.Icc (-q) q

theorem perp_zero (s θ : ℝ) : perp s θ 0 = ray s θ := by
  simp [perp, ray]

theorem perp_onSheet (s θ u : ℝ) : OnSheet (perp s θ u) := by
  constructor
  · exact mul_pos (Real.cosh_pos u) (Real.cosh_pos s)
  · dsimp [lorentz, perp]
    ring_nf
    simp only [Real.cosh_sq, Real.sin_sq]
    ring

theorem ray_onSheet (s θ : ℝ) : OnSheet (ray s θ) := by
  rw [← perp_zero s θ]
  exact perp_onSheet s θ 0

theorem mirror_onSheet {p : Vec} (hp : OnSheet p) : OnSheet (mirror p) := by
  constructor
  · exact hp.1
  · simpa [lorentz, mirror] using hp.2

/-- The perpendicular direction is a unit spatial tangent. -/
theorem inward_unit (θ : ℝ) : lorentz (inward θ) (inward θ) = -1 := by
  dsimp [lorentz, inward]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem radial_unit (s θ : ℝ) :
    lorentz (radialTangent s θ) (radialTangent s θ) = -1 := by
  dsimp [lorentz, radialTangent]
  ring_nf
  simp only [Real.cosh_sq, Real.sin_sq]
  ring

theorem perpendicular (s θ : ℝ) : lorentz (radialTangent s θ) (inward θ) = 0 := by
  dsimp [lorentz, radialTangent, inward]
  ring

theorem tangent_at_foot (s θ : ℝ) : lorentz (ray s θ) (inward θ) = 0 := by
  dsimp [lorentz, ray, inward]
  ring

/-- This identity will certify arclength in the hyperbolic metric. -/
theorem perp_lorentz (s θ u v : ℝ) :
    lorentz (perp s θ u) (perp s θ v) = Real.cosh (u - v) := by
  rw [Real.cosh_sub]
  dsimp [lorentz, perp]
  ring_nf
  simp only [Real.cosh_sq, Real.sin_sq]
  ring

/-- An intersection is reached along both inward perpendiculars by time q. -/
theorem exists_inward_intersection {s θ q : ℝ}
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hθ : 0 ≤ Real.sin θ)
    (hend : Real.cosh q * Real.sinh s * Real.sin θ ≤
      Real.sinh q * Real.cos θ) :
    ∃ u ∈ Set.Icc 0 q, mirror (perp s θ u) = perp s θ u := by
  let f : ℝ → ℝ := fun u =>
    Real.cosh u * Real.sinh s * Real.sin θ - Real.sinh u * Real.cos θ
  have hf : Continuous f :=
    ((Real.continuous_cosh.mul continuous_const).mul continuous_const).sub
      (Real.continuous_sinh.mul continuous_const)
  have hstart : 0 ≤ f 0 := by
    simpa [f] using mul_nonneg (Real.sinh_nonneg_iff.mpr hs) hθ
  have hfinish : f q ≤ 0 := sub_nonpos.mpr hend
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hq hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f q) (f 0) from ⟨hfinish, hstart⟩)
  refine ⟨u, hu, ?_⟩
  dsimp [mirror, perp]
  dsimp [f] at heq
  congr 2
  linarith

/-- Actual set intersection, proved from the constructed inward witness. -/
theorem intersect_of_endpoint {s θ q : ℝ}
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hθ : 0 ≤ Real.sin θ)
    (hend : Real.cosh q * Real.sinh s * Real.sin θ ≤
      Real.sinh q * Real.cos θ) :
    (upperSegment s θ q ∩ lowerSegment s θ q).Nonempty := by
  obtain ⟨u, hu, heq⟩ := exists_inward_intersection hs hq hθ hend
  have hu' : u ∈ Set.Icc (-q) q := ⟨by linarith [hu.1], hu.2⟩
  exact ⟨perp s θ u, ⟨u, hu', rfl⟩, u, hu', heq⟩

end Turning.Hyperboloid
