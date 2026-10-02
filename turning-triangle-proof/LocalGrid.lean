import CenteredTurning
import HyperbolicMetric
import HyperbolicAngles

/-!
# Local-grid turning lemma in mathlib's hyperbolic plane

`lGrid` and `mGrid` are actual sets of `UpperHalfPlane` points with its hyperbolic
metric. They are perpendicular geodesic segments of total length `2*n²*epsilon n`,
at offset `x*epsilon n` on the two forward rays of angle `pi-alpha`.

Two placements are covered: centered at the attachment point, or one-sided with
both perpendiculars directed inward. An outward-only placement is not asserted.
The angle and tangent identities are certified separately in HyperbolicAngles.
-/

namespace Turning

open Hyperboloid

/-- The parameter α is the actual interior angle in the hyperboloid model. -/
theorem grid_interior_angle {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    unitTangentAngle (-radialTangent 0 ((Real.pi - α) / 2))
      (radialTangent 0 (-((Real.pi - α) / 2))) = α := by
  rw [interior_angle (by linarith : 0 ≤ (Real.pi - α) / 2)
    (by linarith : (Real.pi - α) / 2 ≤ Real.pi / 2)]
  ring

theorem grid_turning_angle {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    unitTangentAngle (radialTangent 0 ((Real.pi - α) / 2))
      (radialTangent 0 (-((Real.pi - α) / 2))) = Real.pi - α := by
  rw [outgoing_angle (by linarith : 0 ≤ (Real.pi - α) / 2)
    (by linarith : (Real.pi - α) / 2 ≤ Real.pi / 2)]
  ring

inductive Placement
  | centered
  | inward

def startParameter : Placement → ℝ → ℝ
  | .centered, q => -q
  | .inward, _ => 0

def endParameter : Placement → ℝ → ℝ
  | .centered, q => q
  | .inward, q => 2 * q

def parameterInterval (p : Placement) (q : ℝ) : Set ℝ :=
  Set.Icc (startParameter p q) (endParameter p q)

theorem inward_subset_interval (p : Placement) {q : ℝ} (hq : 0 ≤ q) :
    Set.Icc 0 q ⊆ parameterInterval p q := by
  intro u hu
  cases p <;> constructor <;>
    dsimp [parameterInterval, startParameter, endParameter] <;> linarith [hu.1, hu.2]

noncomputable def upperLine (s θ u : ℝ) : UpperHalfPlane :=
  toUpper (perp s θ u) (perp_onSheet s θ u)

noncomputable def lowerLine (s θ u : ℝ) : UpperHalfPlane :=
  toUpper (mirror (perp s θ u)) (mirror_onSheet (perp_onSheet s θ u))

theorem upperLine_dist (s θ u v : ℝ) : dist (upperLine s θ u) (upperLine s θ v) = |u-v| :=
  dist_perp s θ u v

theorem lowerLine_dist (s θ u v : ℝ) : dist (lowerLine s θ u) (lowerLine s θ v) = |u-v| :=
  dist_mirror_perp s θ u v

theorem upperLine_length (p : Placement) (s θ : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    dist (upperLine s θ (startParameter p q)) (upperLine s θ (endParameter p q)) =
      2 * q := by
  rw [upperLine_dist]
  cases p <;> dsimp [startParameter, endParameter] <;>
    rw [abs_of_nonpos (by linarith)] <;> ring

theorem lowerLine_length (p : Placement) (s θ : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    dist (lowerLine s θ (startParameter p q)) (lowerLine s θ (endParameter p q)) =
      2 * q := by
  rw [lowerLine_dist]
  cases p <;> dsimp [startParameter, endParameter] <;>
    rw [abs_of_nonpos (by linarith)] <;> ring

noncomputable def origin : UpperHalfPlane := toUpper (ray 0 0) (ray_onSheet 0 0)

theorem upperLine_offset (s θ : ℝ) (hs : 0 ≤ s) :
    dist (upperLine s θ 0) origin = s := by
  have hfoot : upperLine s θ 0 = toUpper (ray s θ) (ray_onSheet s θ) := by
    unfold upperLine
    congr 1
    exact perp_zero s θ
  have horigin : origin = toUpper (ray 0 θ) (ray_onSheet 0 θ) := by
    unfold origin
    congr 1
    simp [ray]
  rw [hfoot, horigin, dist_ray, sub_zero, abs_of_nonneg hs]

theorem lowerLine_offset (s θ : ℝ) (hs : 0 ≤ s) :
    dist (lowerLine s θ 0) origin = s := by
  have hzero : origin = toUpper (mirror (ray 0 0))
      (mirror_onSheet (ray_onSheet 0 0)) := by
    unfold origin
    congr 1
    simp [ray, mirror]
  rw [hzero]
  change dist (toUpper (mirror (perp s θ 0)) _)
    (toUpper (mirror (ray 0 0)) _) = s
  rw [dist_mirror]
  exact upperLine_offset s θ hs

noncomputable def lGrid (p : Placement) (n : ℕ) (α : ℝ) (x : ℕ) : Set UpperHalfPlane :=
  upperLine (offset n x) ((Real.pi - α) / 2) '' parameterInterval p (halfWidth n)

noncomputable def mGrid (p : Placement) (n : ℕ) (α : ℝ) (x : ℕ) : Set UpperHalfPlane :=
  lowerLine (offset n x) ((Real.pi - α) / 2) '' parameterInterval p (halfWidth n)

/-- This proof has no assumed geometric-intersection or right-triangle lemma. -/
theorem local_grid_intersects (p : Placement) {n x : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi)
    (hx : x ≤ n ^ 2 + 1) : (lGrid p n α x ∩ mGrid p n α x).Nonempty := by
  obtain ⟨u, hu, heq⟩ := turning_inward_witness hn hα hαπ hx
  have hu' := inward_subset_interval p (halfWidth_pos hn).le hu
  refine ⟨upperLine (offset n x) ((Real.pi - α) / 2) u,
    ⟨u, hu', rfl⟩, u, hu', ?_⟩
  unfold lowerLine upperLine
  congr 1

/-- The stated indexed conclusion with the source construction's n ≥ 2. -/
theorem lem_turning (p : Placement) {n : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi) :
    ∀ x ∈ Set.Icc 1 (n ^ 2 + 1), (lGrid p n α x ∩ mGrid p n α x).Nonempty := by
  intro x hx
  exact local_grid_intersects p (Nat.le_trans (by norm_num) hn) hα hαπ hx.2

/-- The same theorem in every isometric copy of the local coordinate frame. -/
theorem lem_turning_isometric_copy (F : UpperHalfPlane ≃ᵢ UpperHalfPlane)
    (p : Placement) {n : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi) :
    ∀ x ∈ Set.Icc 1 (n ^ 2 + 1),
      (F '' lGrid p n α x ∩ F '' mGrid p n α x).Nonempty := by
  intro x hx
  obtain ⟨z, hzL, hzM⟩ := lem_turning p hn hα hαπ x hx
  exact ⟨F z, ⟨z, hzL, rfl⟩, z, hzM, rfl⟩

end Turning
