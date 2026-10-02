import CenteredBounds
import Hyperboloid

/-!
# The centered local-grid construction

The convention is that the perpendicular segments have their midpoint at the
attachment point. The extended incoming ray and the outgoing ray enclose turning
angle π-α, so we put them at angles ±(π-α)/2 around the bisector.

Unlike the earlier conditional theorem, this construction has no `hgeometry`
hypothesis. Its intersection is proved from explicit geodesic coordinates.
-/

namespace Turning

noncomputable def offset (n x : ℕ) : ℝ := (x : ℝ) * epsilon n

theorem offset_nonneg (n x : ℕ) : 0 ≤ offset n x := by
  unfold offset epsilon
  positivity

theorem offset_le_legLength {n x : ℕ} (hx : x ≤ n ^ 2 + 1) :
    offset n x ≤ legLength n := by
  have hx' : (x : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by exact_mod_cast hx
  rw [legLength_eq]
  exact mul_le_mul_of_nonneg_right hx' (by unfold epsilon; positivity)

noncomputable def lGridCoordinates (n : ℕ) (α : ℝ) (x : ℕ) :
    Set Hyperboloid.Vec :=
  Hyperboloid.upperSegment (offset n x) ((Real.pi - α) / 2) (halfWidth n)

noncomputable def mGridCoordinates (n : ℕ) (α : ℝ) (x : ℕ) :
    Set Hyperboloid.Vec :=
  Hyperboloid.lowerSegment (offset n x) ((Real.pi - α) / 2) (halfWidth n)

/-- The intersection lies at most n²ε along each inward perpendicular. -/
theorem turning_inward_witness {n x : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi)
    (hx : x ≤ n ^ 2 + 1) :
    ∃ u ∈ Set.Icc 0 (halfWidth n),
      Hyperboloid.mirror (Hyperboloid.perp (offset n x) ((Real.pi - α) / 2) u) =
      Hyperboloid.perp (offset n x) ((Real.pi - α) / 2) u := by
  have hθ0 : 0 ≤ (Real.pi - α) / 2 := by linarith
  have hθ : (Real.pi - α) / 2 ≤ 2 * Real.pi / 15 := by linarith
  apply Hyperboloid.exists_inward_intersection
    (offset_nonneg n x) (halfWidth_pos hn).le
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  · exact centered_crossing_bound (offset_nonneg n x) (offset_le_legLength hx)
      (legLength_le_half hn) (by linarith [legLength_le_two_halfWidth hn]) hθ0 hθ

/-- The local-grid intersection, including the extra index x=0. -/
theorem centered_turning_coordinates {n x : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi)
    (hx : x ≤ n ^ 2 + 1) :
    (lGridCoordinates n α x ∩ mGridCoordinates n α x).Nonempty := by
  have hθ0 : 0 ≤ (Real.pi - α) / 2 := by linarith
  have hθ : (Real.pi - α) / 2 ≤ 2 * Real.pi / 15 := by linarith
  apply Hyperboloid.intersect_of_endpoint (offset_nonneg n x) (halfWidth_pos hn).le
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  · exact centered_crossing_bound (offset_nonneg n x) (offset_le_legLength hx)
      (legLength_le_half hn) (by linarith [legLength_le_two_halfWidth hn]) hθ0 hθ

theorem centered_turning_all_coordinates {n : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα : 11 * Real.pi / 15 ≤ α) (hαπ : α ≤ Real.pi) :
    ∀ x ∈ Set.Icc 1 (n ^ 2 + 1),
      (lGridCoordinates n α x ∩ mGridCoordinates n α x).Nonempty := by
  intro x hx
  exact centered_turning_coordinates hn hα hαπ hx.2

end Turning
