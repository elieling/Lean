import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Analytic helpers and the original equal-leg argument

The cosh and arctan helpers are reused by the construction in `LocalGrid.lean`.
The supplied figure clarifies the inward placement. Equal-leg auxiliary triangles
can then be chosen with leg length `x * epsilon n`, bounded by `legLength n`.
The conditional wrappers below are historical utilities.
`Turning.lem_turning_by_triangles` in `TurningTriangleProof.lean` now follows the
manuscript's contradiction and proves its geometric reduction. The alternative
`Turning.lem_turning` in `LocalGrid.lean` uses explicit perpendicular geodesics
directly. See `construction-notes.txt`.

All divisions in this file are in `ℝ`. The construction requires `1 ≤ n`.
-/

namespace Turning

noncomputable def epsilon (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) ^ 8)

noncomputable def legLength (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2 + 1) / (4 * (n : ℝ) ^ 8)

theorem legLength_eq (n : ℕ) :
    legLength n = ((n : ℝ) ^ 2 + 1) * epsilon n := by
  simp [legLength, epsilon, div_eq_mul_inv]

theorem legLength_pos {n : ℕ} (hn : 1 ≤ n) : 0 < legLength n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold legLength
  positivity

theorem legLength_le_half {n : ℕ} (hn : 1 ≤ n) : legLength n ≤ 1 / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 :=
    pow_le_pow_right₀ hn' (by norm_num)
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ 8 := one_le_pow₀ hn'
  unfold legLength
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ) ^ 8)).2
  linarith

/-- The power-series estimate, with its required domain condition. -/
theorem cosh_le_geometric_bound {t : ℝ} (ht : t ^ 2 / 2 < 1) :
    Real.cosh t ≤ 1 / (1 - t ^ 2 / 2) := by
  exact (Real.cosh_le_exp_half_sq t).trans
    (Real.exp_bound_div_one_sub_of_interval (by positivity) ht)

theorem cosh_le_eight_sevenths {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.cosh t ≤ 8 / 7 := by
  have hs : t ^ 2 / 2 ≤ (1 : ℝ) / 8 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht)]
  calc
    Real.cosh t ≤ 1 / (1 - t ^ 2 / 2) := cosh_le_geometric_bound (by linarith)
    _ ≤ 8 / 7 := (div_le_iff₀ (by linarith)).2 (by linarith)

/-- Cancellation in the equal-leg right-triangle formula needs positive length. -/
theorem tanh_div_sinh {t : ℝ} (ht : 0 < t) :
    Real.tanh t / Real.sinh t = 1 / Real.cosh t := by
  have hs : Real.sinh t ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr ht)
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hs]
  exact mul_comm _ _

/-- A positive argument strictly exceeds its inverse tangent. -/
theorem arctan_lt_self_of_pos {x : ℝ} (hx : 0 < x) : Real.arctan x < x := by
  have hpos : 0 < Real.arctan x := by
    simpa only [Real.arctan_zero] using Real.arctan_strictMono hx
  simpa only [Real.tan_arctan] using
    Real.lt_tan hpos (Real.arctan_lt_pi_div_two x)

/-- The tangent-subtraction identity, including the inverse-tangent branch. -/
theorem arctan_seven_eighths_eq :
    Real.arctan (7 / 8 : ℝ) = Real.pi / 4 - Real.arctan (1 / 15 : ℝ) := by
  have hadd := Real.arctan_add (x := (7 / 8 : ℝ)) (y := (1 / 15 : ℝ))
    (by norm_num)
  norm_num at hadd
  linarith

theorem two_pi_div_nine_lt_arctan_seven_eighths :
    2 * Real.pi / 9 < Real.arctan (7 / 8 : ℝ) := by
  rw [arctan_seven_eighths_eq]
  have hsmall := arctan_lt_self_of_pos (x := (1 / 15 : ℝ)) (by norm_num)
  linarith [Real.pi_gt_three]

/-- The lower bound proved by the corrected inequality chain in the excerpt. -/
theorem triangle_angle_gt {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    2 * Real.pi / 9 < Real.arctan (1 / Real.cosh t) := by
  have hc := cosh_le_eight_sevenths ht0 ht
  have hinv : (7 : ℝ) / 8 ≤ 1 / Real.cosh t :=
    (le_div_iff₀ (Real.cosh_pos t)).2 (by linarith)
  exact two_pi_div_nine_lt_arctan_seven_eighths.trans_le
    (Real.arctan_le_arctan hinv)

/-- The complete real-valued contradiction after the geometric reduction. -/
theorem numerical_contradiction {t α β β₁ β₂ : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 1 / 2)
    (hα : 11 * Real.pi / 15 ≤ α) (hβ : β = Real.pi - α)
    (hβ₁ : β₁ = Real.arctan (Real.tanh t / Real.sinh t))
    (hβ₂ : β₂ = Real.arctan (Real.tanh t / Real.sinh t))
    (hsep : β₁ + β₂ < β) : False := by
  rw [tanh_div_sinh ht0] at hβ₁ hβ₂
  have hangle := triangle_angle_gt ht0.le ht
  have hturn : β ≤ 4 * Real.pi / 15 := by linarith
  linarith [Real.pi_pos]

/--
Conditional intersection theorem for a single pair of segments, represented as
sets. `hgeometry` assumes an abstract equal-leg reduction at `legLength n`.
This historical wrapper is not used by either concrete local-grid proof.
No properties of hyperbolic geometry are inferred merely from the type `Point`.
-/
theorem intersection_of_geometric_reduction {Point : Type*}
    {L M : Set Point} {n : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα : 11 * Real.pi / 15 ≤ α)
    (hgeometry : ¬ (L ∩ M).Nonempty →
      ∃ β₁ β₂ : ℝ,
        β₁ = Real.arctan (Real.tanh (legLength n) / Real.sinh (legLength n)) ∧
        β₂ = Real.arctan (Real.tanh (legLength n) / Real.sinh (legLength n)) ∧
        β₁ + β₂ < Real.pi - α) :
    (L ∩ M).Nonempty := by
  by_contra hdisjoint
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hsep⟩ := hgeometry hdisjoint
  exact numerical_contradiction (legLength_pos hn) (legLength_le_half hn)
    hα rfl hβ₁ hβ₂ hsep

/--
The indexed conclusion for `x ∈ [n²+1]`, using the convention `[k] = {1,...,k}`.
The families `L` and `M` are abstract. This result is conditional on `hgeometry`;
use `Turning.lem_turning` for the explicit local-grid construction.
-/
theorem indexed_intersection_of_geometric_reduction {Point : Type*}
    {n : ℕ} {α : ℝ} (L M : ℕ → Set Point)
    (hn : 1 ≤ n) (hα : 11 * Real.pi / 15 ≤ α)
    (hgeometry : ∀ x ∈ Set.Icc 1 (n ^ 2 + 1),
      ¬ (L x ∩ M x).Nonempty →
      ∃ β₁ β₂ : ℝ,
        β₁ = Real.arctan (Real.tanh (legLength n) / Real.sinh (legLength n)) ∧
        β₂ = Real.arctan (Real.tanh (legLength n) / Real.sinh (legLength n)) ∧
        β₁ + β₂ < Real.pi - α) :
    ∀ x ∈ Set.Icc 1 (n ^ 2 + 1), (L x ∩ M x).Nonempty := by
  intro x hx
  exact intersection_of_geometric_reduction hn hα (hgeometry x hx)

end Turning
