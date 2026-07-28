import FirstSectorScalar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonnegativity of the phase defect on `[pi/4, pi/2]`

This is the geometric wrapper around the scalar theorem.  Substituting
`t = tan beta` identifies the exact tangent-wedge excess with `firstLhs t`.
-/

namespace FirstSectorDefectStandalone

noncomputable section

open Real
open OctagonBase
open FirstSectorAlgebra
open FirstSectorScalar

lemma sin_beta_nonneg (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : 0 ≤ Real.sin beta := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hb0
    (by nlinarith [hbq, Real.pi_pos])

lemma cos_beta_pos (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : 0 < Real.cos beta := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [hb0, hbq, Real.pi_pos]

lemma sin_beta_le_cos_beta (beta : ℝ) (hb0 : 0 ≤ beta)
    (hbq : beta ≤ Real.pi / 4) : Real.sin beta ≤ Real.cos beta := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := beta) (y := Real.pi / 2 - beta)
    (by nlinarith [hb0, Real.pi_pos])
    (by nlinarith [hb0])
    (by nlinarith [hbq])
  simpa [Real.sin_pi_div_two_sub] using h

lemma first_angle_sin (beta : ℝ) :
    Real.sin (Real.pi / 4 + beta) =
      (s / 2) * (Real.cos beta + Real.sin beta) := by
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  dsimp [s]
  ring

lemma first_angle_cos (beta : ℝ) :
    Real.cos (Real.pi / 4 + beta) =
      (s / 2) * (Real.cos beta - Real.sin beta) := by
  rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  dsimp [s]
  ring

lemma first_sector_formula
    (beta : ℝ)
    (hcos : Real.cos beta ≠ 0)
    (hsum : Real.cos beta + Real.sin beta ≠ 0) :
    sectorMinimum (Real.pi / 4 + beta) beta =
      d + firstLhs (Real.tan beta) := by
  have htrig := Real.sin_sq_add_cos_sq beta
  dsimp [sectorMinimum, wedge, firstLhs]
  rw [first_angle_sin, first_angle_cos, Real.tan_eq_sin_div_cos]
  field_simp [hcos, hsum, s_pos.ne']
  ring_nf at htrig ⊢
  dsimp [c, d] at *
  rw [s_sq]
  nlinarith

lemma first_baseline_identity (beta : ℝ) :
    phaseSlope * ((Real.pi / 4 + beta) / Real.pi) - cap =
      d + exactK * beta := by
  have hsplit :
      (Real.pi / 4 + beta) / Real.pi =
        (1 : ℝ) / 4 + beta / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have hconst : phaseSlope / 4 - cap = d := by
    dsimp [phaseSlope, cap, c, d]
    nlinarith [s_sq]
  dsimp [exactK]
  rw [hsplit]
  field_simp [Real.pi_ne_zero]
  nlinarith

/-- Nonnegativity of the phase defect on the first large sector. -/
theorem first_sector_defect_nonneg
    (beta : ℝ) (hb0 : 0 ≤ beta) (hbq : beta ≤ Real.pi / 4) :
    0 ≤ sectorMinimum (Real.pi / 4 + beta) beta -
      (phaseSlope * ((Real.pi / 4 + beta) / Real.pi) - cap) := by
  have hcos := cos_beta_pos beta hb0 hbq
  have hsin := sin_beta_nonneg beta hb0 hbq
  have hsum : 0 < Real.cos beta + Real.sin beta := add_pos_of_pos_of_nonneg hcos hsin
  have ht0 : 0 ≤ Real.tan beta := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hsin hcos.le
  have ht1 : Real.tan beta ≤ 1 := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_le_one hcos).2 (sin_beta_le_cos_beta beta hb0 hbq)
  have hscalar := first_sector_scalar (Real.tan beta) ht0 ht1
  have hatan : Real.arctan (Real.tan beta) = beta := by
    apply Real.arctan_tan
    · nlinarith [hb0, Real.pi_pos]
    · nlinarith [hbq, Real.pi_pos]
  rw [hatan] at hscalar
  rw [first_sector_formula beta hcos.ne' hsum.ne', first_baseline_identity]
  linarith

end

end FirstSectorDefectStandalone
