import ArctanPolynomialBounds
import FirstSectorAlgebra
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Complete scalar inequality for the first large octagonal sector

For `0 <= t <= 1`, the exact rational expression `firstLhs t` dominates
`(4 c / pi) * arctan t`.  The proof uses a quintic arctangent upper bound on
`[0,3/5]` and the complementary cubic bound on `[3/5,1]`.
-/

namespace FirstSectorScalar

noncomputable section

open Real
open OctagonBase
open ArctanPolynomialBounds
open FirstSectorAlgebra

/-- Exact coefficient in the phase baseline. -/
def exactK : ℝ := 4 * c / Real.pi

lemma exactK_nonneg : 0 ≤ exactK := by
  dsimp [exactK]
  positivity

lemma lowK_nonneg : 0 ≤ lowK := by
  dsimp [lowK]
  positivity

lemma highK_nonneg : 0 ≤ highK := by
  dsimp [highK]
  positivity

lemma exactK_le_lowK : exactK ≤ lowK := by
  have hpi : (157 : ℝ) / 50 ≤ Real.pi := by
    exact Real.pi_gt_d2.le
  apply (div_le_iff₀ Real.pi_pos).2
  dsimp [exactK, lowK]
  calc
    4 * c = (200 * c / 157) * ((157 : ℝ) / 50) := by ring
    _ ≤ (200 * c / 157) * Real.pi :=
      mul_le_mul_of_nonneg_left hpi (by positivity)

lemma highK_le_exactK : highK ≤ exactK := by
  have hpi : Real.pi ≤ (63 : ℝ) / 20 := by
    exact Real.pi_lt_d2.le
  apply (le_div_iff₀ Real.pi_pos).2
  dsimp [exactK, highK]
  calc
    (80 * c / 63) * Real.pi ≤
        (80 * c / 63) * ((63 : ℝ) / 20) :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    _ = 4 * c := by ring

lemma exactK_mul_pi_div_four : exactK * (Real.pi / 4) = c := by
  dsimp [exactK]
  field_simp [Real.pi_ne_zero]
  ring

lemma u_nonneg (t : ℝ) (ht1 : t ≤ 1) (htm : -1 < t) : 0 ≤ u t := by
  dsimp [u]
  exact div_nonneg (sub_nonneg.mpr ht1) (by linarith)

lemma u_le_quarter (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) : u t ≤ (1 : ℝ) / 4 := by
  have hden : 0 < 1 + t := by nlinarith
  dsimp [u]
  apply (div_le_iff₀ hden).2
  nlinarith

lemma cubic_u_nonneg (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ cubic (u t) := by
  have htm : -1 < t := by nlinarith
  have hu0 := u_nonneg t ht1 htm
  have huq := u_le_quarter t ht
  have hu1 : u t ≤ 1 := by nlinarith
  have hprod : u t * (1 - u t) ≥ 0 :=
    mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hu2 : (u t) ^ 2 ≤ u t := by nlinarith
  have hu3 : (u t) ^ 3 ≤ u t := by
    have hm := mul_le_mul_of_nonneg_left hu2 hu0
    simpa [pow_succ, mul_assoc] using hm
  dsimp [cubic]
  nlinarith

lemma arctan_complement
    (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    Real.arctan t = Real.pi / 4 - Real.arctan (u t) := by
  have ht0 : 0 ≤ t := by nlinarith
  have htm : -1 < t := by nlinarith
  have hu0 := u_nonneg t ht1 htm
  have huq := u_le_quarter t ht
  have htu : t * u t < 1 := by
    have hmul : t * u t ≤ 1 * ((1 : ℝ) / 4) :=
      mul_le_mul ht1 huq hu0 ht0
    nlinarith
  have hadd := Real.arctan_add htu
  have hfrac : (t + u t) / (1 - t * u t) = 1 := by
    have hden : 1 + t ≠ 0 := by nlinarith
    dsimp [u]
    field_simp [hden]
    ring
  rw [hfrac, Real.arctan_one] at hadd
  linarith

lemma low_scalar
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (3 : ℝ) / 5) :
    exactK * Real.arctan t ≤ firstLhs t := by
  have hatan0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht0
  have hquint := arctan_le_quintic t ht0
  calc
    exactK * Real.arctan t ≤ lowK * Real.arctan t :=
      mul_le_mul_of_nonneg_right exactK_le_lowK hatan0
    _ ≤ lowK * quintic t :=
      mul_le_mul_of_nonneg_left hquint lowK_nonneg
    _ ≤ firstLhs t := low_gap_nonneg t ht0 ht1

lemma high_scalar
    (t : ℝ) (ht : (3 : ℝ) / 5 ≤ t) (ht1 : t ≤ 1) :
    exactK * Real.arctan t ≤ firstLhs t := by
  have ht0 : 0 ≤ t := by nlinarith
  have htm : -1 < t := by nlinarith
  have hu0 := u_nonneg t ht1 htm
  have hcubic := cubic_le_arctan (u t) hu0
  have hcomp := arctan_complement t ht ht1
  have hR0 := cubic_u_nonneg t ht ht1
  have hkR := mul_le_mul_of_nonneg_right highK_le_exactK hR0
  have hupper :
      exactK * Real.arctan t ≤ c - exactK * cubic (u t) := by
    rw [hcomp]
    rw [mul_sub, exactK_mul_pi_div_four]
    have hm := mul_le_mul_of_nonneg_left hcubic exactK_nonneg
    linarith
  calc
    exactK * Real.arctan t ≤ c - exactK * cubic (u t) := hupper
    _ ≤ c - highK * cubic (u t) := by linarith
    _ ≤ firstLhs t := high_gap_nonneg t ht ht1

/-- Complete first-large-sector scalar inequality. -/
theorem first_sector_scalar
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    exactK * Real.arctan t ≤ firstLhs t := by
  by_cases h : t ≤ (3 : ℝ) / 5
  · exact low_scalar t ht0 h
  · exact high_scalar t (le_of_not_ge h) ht1

end

end FirstSectorScalar
