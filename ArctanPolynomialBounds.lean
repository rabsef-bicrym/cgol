import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Two elementary polynomial bounds for arctangent

The alternating cubic and quintic truncations are proved by monotonicity of
explicit derivative gaps. These are the only transcendental estimates used in
the first-large-sector octagonal phase proof.
-/

namespace ArctanPolynomialBounds

noncomputable section

open Real

/-- Gap between the quintic alternating upper polynomial and `arctan`. -/
def upperGap (x : ℝ) : ℝ :=
  x - x ^ 3 / 3 + x ^ 5 / 5 - Real.arctan x

/-- Gap between `arctan` and the cubic alternating lower polynomial. -/
def lowerGap (x : ℝ) : ℝ :=
  Real.arctan x - (x - x ^ 3 / 3)

lemma hasDerivAt_upperGap (x : ℝ) :
    HasDerivAt upperGap (x ^ 6 / (1 + x ^ 2)) x := by
  have hpoly : HasDerivAt
      (fun y : ℝ => y - y ^ 3 / 3 + y ^ 5 / 5)
      (1 - x ^ 2 + x ^ 4) x := by
    have h := ((hasDerivAt_id x).sub
      (((hasDerivAt_id x).pow 3).div_const 3)).add
      (((hasDerivAt_id x).pow 5).div_const 5)
    convert h using 1 <;> simp <;> ring
  have hraw := hpoly.sub (Real.hasDerivAt_arctan x)
  change HasDerivAt
    ((fun y : ℝ => y - y ^ 3 / 3 + y ^ 5 / 5) - Real.arctan)
    (x ^ 6 / (1 + x ^ 2)) x
  convert hraw using 1
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma hasDerivAt_lowerGap (x : ℝ) :
    HasDerivAt lowerGap (x ^ 4 / (1 + x ^ 2)) x := by
  have hpoly : HasDerivAt
      (fun y : ℝ => y - y ^ 3 / 3)
      (1 - x ^ 2) x := by
    have h := (hasDerivAt_id x).sub
      (((hasDerivAt_id x).pow 3).div_const 3)
    convert h using 1 <;> simp <;> ring
  have hraw := (Real.hasDerivAt_arctan x).sub hpoly
  change HasDerivAt
    (Real.arctan - (fun y : ℝ => y - y ^ 3 / 3))
    (x ^ 4 / (1 + x ^ 2)) x
  convert hraw using 1
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma differentiable_upperGap : Differentiable ℝ upperGap :=
  fun x => (hasDerivAt_upperGap x).differentiableAt

lemma differentiable_lowerGap : Differentiable ℝ lowerGap :=
  fun x => (hasDerivAt_lowerGap x).differentiableAt

lemma deriv_upperGap_nonneg (x : ℝ) : 0 ≤ deriv upperGap x := by
  rw [(hasDerivAt_upperGap x).deriv]
  positivity

lemma deriv_lowerGap_nonneg (x : ℝ) : 0 ≤ deriv lowerGap x := by
  rw [(hasDerivAt_lowerGap x).deriv]
  positivity

/-- Alternating quintic upper bound, valid for every nonnegative argument. -/
theorem arctan_le_quintic (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hgrow := mul_sub_le_image_sub_of_le_deriv differentiable_upperGap
    (C := 0) deriv_upperGap_nonneg (x := 0) (y := x) hx
  norm_num [upperGap] at hgrow ⊢
  linarith

/-- Alternating cubic lower bound, valid for every nonnegative argument. -/
theorem cubic_le_arctan (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hgrow := mul_sub_le_image_sub_of_le_deriv differentiable_lowerGap
    (C := 0) deriv_lowerGap_nonneg (x := 0) (y := x) hx
  norm_num [lowerGap] at hgrow ⊢
  linarith

end

end ArctanPolynomialBounds
