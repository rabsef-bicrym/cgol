import SmallGapReserveStandalone
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Monotonicity of the exact small-sector phase defect

This closes the soundness gap in the interval verifier's endpoint evaluation.
On the normalized interval `0 ≤ u ≤ 1/4`, the exact phase defect is antitone,
so its minimum on a box is attained at the box's right endpoint.
-/

namespace SmallSectorMonotonicityStandalone

noncomputable section

open Real Set
open OctagonBase
open SmallGapReserveStandalone

def rawDeriv (u : ℝ) : ℝ :=
  -phaseSlope + d *
    (Real.pi * Real.cos (Real.pi * u) *
        (Real.cos (Real.pi * u) + Real.sin (Real.pi * u)) +
      Real.sin (Real.pi * u) *
        (-Real.pi * Real.sin (Real.pi * u) +
          Real.pi * Real.cos (Real.pi * u)))

def compactDeriv (u : ℝ) : ℝ :=
  -phaseSlope + d * Real.pi *
    (Real.cos (2 * Real.pi * u) + Real.sin (2 * Real.pi * u))

lemma hasDerivAt_smallPhaseDefect (u : ℝ) :
    HasDerivAt smallPhaseDefect (rawDeriv u) u := by
  have hg : HasDerivAt (fun x : ℝ => Real.pi * x) Real.pi u := by
    simpa using (hasDerivAt_id u).const_mul Real.pi
  have hs := (Real.hasDerivAt_sin (Real.pi * u)).comp u hg
  have hc := (Real.hasDerivAt_cos (Real.pi * u)).comp u hg
  have hlinear := (hasDerivAt_const u cap).sub
    ((hasDerivAt_id u).const_mul phaseSlope)
  have hprod := hs.mul (hc.add hs)
  have hraw := hlinear.add (hprod.const_mul d)
  convert hraw using 1 <;> dsimp [smallPhaseDefect, rawDeriv] <;> ring

lemma rawDeriv_eq_compact (u : ℝ) : rawDeriv u = compactDeriv u := by
  dsimp [rawDeriv, compactDeriv]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  ring

lemma sin_add_cos_le_s (y : ℝ) :
    Real.sin y + Real.cos y ≤ s := by
  by_cases hnonneg : 0 ≤ Real.sin y + Real.cos y
  · have htrig := Real.sin_sq_add_cos_sq y
    have hdiff := sq_nonneg (Real.sin y - Real.cos y)
    have hsq : (Real.sin y + Real.cos y) ^ 2 ≤ 2 := by
      nlinarith
    nlinarith [s_sq, s_nonneg]
  · nlinarith [s_nonneg]

lemma d_mul_s : d * s = c := by
  dsimp [d, c]
  nlinarith [s_sq]

lemma compactDeriv_nonpos (u : ℝ) : compactDeriv u ≤ 0 := by
  have hsum := sin_add_cos_le_s (2 * Real.pi * u)
  have hfactor : 0 ≤ d * Real.pi := mul_nonneg d_nonneg Real.pi_pos.le
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hcpi := mul_le_mul_of_nonneg_left hpi c_nonneg
  have hslope : phaseSlope = 4 * c := rfl
  have hrewrite : d * Real.pi * s = c * Real.pi := by
    rw [mul_assoc, d_mul_s]
  rw [hrewrite] at hmul
  dsimp [compactDeriv]
  rw [hslope]
  nlinarith

lemma deriv_smallPhaseDefect_nonpos (u : ℝ) :
    deriv smallPhaseDefect u ≤ 0 := by
  rw [(hasDerivAt_smallPhaseDefect u).deriv, rawDeriv_eq_compact]
  exact compactDeriv_nonpos u

/-- The exact small-sector phase defect is antitone on `[0,1/4]`. -/
theorem smallPhaseDefect_antitone :
    AntitoneOn smallPhaseDefect (Set.Icc 0 ((1 : ℝ) / 4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 ((1 : ℝ) / 4))
  · fun_prop
  · intro x hx
    exact deriv_smallPhaseDefect_nonpos x

/-- Box-minimum form used by the interval verifier. -/
theorem right_endpoint_lower
    (a b u : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ u) (hub : u ≤ b) (hb : b ≤ (1 : ℝ) / 4) :
    smallPhaseDefect b ≤ smallPhaseDefect u := by
  exact smallPhaseDefect_antitone ⟨hab, hub⟩ ⟨ha, hb⟩ hub

end

end SmallSectorMonotonicityStandalone
