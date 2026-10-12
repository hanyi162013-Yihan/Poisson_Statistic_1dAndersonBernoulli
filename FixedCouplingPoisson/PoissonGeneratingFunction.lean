import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! The actual Poisson probability generating function, proved from its
Mathlib probability mass formula and the exponential series. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The weighted exponential series for the actual Poisson masses. -/
theorem poissonPower_hasSum (a : ℝ≥0) (z : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(a : ℝ)) * (a : ℝ) ^ n /
      (n.factorial : ℝ) * z ^ n)
      (Real.exp ((a : ℝ) * (z - 1))) := by
  convert (NormedSpace.expSeries_div_hasSum_exp ((a : ℝ) * z)).mul_left
    (Real.exp (-(a : ℝ))) using 1 <;> try rfl
  · funext n
    rw [mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

/-- In fact the Poisson power is integrable for every real `z`. -/
theorem integrable_poissonPower (a : ℝ≥0) (z : ℝ) :
    Integrable (fun n : ℕ => z ^ n) (poissonMeasure a) := by
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_pow] using
    (poissonPower_hasSum a |z|).summable

/-- The probability generating function of the actual Mathlib Poisson law.
This holds for every real `z`, hence in particular for `0 ≤ z ≤ 1`. -/
theorem integral_poissonGeneratingFunction (a : ℝ≥0) (z : ℝ) :
    (∫ n : ℕ, z ^ n ∂poissonMeasure a) =
      Real.exp ((a : ℝ) * (z - 1)) := by
  rw [integral_poissonMeasure a]
  simpa only [smul_eq_mul] using (poissonPower_hasSum a z).tsum_eq

end FixedCouplingPoisson
