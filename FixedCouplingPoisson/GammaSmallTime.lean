import FixedCouplingPoisson.GammaIntegerCDF
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem one_sub_exp_neg_le_self (t : ℝ) : 1 - Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

theorem cdf_exponentialSumLaw_one_error_le_half_sq (t : ℝ) (ht : 0 ≤ t) :
    |cdf (exponentialSumLaw 1 : Measure ℝ) t - t| ≤ t ^ 2 / 2 := by
  have hf : Continuous (fun x : ℝ => 1 - Real.exp (-x)) := by fun_prop
  have hi : (∫ x in 0..t, 1 - Real.exp (-x)) = t + Real.exp (-t) - 1 := by
    have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y + Real.exp (-y))
        (1 - Real.exp (-x)) x := by
      convert (hasDerivAt_id x).add ((hasDerivAt_id x).neg.exp) using 1 <;> try rfl
      simp only [Pi.neg_apply, id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hf.intervalIntegrable 0 t)]
    simp
  have hbound := intervalIntegral.integral_mono_on (μ := volume) ht (hf.intervalIntegrable 0 t)
    (continuous_id.intervalIntegrable 0 t) (fun x _ => one_sub_exp_neg_le_self x)
  simp only [id_eq] at hbound
  rw [hi, integral_id] at hbound
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hbound
  rw [cdf_exponentialSumLaw_one t ht,
    abs_of_nonpos (sub_nonpos.mpr (one_sub_exp_neg_le_self t))]
  linarith

theorem cdf_exponentialSumLaw_two_le_half_sq (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw 2 : Measure ℝ) t ≤ t ^ 2 / 2 := by
  have hf : Continuous (fun x : ℝ => x * Real.exp (-x)) := by fun_prop
  have hi : (∫ x in 0..t, x * Real.exp (-x)) =
      1 - Real.exp (-t) * (1 + t) := by
    have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -(y + 1) * Real.exp (-y))
        (x * Real.exp (-x)) x := by
      convert (((hasDerivAt_id x).add_const 1).neg.mul ((hasDerivAt_id x).neg.exp)) using 1 <;> try rfl
      simp only [Pi.neg_apply, id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hf.intervalIntegrable 0 t)]
    simp only [zero_add, neg_zero, Real.exp_zero, mul_one]
    ring
  have hbound := intervalIntegral.integral_mono_on (μ := volume) ht (hf.intervalIntegrable 0 t)
    (continuous_id.intervalIntegrable 0 t) (fun x hx =>
      mul_le_of_le_one_right hx.1 (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.1)))
  simp only [id_eq] at hbound
  rw [hi, integral_id] at hbound
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    cdf_exponentialSumLaw_two t ht] using hbound

end FixedCouplingPoisson
