import FixedCouplingPoisson.GammaArrivals

/-! Laplace estimates for the actual exponential-sum laws, including the
tail in the number of arrivals that is needed to truncate renewal counts. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem exponentialSumLaw_ae_nonneg (k : ℕ) :
    ∀ᵐ x ∂(exponentialSumLaw k : Measure ℝ), 0 ≤ x := by
  rw [exponentialSumLaw_map]
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
  filter_upwards [exponentialProduct_ae_nonneg (Fin k)] with x hx
  exact Finset.sum_nonneg fun j _ => hx j

theorem integrable_exponentialSumLaw_laplace (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x : ℝ => Real.exp (-t * x)) (exponentialSumLaw k : Measure ℝ) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [exponentialSumLaw_ae_nonneg k] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  simpa only [neg_mul] using (neg_nonpos.mpr (mul_nonneg ht hx))

theorem integral_exponentialSumLaw_laplace (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, Real.exp (-t * x) ∂(exponentialSumLaw k : Measure ℝ)) =
      ((1 + t)⁻¹) ^ k := by
  classical
  rw [exponentialSumLaw_map, integral_map (by fun_prop)
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.exp (-t * x)) _)]
  have heq (x : Fin k → ℝ) :
      Real.exp (-t * (∑ j, x j)) = ∏ j, Real.exp (-t * x j) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [heq]
  change (∫ x : Fin k → ℝ, ∏ j, Real.exp (-t * x j)
    ∂Measure.pi (fun _ => (exponentialOne : Measure ℝ))) = _
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin k => (exponentialOne : Measure ℝ))
    (fun _ (x : ℝ) => Real.exp (-t * x))]
  simp_rw [integral_exponentialOne_laplace t ht]
  simp

theorem cdf_exponentialSumLaw_le_geometric (k : ℕ) (t : ℝ) :
    cdf (exponentialSumLaw k : Measure ℝ) t ≤ Real.exp t * ((1 / 2 : ℝ) ^ k) := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := (exponentialSumLaw k : Measure ℝ))
    (f := fun x : ℝ => Real.exp (-x))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (by simpa using integrable_exponentialSumLaw_laplace k 1 zero_le_one)
    (Real.exp (-t))
  have hs : {x : ℝ | Real.exp (-t) ≤ Real.exp (-x)} = Iic t := by
    ext x
    simp only [mem_setOf_eq, Real.exp_le_exp, neg_le_neg_iff, mem_Iic]
  rw [hs, ← cdf_eq_real] at h
  have hi : (∫ x, Real.exp (-x) ∂(exponentialSumLaw k : Measure ℝ)) =
      (1 / 2 : ℝ) ^ k := by
    simpa only [neg_mul, one_mul, show (1 : ℝ) + 1 = 2 by norm_num, one_div] using
      integral_exponentialSumLaw_laplace k 1 zero_le_one
  rw [hi] at h
  have hpos := Real.exp_pos t
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h' := mul_le_mul_of_nonneg_left h hpos.le
  simpa only [← mul_assoc, hexp, one_mul] using h'

theorem tendsto_cdf_exponentialSumLaw_atTop_zero (t : ℝ) :
    Tendsto (fun k : ℕ => cdf (exponentialSumLaw k : Measure ℝ) t) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : Tendsto (fun k : ℕ => Real.exp t * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  exact squeeze_zero (fun k => cdf_nonneg _ _) (fun k => cdf_exponentialSumLaw_le_geometric k t)
    hbound

end FixedCouplingPoisson
