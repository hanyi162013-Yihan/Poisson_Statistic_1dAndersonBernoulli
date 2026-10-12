import FixedCouplingPoisson.GammaIdentification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Distributions.Poisson.Basic

noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped NNReal

def erlangSurvival (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * ∑ j ∈ Finset.range (k + 1), x ^ j / (j.factorial : ℝ)

theorem erlangSurvival_succ (k : ℕ) (x : ℝ) :
    erlangSurvival (k + 1) x = erlangSurvival k x +
      Real.exp (-x) * x ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  simp only [erlangSurvival, Finset.sum_range_succ, mul_add, mul_div_assoc]

theorem hasDerivAt_erlangSurvival (k : ℕ) (x : ℝ) :
    HasDerivAt (erlangSurvival k)
      (-Real.exp (-x) * x ^ k / (k.factorial : ℝ)) x := by
  induction k with
  | zero =>
      have hf : erlangSurvival 0 = fun y : ℝ => Real.exp (-y) := by
        funext y
        simp [erlangSurvival]
      rw [hf]
      simpa using (hasDerivAt_id x).neg.exp
  | succ k ih =>
      have hf : erlangSurvival (k + 1) = fun y => erlangSurvival k y +
          Real.exp (-y) * y ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        funext y
        exact erlangSurvival_succ k y
      rw [hf]
      convert ih.add
        (((hasDerivAt_id x).neg.exp.mul ((hasDerivAt_id x).pow (k + 1))).div_const
          ((k + 1).factorial : ℝ)) using 1 <;> try rfl
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq, mul_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      try simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have hkp : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hk, hkp]
      ring

theorem erlangSurvival_zero (k : ℕ) : erlangSurvival k 0 = 1 := by
  simp only [erlangSurvival, neg_zero, Real.exp_zero, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

theorem gammaArrivalLaw_density (k : ℕ) :
    gammaPDFReal (k + 1 : ℕ) 1 = (Ici (0 : ℝ)).indicator
      (fun x => x ^ k * Real.exp (-x) / (k.factorial : ℝ)) := by
  have hΓ : Real.Gamma (k + 1 : ℕ) = (k.factorial : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial k
  have hc : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
  funext x
  simp only [gammaPDFReal, hΓ, hc, Real.rpow_natCast, one_pow, one_mul]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    ring
  · rw [if_neg hx, indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]

theorem cdf_gammaArrivalLaw (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    cdf (gammaArrivalLaw k : Measure ℝ) t = 1 - erlangSurvival k t := by
  change cdf (gammaMeasure (k + 1 : ℕ) 1) t = _
  rw [cdf_gammaMeasure_eq_integral (by positivity) zero_lt_one, gammaArrivalLaw_density,
    integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hs : Ici (0 : ℝ) ∩ Iic t = Icc 0 t := by ext x; simp
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have hd (x : ℝ) : HasDerivAt (fun y => -erlangSurvival k y)
      (x ^ k * Real.exp (-x) / (k.factorial : ℝ)) x := by
    convert (hasDerivAt_erlangSurvival k x).neg using 1 <;> try rfl
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => x ^ k * Real.exp (-x) / (k.factorial : ℝ))
      volume 0 t from (by fun_prop : Continuous
        (fun x : ℝ => x ^ k * Real.exp (-x) / (k.factorial : ℝ))).intervalIntegrable 0 t)]
  rw [erlangSurvival_zero]
  ring

theorem cdf_exponentialSumLaw_succ (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw (k + 1) : Measure ℝ) t =
      1 - Real.exp (-t) * ∑ j ∈ Finset.range (k + 1), t ^ j / (j.factorial : ℝ) := by
  rw [exponentialSumLaw_succ_eq_gammaArrivalLaw, cdf_gammaArrivalLaw _ _ ht]
  rfl

theorem cdf_exponentialSumLaw_adjacent_diff (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw (k + 1) : Measure ℝ) t -
      cdf (exponentialSumLaw (k + 2) : Measure ℝ) t =
        Real.exp (-t) * t ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  rw [exponentialSumLaw_succ_eq_gammaArrivalLaw,
    show k + 2 = (k + 1) + 1 by omega, exponentialSumLaw_succ_eq_gammaArrivalLaw,
    cdf_gammaArrivalLaw _ _ ht, cdf_gammaArrivalLaw _ _ ht, erlangSurvival_succ]
  ring

theorem cdf_exponentialSumLaw_zero (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw 0 : Measure ℝ) t = 1 := by
  rw [cdf_eq_real, measureReal_def, exponentialSumLaw_map,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hs : (fun x : Fin 0 → ℝ => ∑ j, x j) ⁻¹' Iic t = univ := by
    ext x
    simp [ht]
  rw [hs, measure_univ, ENNReal.toReal_one]

/-- The difference between successive arrival CDFs is exactly the rate-one
Poisson probability of `k` arrivals by time `t`. -/
theorem exponentialSumLaw_cdf_difference (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw k : Measure ℝ) t -
      cdf (exponentialSumLaw (k + 1) : Measure ℝ) t =
        Real.exp (-t) * t ^ k / (k.factorial : ℝ) := by
  cases k with
  | zero =>
      rw [cdf_exponentialSumLaw_zero t ht, cdf_exponentialSumLaw_one t ht]
      simp
  | succ k => exact cdf_exponentialSumLaw_adjacent_diff k t ht

theorem exponentialSumLaw_cdf_difference_eq_poissonMeasure (k : ℕ) (t : ℝ≥0) :
    cdf (exponentialSumLaw k : Measure ℝ) t -
      cdf (exponentialSumLaw (k + 1) : Measure ℝ) t =
        (poissonMeasure t).real {k} := by
  rw [exponentialSumLaw_cdf_difference k t t.property, poissonMeasure_real_singleton]

theorem cdf_exponentialSumLaw_two (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw 2 : Measure ℝ) t =
      1 - Real.exp (-t) * (1 + t) := by
  simpa [Finset.sum_range_succ] using cdf_exponentialSumLaw_succ 1 t ht

end FixedCouplingPoisson
