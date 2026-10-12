import FixedCouplingPoisson.GammaTails
import FixedCouplingPoisson.ScalarLaplaceIdentification

noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem gammaMeasure_ae_nonneg (a r : ℝ) :
    ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  apply (ae_withDensity_iff (measurable_gammaPDFReal a r).ennreal_ofReal).mpr
  exact ae_of_all _ fun x hx => le_of_not_gt fun hneg => hx (gammaPDF_of_neg hneg)

theorem integral_gammaMeasure_laplace (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ x, Real.exp (-t * x) ∂gammaMeasure a 1) = (1 / (1 + t)) ^ a := by
  rw [gammaMeasure]
  have hid := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure ℝ)) (f := gammaPDF a 1)
    (measurable_gammaPDFReal a 1).ennreal_ofReal
    (ae_of_all _ fun x => (show gammaPDF a 1 x < ⊤ from ENNReal.ofReal_lt_top))
    (fun x : ℝ => Real.exp (-t * x))
  rw [hid]
  have hfun : (fun x : ℝ => (gammaPDF a 1 x).toReal • Real.exp (-t * x)) =
      (Ici (0 : ℝ)).indicator
        (fun x => (Real.Gamma a)⁻¹ * (x ^ (a - 1) * Real.exp (-(1 + t) * x))) := by
    funext x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha zero_lt_one x)]
    simp only [gammaPDFReal, Real.one_rpow, one_div, one_mul, smul_eq_mul]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
      simp only [mul_assoc, ← Real.exp_add]
      congr 3 <;> ring
    · simp only [if_neg hx, zero_mul,
        indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]
  simp only [neg_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by linarith : 0 < 1 + t)]
  have hΓ : Real.Gamma a ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos ha)
  field_simp [hΓ] <;> ring

def gammaArrivalLaw (k : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gammaMeasure (k + 1 : ℕ) 1,
    isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one⟩

theorem exponentialSumLaw_succ_eq_gammaArrivalLaw (k : ℕ) :
    exponentialSumLaw (k + 1) = gammaArrivalLaw k := by
  apply probabilityMeasure_eq_of_nonnegative_integer_laplace
    (exponentialSumLaw (k + 1)) (gammaArrivalLaw k)
    (exponentialSumLaw_ae_nonneg (k + 1)) (gammaMeasure_ae_nonneg (k + 1 : ℕ) 1)
  intro m
  rw [integral_exponentialSumLaw_laplace _ _ (Nat.cast_nonneg _)]
  change _ = ∫ x, Real.exp (-(m : ℝ) * x) ∂gammaMeasure (k + 1 : ℕ) 1
  rw [integral_gammaMeasure_laplace _ _ (by positivity) (Nat.cast_nonneg _)]
  simp only [Real.rpow_natCast, one_div]

end FixedCouplingPoisson
