import FixedCouplingPoisson.JointLaplaceWeak
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual product of rate-one exponential probability measures,
its nonnegative support and its mixed Laplace transforms. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem exponentialOne_ae_nonneg :
    ∀ᵐ x ∂(exponentialOne : Measure ℝ), 0 ≤ x := by
  change ∀ᵐ x ∂volume.withDensity (gammaPDF 1 1), 0 ≤ x
  apply (ae_withDensity_iff (measurable_gammaPDFReal 1 1).ennreal_ofReal).mpr
  exact ae_of_all _ fun x hx => le_of_not_gt fun hneg => hx (gammaPDF_of_neg hneg)

theorem integral_exponentialOne_laplace (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, Real.exp (-t * x) ∂(exponentialOne : Measure ℝ)) = (1 + t)⁻¹ := by
  change (∫ x, Real.exp (-t * x) ∂volume.withDensity (gammaPDF 1 1)) = _
  have hid := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure ℝ)) (f := gammaPDF 1 1)
    (measurable_gammaPDFReal 1 1).ennreal_ofReal
    (ae_of_all _ fun x => (show gammaPDF 1 1 x < ⊤ from ENNReal.ofReal_lt_top))
    (fun x : ℝ => Real.exp (-t * x))
  rw [hid]
  have hfun : (fun x : ℝ => (gammaPDF 1 1 x).toReal • Real.exp (-t * x)) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-(1 + t) * x)) := by
    funext x
    simp only [gammaPDF, gammaPDFReal, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one, one_mul, smul_eq_mul]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, ENNReal.toReal_ofReal (Real.exp_nonneg _),
        indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), ← Real.exp_add]
      congr 1
      ring
    · simp only [if_neg hx, ENNReal.ofReal_zero, ENNReal.toReal_zero, zero_mul,
        indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] using
    integral_exp_mul_Ioi (by linarith : -(1 + t) < 0) 0

section FiniteDimension
variable (d : Type*) [Fintype d]

/-- Its coordinates are independent by the actual finite product measure. -/
def exponentialProduct : ProbabilityMeasure (d → ℝ) :=
  ⟨Measure.pi (fun _ : d => (exponentialOne : Measure ℝ)), inferInstance⟩

theorem exponentialProduct_ae_nonneg :
    ∀ᵐ x ∂(exponentialProduct d : Measure (d → ℝ)), ∀ j, 0 ≤ x j := by
  change ∀ᵐ x ∂Measure.pi (fun _ : d => (exponentialOne : Measure ℝ)), ∀ j, 0 ≤ x j
  apply eventually_all.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : d => (exponentialOne : Measure ℝ)) (i := j)).eventually
      exponentialOne_ae_nonneg

theorem realMixedLaplaceTest_eq_prod (m : d → ℕ) (x : d → ℝ) :
    realMixedLaplaceTest m x = ∏ j, Real.exp (-(m j : ℝ) * x j) := by
  classical
  unfold realMixedLaplaceTest
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp only [neg_mul]

theorem integral_exponentialProduct_mixedLaplace (m : d → ℕ) :
    (∫ x, realMixedLaplaceTest m x ∂(exponentialProduct d : Measure (d → ℝ))) =
      ∏ j, (1 + (m j : ℝ))⁻¹ := by
  classical
  simp_rw [realMixedLaplaceTest_eq_prod]
  change (∫ x : d → ℝ, ∏ j, Real.exp (-(m j : ℝ) * x j)
    ∂Measure.pi (fun _ : d => (exponentialOne : Measure ℝ))) = _
  rw [integral_fintype_prod_eq_prod (μ := fun _ : d => (exponentialOne : Measure ℝ))
    (fun j (x : ℝ) => Real.exp (-(m j : ℝ) * x))]
  apply Finset.prod_congr rfl
  intro j hj
  exact integral_exponentialOne_laplace (m j : ℝ) (Nat.cast_nonneg _)

end FiniteDimension
end FixedCouplingPoisson
