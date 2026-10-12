import FixedCouplingPoisson.ExponentialProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Exponential

/-! Actual finite sums of independent rate-one exponential variables.
The law is defined by pushing forward the actual product probability measure. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def exponentialSum (k : ℕ) (x : Fin k → ℝ) : ℝ := ∑ j, x j

def exponentialSumLaw (k : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (exponentialProduct (Fin k))
    (show Measurable (exponentialSum k) from by unfold exponentialSum; fun_prop).aemeasurable

theorem measurable_exponentialSum (k : ℕ) :
    Measurable (exponentialSum k) := by unfold exponentialSum; fun_prop

theorem continuous_exponentialSum (k : ℕ) :
    Continuous (exponentialSum k) := by unfold exponentialSum; fun_prop

theorem exponentialSumLaw_map (k : ℕ) :
    (exponentialSumLaw k : Measure ℝ) =
      (exponentialProduct (Fin k) : Measure (Fin k → ℝ)).map (fun x => ∑ j, x j) := rfl

theorem exponentialSumLaw_succ_map (k : ℕ) :
    (exponentialSumLaw (k + 1) : Measure ℝ) =
      ((exponentialOne : Measure ℝ).prod
        (exponentialProduct (Fin k) : Measure (Fin k → ℝ))).map
          (fun p : ℝ × (Fin k → ℝ) => p.1 + ∑ j, p.2 j) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have he := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => (exponentialOne : Measure ℝ)) 0
  rw [exponentialSumLaw_map]
  change (Measure.pi (fun _ : Fin (k + 1) => (exponentialOne : Measure ℝ))).map _ =
    ((exponentialOne : Measure ℝ).prod
      (Measure.pi (fun _ : Fin k => (exponentialOne : Measure ℝ)))).map _
  rw [← he.map_eq, Measure.map_map (by fun_prop) e.measurable]
  congr 1
  funext x
  simpa [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove, Fin.tail] using
    (Fin.sum_univ_succ (fun j : Fin (k + 1) => x j))

theorem exponentialSumLaw_succ_nullSingletonClass (k : ℕ) :
    NullSingletonClass (exponentialSumLaw (k + 1) : Measure ℝ) := by
  constructor
  intro t
  rw [exponentialSumLaw_succ_map,
    Measure.map_apply (by fun_prop) (measurableSet_singleton t),
    Measure.prod_apply_symm ((measurableSet_singleton t).preimage (by fun_prop))]
  have hsection (x : Fin k → ℝ) :
      (fun a : ℝ => (a, x)) ⁻¹'
        ((fun p : ℝ × (Fin k → ℝ) => p.1 + ∑ j, p.2 j) ⁻¹' {t}) =
      {t - ∑ j, x j} := by
    ext a
    simp only [mem_preimage, mem_singleton_iff]
    exact eq_sub_iff_add_eq.symm
  simp_rw [hsection, measure_singleton]
  simp

theorem continuous_cdf_of_nullSingletonClass (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] : Continuous (cdf μ) := by
  have hc : Continuous (fun t : ℝ => ∫ x in Iic t, (1 : ℝ) ∂μ) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have h := IntegrableOn.continuousOn_Iic_primitive_Iic
      (show IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (t + 1)) μ from
        (integrable_const (1 : ℝ)).restrict)
    exact h.continuousAt (Iic_mem_nhds (by linarith : t < t + 1))
  simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
    ← cdf_eq_real] using hc

theorem continuous_cdf_exponentialSumLaw_succ (k : ℕ) :
    Continuous (cdf (exponentialSumLaw (k + 1) : Measure ℝ)) := by
  letI := exponentialSumLaw_succ_nullSingletonClass k
  exact continuous_cdf_of_nullSingletonClass _

theorem exponentialSumLaw_one : exponentialSumLaw 1 = exponentialOne := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [exponentialSumLaw_map]
  change (Measure.pi (fun _ : Fin 1 => (exponentialOne : Measure ℝ))).map _ = _
  simpa using (measurePreserving_piUnique
    (fun _ : Fin 1 => (exponentialOne : Measure ℝ))).map_eq

theorem cdf_exponentialSumLaw_one (t : ℝ) (ht : 0 ≤ t) :
    cdf (exponentialSumLaw 1 : Measure ℝ) t = 1 - Real.exp (-t) := by
  rw [exponentialSumLaw_one]
  change cdf (expMeasure 1) t = _
  simp only [cdf_expMeasure_eq zero_lt_one t, if_pos ht, one_mul]

end FixedCouplingPoisson
