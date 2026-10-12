import FixedCouplingPoisson.JointLaplaceWeak
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-! The actual finite product Poisson probability measure and its joint
Laplace transform. This only identifies the target law. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open scoped NNReal

theorem poissonLaplace_hasSum (r : ℝ≥0) (t : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) *
      Real.exp (-t * (n : ℝ)))
      (Real.exp ((r : ℝ) * (Real.exp (-t) - 1))) := by
  convert (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp (-t))).mul_left
    (Real.exp (-(r : ℝ))) using 1 <;> try rfl
  · funext n
    rw [show Real.exp (-t * (n : ℝ)) = Real.exp (-t) ^ n by
      rw [mul_comm, Real.exp_nat_mul]]
    rw [mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

theorem integrable_poissonLaplace (r : ℝ≥0) (t : ℝ) :
    Integrable (fun n : ℕ => Real.exp (-t * (n : ℝ))) (poissonMeasure r) := by
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (poissonLaplace_hasSum r t).summable

theorem integral_poissonLaplace (r : ℝ≥0) (t : ℝ) :
    (∫ n : ℕ, Real.exp (-t * (n : ℝ)) ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (Real.exp (-t) - 1)) := by
  rw [integral_poissonMeasure r]
  simpa only [smul_eq_mul] using (poissonLaplace_hasSum r t).tsum_eq

section FiniteDimension
variable {d : Type*} [Fintype d]

def poissonProduct (w : d → ℝ≥0) : ProbabilityMeasure (d → ℕ) :=
  ⟨Measure.pi (fun j => poissonMeasure (w j)), inferInstance⟩

theorem poissonProduct_real_singleton (w : d → ℝ≥0) (x : d → ℕ) :
    (poissonProduct w : Measure (d → ℕ)).real {x} =
      ∏ j, Real.exp (-(w j : ℝ)) * (w j : ℝ) ^ x j / ((x j).factorial : ℝ) := by
  classical
  change (Measure.pi (fun j => poissonMeasure (w j))).real {x} = _
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [← measureReal_def, poissonMeasure_real_singleton]

def poissonMixedLaplaceTest (t : d → ℝ) (x : d → ℕ) : ℝ :=
  Real.exp (-(∑ j, t j * (x j : ℝ)))

theorem poissonMixedLaplaceTest_eq_prod (t : d → ℝ) (x : d → ℕ) :
    poissonMixedLaplaceTest t x = ∏ j, Real.exp (-t j * (x j : ℝ)) := by
  classical
  unfold poissonMixedLaplaceTest
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp only [neg_mul]

theorem integrable_poissonProduct_mixedLaplace (w : d → ℝ≥0) (t : d → ℝ) :
    Integrable (poissonMixedLaplaceTest t) (poissonProduct w : Measure (d → ℕ)) := by
  simp_rw [show poissonMixedLaplaceTest t =
    (fun x : d → ℕ => ∏ j, Real.exp (-t j * (x j : ℝ))) from
    funext (poissonMixedLaplaceTest_eq_prod t)]
  exact Integrable.fintype_prod (fun j => integrable_poissonLaplace (w j) (t j))

theorem integral_poissonProduct_mixedLaplace (w : d → ℝ≥0) (t : d → ℝ) :
    (∫ x, poissonMixedLaplaceTest t x ∂(poissonProduct w : Measure (d → ℕ))) =
      Real.exp (-(∑ j, (w j : ℝ) * (1 - Real.exp (-t j)))) := by
  classical
  simp_rw [poissonMixedLaplaceTest_eq_prod]
  change (∫ x : d → ℕ, ∏ j, Real.exp (-t j * (x j : ℝ))
    ∂Measure.pi (fun j => poissonMeasure (w j))) = _
  rw [integral_fintype_prod_eq_prod (μ := fun j => poissonMeasure (w j))
    (fun j (n : ℕ) => Real.exp (-t j * (n : ℝ)))]
  simp only [integral_poissonLaplace]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def poissonRealProduct (w : d → ℝ≥0) : ProbabilityMeasure (d → ℝ) :=
  (poissonProduct w).map
    (show Measurable (fun x : d → ℕ => fun j => (x j : ℝ)) from by fun_prop).aemeasurable

theorem poissonRealProduct_ae_nonneg (w : d → ℝ≥0) :
    ∀ᵐ x ∂(poissonRealProduct w : Measure (d → ℝ)), ∀ j, 0 ≤ x j := by
  change ∀ᵐ x ∂(poissonProduct w : Measure (d → ℕ)).map
    (fun x : d → ℕ => fun j => (x j : ℝ)), ∀ j, 0 ≤ x j
  apply (ae_map_iff
    (show Measurable (fun x : d → ℕ => fun j => (x j : ℝ)) from by fun_prop).aemeasurable
    (by measurability)).mpr
  exact ae_of_all _ fun x j => Nat.cast_nonneg (x j)

theorem integral_poissonRealProduct_integerLaplace (w : d → ℝ≥0) (m : d → ℕ) :
    (∫ x, realMixedLaplaceTest m x ∂(poissonRealProduct w : Measure (d → ℝ))) =
      Real.exp (-(∑ j, (w j : ℝ) * (1 - Real.exp (-(m j : ℝ))))) := by
  change (∫ x, realMixedLaplaceTest m x ∂(poissonProduct w : Measure (d → ℕ)).map
    (fun x : d → ℕ => fun j => (x j : ℝ))) = _
  rw [integral_map
    (show Measurable (fun x : d → ℕ => fun j => (x j : ℝ)) from by fun_prop).aemeasurable
    (show Continuous (realMixedLaplaceTest m) from by
      unfold realMixedLaplaceTest; fun_prop).aestronglyMeasurable]
  exact integral_poissonProduct_mixedLaplace w (fun j => (m j : ℝ))

/-- Identification of the joint count target from mixed integer Laplace limits. -/
theorem poissonReal_laws_tendsto_of_mixed_integer_laplace
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (P : ProbabilityMeasure Ω) (Y : ι → Ω → d → ℕ) (hY : ∀ i, Measurable (Y i))
    (w : d → ℝ≥0)
    (hlaplace : ∀ m : d → ℕ, Tendsto
      (fun i => ∫ ω, poissonMixedLaplaceTest (fun j => (m j : ℝ)) (Y i ω)
        ∂(P : Measure Ω)) F
      (𝓝 (Real.exp (-(∑ j, (w j : ℝ) * (1 - Real.exp (-(m j : ℝ)))))))) :
    Tendsto
      (fun i => P.map ((show Measurable (fun x : d → ℕ => fun j => (x j : ℝ))
        from by fun_prop).comp (hY i)).aemeasurable)
      F (𝓝 (poissonRealProduct w)) := by
  apply laws_tendsto_of_mixed_integer_laplace P
    (fun i ω j => (Y i ω j : ℝ))
    (fun i => (show Measurable (fun x : d → ℕ => fun j => (x j : ℝ))
      from by fun_prop).comp (hY i))
    (fun i ω j => Nat.cast_nonneg (Y i ω j))
    (poissonRealProduct w) (poissonRealProduct_ae_nonneg w)
  intro m
  rw [integral_poissonRealProduct_integerLaplace w m]
  exact hlaplace m

end FiniteDimension
end FixedCouplingPoisson
