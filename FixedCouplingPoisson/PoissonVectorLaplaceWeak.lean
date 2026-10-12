import FixedCouplingPoisson.PoissonProduct
import FixedCouplingPoisson.WeakProbabilityTransfer

/-! Ordinary Poisson vector weak convergence supplies every nonnegative
real Laplace test, using an actual bounded continuous extension. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal

section
variable {d : Type*} [Fintype d]

def clippedVectorLaplace (t : d → ℝ) (x : d → ℝ) : ℝ :=
  Real.exp (-(∑ i, t i * max 0 (x i)))

theorem clippedVectorLaplace_bounds (t : d → ℝ) (ht : ∀ i, 0 ≤ t i) (x : d → ℝ) :
    0 ≤ clippedVectorLaplace t x ∧ clippedVectorLaplace t x ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => mul_nonneg (ht i) (le_max_left _ _))

def clippedVectorLaplaceBounded (t : d → ℝ) (ht : ∀ i, 0 ≤ t i) : (d → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨clippedVectorLaplace t, by
    unfold clippedVectorLaplace; fun_prop⟩ 1 (by
    intro x y
    have hx := clippedVectorLaplace_bounds t ht x
    have hy := clippedVectorLaplace_bounds t ht y
    change dist (clippedVectorLaplace t x) (clippedVectorLaplace t y) ≤ 1
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])

theorem clippedVectorLaplace_nat (t : d → ℝ) (x : d → ℕ) :
    clippedVectorLaplace t (fun i => (x i : ℝ)) = poissonMixedLaplaceTest t x := by
  simp only [clippedVectorLaplace, max_eq_right (Nat.cast_nonneg _), poissonMixedLaplaceTest]

theorem integral_clippedVectorLaplace_poissonRealProduct (w : d → ℝ≥0)
    (t : d → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∫ x, clippedVectorLaplaceBounded t ht x ∂(poissonRealProduct w : Measure (d → ℝ))) =
      Real.exp (-(∑ i, (w i : ℝ) * (1 - Real.exp (-t i)))) := by
  change (∫ x, clippedVectorLaplaceBounded t ht x ∂(poissonProduct w : Measure (d → ℕ)).map
    (fun x : d → ℕ => fun i => (x i : ℝ))) = _
  rw [integral_map
    (show Measurable (fun x : d → ℕ => fun i => (x i : ℝ)) from by fun_prop).aemeasurable
    (clippedVectorLaplaceBounded t ht).continuous.measurable.aestronglyMeasurable]
  change (∫ x, clippedVectorLaplace t (fun i => (x i : ℝ))
    ∂(poissonProduct w : Measure (d → ℕ))) = _
  simp_rw [clippedVectorLaplace_nat]
  exact integral_poissonProduct_mixedLaplace w t

/-- The same true bounded continuous test applies to every nonnegative
real-valued vector, including intrinsic interval masses. -/
theorem nonnegative_vector_laplace_tendsto_of_poissonRealLaw
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {F : Filter ι}
    (P : ProbabilityMeasure Ω) (Y : ι → Ω → d → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hpos : ∀ n ω i, 0 ≤ Y n ω i) (w : d → ℝ≥0)
    (hweak : Tendsto (fun n => P.map (hY n).aemeasurable) F (𝓝 (poissonRealProduct w)))
    (t : d → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ i, t i * Y n ω i)) ∂P) F
      (𝓝 (Real.exp (-(∑ i, (w i : ℝ) * (1 - Real.exp (-t i)))))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    (clippedVectorLaplaceBounded t ht)
  rw [integral_clippedVectorLaplace_poissonRealProduct w t ht] at h
  have heq (n : ι) :
      (∫ x, clippedVectorLaplaceBounded t ht x ∂(P.map (hY n).aemeasurable : Measure (d → ℝ))) =
        ∫ ω, Real.exp (-(∑ i, t i * Y n ω i)) ∂P := by
    rw [integral_probabilityMeasure_map P (hY n) (clippedVectorLaplaceBounded t ht)]
    apply integral_congr_ae
    filter_upwards with ω
    change clippedVectorLaplace t (Y n ω) = _
    simp only [clippedVectorLaplace, max_eq_right (hpos n ω _)]
  simpa only [heq] using h

theorem count_laplace_tendsto_of_poissonRealLaw {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} {F : Filter ι} (P : ProbabilityMeasure Ω)
    (Y : ι → Ω → d → ℕ) (hY : ∀ n, Measurable (Y n)) (w : d → ℝ≥0)
    (hweak : Tendsto (fun n => P.map
      ((show Measurable (fun x : d → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
        (hY n)).aemeasurable) F (𝓝 (poissonRealProduct w)))
    (t : d → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Tendsto (fun n => ∫ ω, poissonMixedLaplaceTest t (Y n ω) ∂P) F
      (𝓝 (Real.exp (-(∑ i, (w i : ℝ) * (1 - Real.exp (-t i)))))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    (clippedVectorLaplaceBounded t ht)
  rw [integral_clippedVectorLaplace_poissonRealProduct w t ht] at h
  have heq (n : ι) : (∫ x, clippedVectorLaplaceBounded t ht x ∂(P.map
      ((show Measurable (fun x : d → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
        (hY n)).aemeasurable : Measure (d → ℝ))) =
      ∫ ω, poissonMixedLaplaceTest t (Y n ω) ∂P := by
    rw [integral_probabilityMeasure_map P
      ((show Measurable (fun x : d → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
        (hY n)) (clippedVectorLaplaceBounded t ht)]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => clippedVectorLaplace_nat t (Y n ω)
  simpa only [heq] using h

end
end FixedCouplingPoisson
