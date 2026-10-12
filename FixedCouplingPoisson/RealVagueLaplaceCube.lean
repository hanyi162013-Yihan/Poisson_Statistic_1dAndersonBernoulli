import FixedCouplingPoisson.RealVagueLaplace
import FixedCouplingPoisson.GeneralCubeWeak

/-! Actual finite-support moments of the full Borel Laplace coordinate cube. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Filter
open scoped Topology CompactlySupported BigOperators

abbrev NonnegCompactTest := {f : C_c(ℝ, ℝ) // 0 ≤ f}

/-- All nonnegative compact Laplace tests in the genuine Borel unit product. -/
def laplaceCubeCoordinates (μ : RealVagueMeasure) : BorelMomentCube NonnegCompactTest :=
  fun f => ⟨laplaceTest f.val μ, laplaceTest_mem_Icc f.val f.property μ⟩

theorem continuous_laplaceCubeCoordinates : Continuous laplaceCubeCoordinates :=
  continuous_pi fun f => (continuous_laplaceTest f.val).subtype_mk
    (fun μ => laplaceTest_mem_Icc f.val f.property μ)

theorem laplaceCubeCoordinates_injective : Function.Injective laplaceCubeCoordinates := by
  intro μ ν h
  apply ext_of_nonneg_laplaceTest
  intro f hf
  exact congrArg Subtype.val (congrFun h (⟨f, hf⟩ : NonnegCompactTest))

/-- The actual compactly supported nonnegative test represented by a mixed moment. -/
def supportedCompactTest (m : NonnegCompactTest →₀ ℕ) : C_c(ℝ, ℝ) :=
  ∑ f ∈ m.support, (m f : ℝ) • f.val

theorem supportedCompactTest_nonneg (m : NonnegCompactTest →₀ ℕ) :
    0 ≤ supportedCompactTest m := by
  classical
  intro x
  simp only [supportedCompactTest, CompactlySupportedContinuousMap.sum_apply,
    CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun f _ => mul_nonneg (Nat.cast_nonneg _) (f.property x)

theorem testIntegral_supportedCompactTest (μ : RealVagueMeasure)
    (m : NonnegCompactTest →₀ ℕ) :
    testIntegral μ (supportedCompactTest m) =
      ∑ f ∈ m.support, (m f : ℝ) * testIntegral μ f.val := by
  classical
  let Λ := CompactlySupportedContinuousMap.integralPositiveLinearMap (μ : Measure ℝ)
  change Λ (∑ f ∈ m.support, (m f : ℝ) • f.val) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem supportedMonomial_laplaceCubeCoordinates
    (m : NonnegCompactTest →₀ ℕ) (μ : RealVagueMeasure) :
    supportedMonomial m (laplaceCubeCoordinates μ) = laplaceTest (supportedCompactTest m) μ := by
  classical
  change (∏ f ∈ m.support, Real.exp (-testIntegral μ f.val) ^ m f) = _
  calc
    _ = ∏ f ∈ m.support, Real.exp (-((m f : ℝ) * testIntegral μ f.val)) := by
      apply Finset.prod_congr rfl
      intro f hf
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (-(∑ f ∈ m.support, (m f : ℝ) * testIntegral μ f.val)) := by
      simpa only [Finset.sum_neg_distrib] using
        (Real.exp_sum m.support (fun f => -((m f : ℝ) * testIntegral μ f.val))).symm
    _ = _ := by rw [laplaceTest, testIntegral_supportedCompactTest]

theorem supportedMoment_laplaceCube_map
    (ν : ProbabilityMeasure RealVagueMeasure) (m : NonnegCompactTest →₀ ℕ) :
    supportedMoment (ν.map continuous_laplaceCubeCoordinates.measurable.aemeasurable) m =
      ∫ μ, laplaceTest (supportedCompactTest m) μ ∂(ν : Measure RealVagueMeasure) := by
  rw [supportedMoment, ProbabilityMeasure.toMeasure_map,
    integral_map continuous_laplaceCubeCoordinates.measurable.aemeasurable
      (continuous_supportedMonomial m).measurable.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun μ => supportedMonomial_laplaceCubeCoordinates m μ)

/-- Actual nonnegative compact-test Laplace expectation limits give genuine
weak convergence of the full compact coordinate laws. -/
theorem laplaceCube_laws_tendsto_of_laplace {ι : Type*} {F : Filter ι}
    (νs : ι → ProbabilityMeasure RealVagueMeasure) (ν : ProbabilityMeasure RealVagueMeasure)
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ μ, laplaceTest f μ ∂(νs i : Measure RealVagueMeasure)) F
      (𝓝 (∫ μ, laplaceTest f μ ∂(ν : Measure RealVagueMeasure)))) :
    Tendsto (fun i => (νs i).map continuous_laplaceCubeCoordinates.measurable.aemeasurable) F
      (𝓝 (ν.map continuous_laplaceCubeCoordinates.measurable.aemeasurable)) := by
  apply probabilityMeasure_tendsto_of_supportedMoments
  intro m
  simpa only [supportedMoment_laplaceCube_map] using
    hlaplace (supportedCompactTest m) (supportedCompactTest_nonneg m)

end FixedCouplingPoisson.RealVagueMeasure
