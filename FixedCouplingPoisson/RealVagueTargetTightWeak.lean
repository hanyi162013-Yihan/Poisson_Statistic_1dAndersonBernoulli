import FixedCouplingPoisson.RealVagueLaplaceEmbedding
import FixedCouplingPoisson.SingletonTightEmbeddingWeak

/-! The compact-test Laplace criterion needs tightness only of the target law. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Filter Set
open scoped Topology CompactlySupported

/-- Actual Laplace expectation convergence for all nonnegative compact tests
implies ordinary vague-law weak convergence at every tight target law.
There is no source-family tightness premise. -/
theorem probabilityMeasure_tendsto_of_target_tight_of_laplace {ι : Type*} {F : Filter ι}
    (νs : ι → ProbabilityMeasure RealVagueMeasure) (ν : ProbabilityMeasure RealVagueMeasure)
    (htight : IsTightMeasureSet {(ν : Measure RealVagueMeasure)})
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ μ, laplaceTest f μ ∂(νs i : Measure RealVagueMeasure)) F
      (𝓝 (∫ μ, laplaceTest f μ ∂(ν : Measure RealVagueMeasure)))) :
    Tendsto νs F (𝓝 ν) :=
  probabilityMeasure_tendsto_of_target_tight_of_isEmbedding_compact
    laplaceCubeCoordinates isEmbedding_laplaceCubeCoordinates
    νs ν htight (laplaceCube_laws_tendsto_of_laplace νs ν hlaplace)

/-- The genuine pushforward-law form of the target-tight Laplace criterion. -/
theorem laws_tendsto_of_target_tight_of_laplace {Ω ι : Type*} [MeasurableSpace Ω]
    {F : Filter ι} (P : ProbabilityMeasure Ω) (Xs : ι → Ω → RealVagueMeasure)
    (hX : ∀ i, Measurable (Xs i)) (ν : ProbabilityMeasure RealVagueMeasure)
    (htight : IsTightMeasureSet {(ν : Measure RealVagueMeasure)})
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ ω, laplaceTest f (Xs i ω) ∂(P : Measure Ω)) F
      (𝓝 (∫ μ, laplaceTest f μ ∂(ν : Measure RealVagueMeasure)))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 ν) := by
  apply probabilityMeasure_tendsto_of_target_tight_of_laplace _ ν htight
  intro f hf
  have heq (i : ι) :
      (∫ μ, laplaceTest f μ ∂(P.map (hX i).aemeasurable : Measure RealVagueMeasure)) =
        ∫ ω, laplaceTest f (Xs i ω) ∂(P : Measure Ω) := by
    simpa only [laplaceBoundedTest_apply] using
      integral_probabilityMeasure_map P (hX i) (laplaceBoundedTest f hf)
  simpa only [heq] using hlaplace f hf

end FixedCouplingPoisson.RealVagueMeasure
