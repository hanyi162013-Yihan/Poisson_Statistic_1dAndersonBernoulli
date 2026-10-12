import FixedCouplingPoisson.RealVagueLaplaceCube
import FixedCouplingPoisson.TightEmbeddingWeak

/-! Genuine vague-law weak convergence from compact-test Laplace expectations.
Both the model family and the actual target law must belong to the tight
family. Model tightness, target tightness, and Laplace expectations remain
explicit application obligations, not new mathematical interfaces.
-/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Filter Set
open scoped Topology CompactlySupported

/-- Uniform tightness including the target and all actual nonnegative C_c
Laplace expectation limits imply ordinary weak convergence in the actual
vague topology. No Polish or law-identification assumption is used. -/
theorem probabilityMeasure_tendsto_of_tight_of_laplace {ι : Type*} {F : Filter ι}
    (νs : ι → ProbabilityMeasure RealVagueMeasure) (ν : ProbabilityMeasure RealVagueMeasure)
    (htight : IsTightMeasureSet (insert (ν : Measure RealVagueMeasure)
      (Set.range (fun i => (νs i : Measure RealVagueMeasure)))))
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ μ, laplaceTest f μ ∂(νs i : Measure RealVagueMeasure)) F
      (𝓝 (∫ μ, laplaceTest f μ ∂(ν : Measure RealVagueMeasure)))) :
    Tendsto νs F (𝓝 ν) :=
  probabilityMeasure_tendsto_of_tight_of_continuous_injective_map
    laplaceCubeCoordinates continuous_laplaceCubeCoordinates laplaceCubeCoordinates_injective
    νs ν htight (laplaceCube_laws_tendsto_of_laplace νs ν hlaplace)

/-- The corresponding genuine push-forward-law statement, written directly
with the compact-test expectations on the original sample space. -/
theorem laws_tendsto_of_tight_of_laplace {Ω ι : Type*} [MeasurableSpace Ω] {F : Filter ι}
    (P : ProbabilityMeasure Ω) (Xs : ι → Ω → RealVagueMeasure)
    (hX : ∀ i, Measurable (Xs i)) (ν : ProbabilityMeasure RealVagueMeasure)
    (htight : IsTightMeasureSet (insert (ν : Measure RealVagueMeasure)
      (Set.range (fun i =>
        (P.map (hX i).aemeasurable : Measure RealVagueMeasure)))))
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ ω, laplaceTest f (Xs i ω) ∂(P : Measure Ω)) F
      (𝓝 (∫ μ, laplaceTest f μ ∂(ν : Measure RealVagueMeasure)))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 ν) := by
  apply probabilityMeasure_tendsto_of_tight_of_laplace _ ν htight
  intro f hf
  have heq (i : ι) :
      (∫ μ, laplaceTest f μ ∂(P.map (hX i).aemeasurable : Measure RealVagueMeasure)) =
        ∫ ω, laplaceTest f (Xs i ω) ∂(P : Measure Ω) := by
    simpa only [laplaceBoundedTest_apply] using
      integral_probabilityMeasure_map P (hX i) (laplaceBoundedTest f hf)
  simpa only [heq] using hlaplace f hf

end FixedCouplingPoisson.RealVagueMeasure
