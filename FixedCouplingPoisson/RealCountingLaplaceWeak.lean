import FixedCouplingPoisson.RealCountingWeak
import FixedCouplingPoisson.RealVagueTargetTightWeak

/-! The full compact-test Laplace criterion in the exact counting-measure space. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter
open scoped Topology CompactlySupported BoundedContinuousFunction

/-- All genuine compact-test Laplace expectations tending to the actual Poisson
target imply ordinary weak convergence of the exact counting-space laws.
Every target tightness premise is discharged; no common source tightness is assumed. -/
theorem probabilityMeasure_tendsto_poissonCountingLaw_of_laplace
    {ι : Type*} {F : Filter ι} (μs : ι → ProbabilityMeasure RealCountingMeasure)
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ μ, RealVagueMeasure.laplaceTest f (RealCountingMeasure.toVague μ)
        ∂(μs i : Measure RealCountingMeasure)) F
      (𝓝 (∫ μ, RealVagueMeasure.laplaceTest f μ
        ∂(poissonVagueLaw : Measure RealVagueMeasure)))) :
    Tendsto μs F (𝓝 poissonCountingLaw) := by
  apply probabilityMeasure_tendsto_poissonCountingLaw_of_vague_tendsto μs
  apply RealVagueMeasure.probabilityMeasure_tendsto_of_target_tight_of_laplace
    _ poissonVagueLaw isTightMeasureSet_poissonVagueLaw
  intro f hf
  have heq (ν : ProbabilityMeasure RealCountingMeasure) :
      (∫ μ, RealVagueMeasure.laplaceTest f μ
        ∂(ν.map RealCountingMeasure.measurable_toVague.aemeasurable : Measure RealVagueMeasure)) =
        ∫ μ, RealVagueMeasure.laplaceTest f (RealCountingMeasure.toVague μ)
          ∂(ν : Measure RealCountingMeasure) := by
    simpa only [RealVagueMeasure.laplaceBoundedTest_apply] using
      integral_probabilityMeasure_map ν RealCountingMeasure.measurable_toVague
        (RealVagueMeasure.laplaceBoundedTest f hf)
  simpa only [heq] using hlaplace f hf

/-- The corresponding genuine law theorem for actual counting-valued random variables. -/
theorem counting_laws_tendsto_poissonCountingLaw_of_laplace
    {Ω ι : Type*} [MeasurableSpace Ω] {F : Filter ι}
    (P : ProbabilityMeasure Ω) (Xs : ι → Ω → RealCountingMeasure)
    (hX : ∀ i, Measurable (Xs i))
    (hlaplace : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → Tendsto
      (fun i => ∫ ω, RealVagueMeasure.laplaceTest f (RealCountingMeasure.toVague (Xs i ω))
        ∂(P : Measure Ω)) F
      (𝓝 (∫ μ, RealVagueMeasure.laplaceTest f μ
        ∂(poissonVagueLaw : Measure RealVagueMeasure)))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 poissonCountingLaw) := by
  apply probabilityMeasure_tendsto_poissonCountingLaw_of_laplace
  intro f hf
  let G : RealCountingMeasure →ᵇ ℝ :=
    (RealVagueMeasure.laplaceBoundedTest f hf).compContinuous
      ⟨RealCountingMeasure.toVague, RealCountingMeasure.continuous_toVague⟩
  have heq (i : ι) :
      (∫ μ, RealVagueMeasure.laplaceTest f (RealCountingMeasure.toVague μ)
        ∂(P.map (hX i).aemeasurable : Measure RealCountingMeasure)) =
        ∫ ω, RealVagueMeasure.laplaceTest f (RealCountingMeasure.toVague (Xs i ω))
          ∂(P : Measure Ω) :=
    integral_probabilityMeasure_map P (hX i) G
  simpa only [heq] using hlaplace f hf

end FixedCouplingPoisson
