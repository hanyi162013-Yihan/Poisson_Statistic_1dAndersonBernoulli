import FixedCouplingPoisson.PoissonCloudLaplace
import FixedCouplingPoisson.RealVagueSpace
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Instances.Nat

/-! The concrete locally finite cloud as an actual probability law on the Borel
space of the actual vague topology, with its proved Laplace functional. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter CompactlySupported
open scoped NNReal unitInterval Topology

def poissonCloudVagueMeasure (ω : PoissonCloud) : RealVagueMeasure :=
  ⟨poissonCloudMeasure ω, poissonCloudMeasure_isLocallyFiniteMeasure ω⟩

theorem poissonCloudVagueMeasure_testIntegral (ω : PoissonCloud) (f : C_c(ℝ, ℝ)) :
    RealVagueMeasure.testIntegral (poissonCloudVagueMeasure ω) f =
      ∫ x, f x ∂poissonCloudMeasure ω := rfl

theorem continuous_poissonCloudVagueMeasure : Continuous poissonCloudVagueMeasure := by
  apply RealVagueMeasure.continuous_iff_testIntegral.mpr
  intro f
  exact continuous_integral_poissonCloudMeasure f

def poissonVagueLaw : ProbabilityMeasure RealVagueMeasure :=
  poissonCloudLaw.map continuous_poissonCloudVagueMeasure.measurable.aemeasurable

theorem integral_poissonVagueLaw_laplace (f : C_c(ℝ, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ μ : RealVagueMeasure, Real.exp (-RealVagueMeasure.testIntegral μ f)
      ∂(poissonVagueLaw : Measure RealVagueMeasure)) =
        Real.exp (-(∫ x, 1 - Real.exp (-f x))) := by
  change (∫ μ : RealVagueMeasure, Real.exp (-RealVagueMeasure.testIntegral μ f)
    ∂(poissonCloudLaw : Measure PoissonCloud).map poissonCloudVagueMeasure) = _
  calc
    _ = ∫ ω : PoissonCloud,
        Real.exp (-RealVagueMeasure.testIntegral (poissonCloudVagueMeasure ω) f)
          ∂(poissonCloudLaw : Measure PoissonCloud) := by
      exact integral_map continuous_poissonCloudVagueMeasure.measurable.aemeasurable
        (((RealVagueMeasure.continuous_testIntegral f).neg).rexp).aestronglyMeasurable
    _ = _ := integral_poissonCloudLaplaceFunctional f hf0

theorem isTightMeasureSet_poissonVagueLaw :
    IsTightMeasureSet {(poissonVagueLaw : Measure RealVagueMeasure)} := by
  have h : IsTightMeasureSet {(poissonCloudLaw : Measure PoissonCloud)} :=
    isTightMeasureSet_singleton
  simpa only [Set.image_singleton, poissonVagueLaw, ProbabilityMeasure.toMeasure_map] using
    h.map continuous_poissonCloudVagueMeasure

end FixedCouplingPoisson
