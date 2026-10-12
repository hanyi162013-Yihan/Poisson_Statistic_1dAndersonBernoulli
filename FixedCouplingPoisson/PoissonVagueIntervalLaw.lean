import FixedCouplingPoisson.PoissonCloudVagueLaw
import FixedCouplingPoisson.PoissonCloudIntervalLaw
import FixedCouplingPoisson.RealVagueEvaluation
import FixedCouplingPoisson.RealCountingMeasure

/-! The interval-count characterization belongs to the constructed vague law
itself. Intrinsic interval evaluation is Borel measurable, and its pushforward
agrees with the already identified actual uniform-mark cloud counts. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

section FiniteDimension
variable {d : Type*} [Fintype d]

def poissonVagueIntervalVector (a b : d → ℝ) (μ : RealVagueMeasure) : d → ℝ :=
  fun j => (μ : Measure ℝ).real (Ioc (a j) (b j))

theorem measurable_poissonVagueIntervalVector (a b : d → ℝ) :
    Measurable (poissonVagueIntervalVector a b) := by
  apply measurable_pi_lambda
  intro j
  exact RealVagueMeasure.measurable_measureReal_Ioc (a j) (b j)

theorem poissonVagueIntervalCounts_law (a b : d → ℝ) (hab : ∀ j, a j ≤ b j)
    (hdisj : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    poissonVagueLaw.map (measurable_poissonVagueIntervalVector a b).aemeasurable =
      poissonRealProduct (fun j => ⟨b j - a j, sub_nonneg.mpr (hab j)⟩) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((poissonCloudLaw : Measure PoissonCloud).map poissonCloudVagueMeasure).map
    (poissonVagueIntervalVector a b) = _
  rw [Measure.map_map (measurable_poissonVagueIntervalVector a b)
    continuous_poissonCloudVagueMeasure.measurable]
  have he : poissonVagueIntervalVector a b ∘ poissonCloudVagueMeasure =
      (fun ω : PoissonCloud => fun j => (poissonCloudIntervalCount (a j) (b j) ω : ℝ)) := by
    funext ω j
    exact poissonCloudMeasure_real_Ioc_eq_nat_count (a j) (b j) ω
  rw [he]
  simpa only [ProbabilityMeasure.toMeasure_map] using
    congrArg ProbabilityMeasure.toMeasure (poissonCloudIntervalCounts_real_law a b hab hdisj)

theorem poissonCountingIntervalCounts_law (a b : d → ℝ) (hab : ∀ j, a j ≤ b j)
    (hdisj : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    poissonCountingLaw.map ((measurable_poissonVagueIntervalVector a b).comp
      RealCountingMeasure.measurable_toVague).aemeasurable =
      poissonRealProduct (fun j => ⟨b j - a j, sub_nonneg.mpr (hab j)⟩) := by
  apply ProbabilityMeasure.toMeasure_injective
  have h := congrArg ProbabilityMeasure.toMeasure (poissonVagueIntervalCounts_law a b hab hdisj)
  rw [← poissonCountingLaw_map_toVague] at h
  simp only [ProbabilityMeasure.toMeasure_map] at h
  rw [Measure.map_map (measurable_poissonVagueIntervalVector a b)
    RealCountingMeasure.measurable_toVague] at h
  exact h

end FiniteDimension
end FixedCouplingPoisson
