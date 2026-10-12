import FixedCouplingPoisson.FurstenbergStationaryExistence
import FixedCouplingPoisson.FurstenbergNoAtoms
import FixedCouplingPoisson.StationaryUniqueness
import FixedCouplingPoisson.FurstenbergPositive

/-!
The original qualitative Furstenberg interface, instantiated for the actual
Schrodinger transfer law. Each field is supplied by the concrete stationary,
atomlessness, positivity, contraction, or coordinate-flip construction.

Verification is recorded by actual compilation and build receipts. This
construction introduces no extra hypothesis and changes no interface.
-/

noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory

/-- The concrete forward stationary probability and its coordinate-flipped
inverse stationary probability supply all original qualitative fields. -/
def provedFurstenbergQualitativeData (law : PotentialLaw) (E : ℝ) :
    QualitativeData law E := by
  let ν : ProbabilityMeasure ProjectivePoint :=
    Classical.choose (exists_forwardStationary law E)
  have hν : ForwardStationary law E ν :=
    Classical.choose_spec (exists_forwardStationary law E)
  have hpos : ∀ σ : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E σ → 0 < stationaryMean law E σ :=
    fun σ hσ => forwardStationary_stationaryMean_pos law E σ hσ
  have hunique : ∀ σ : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E σ → σ = ν := by
    intro σ hσ
    exact forwardStationary_unique_of_all_stationary_positive law E hpos σ ν hσ hν
  have hnull : ∀ p, (ν : Measure ProjectivePoint) {p} = 0 :=
    forwardStationary_null_singletons law E ν hν
  exact {
    forwardMeasure := ν
    inverseMeasure := flipDistribution ν
    forward_stationary := hν
    inverse_stationary := inverseStationary_flip law E ν hν
    forward_unique := hunique
    inverse_unique := inverseStationary_unique_of_forward law E ν hunique
    forward_null_singletons := hnull
    inverse_null_singletons := flipDistribution_null_singletons ν hnull
    stationary_mean_pos := hpos ν hν
    inverse_stationary_mean_pos := by
      rw [inverseStationaryMean_flip]
      exact hpos ν hν
  }

/-- The original `Input` is constructed for every energy from the actual
SL2 transfer law, with no supplied Furstenberg assumption. -/
def provedFurstenbergInput (law : PotentialLaw) : Input law where
  atEnergy E := provedFurstenbergQualitativeData law E

end FixedCouplingPoisson.Furstenberg
