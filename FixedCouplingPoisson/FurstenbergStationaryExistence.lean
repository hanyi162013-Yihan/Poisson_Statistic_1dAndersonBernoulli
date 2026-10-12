import FixedCouplingPoisson.ProjectiveCesaro
import FixedCouplingPoisson.ProjectiveFlip

/-! Actual stationary laws exist by compactness and the already proved
Cesaro telescope. No uniqueness, nonatomicity, positivity or Input is assumed.
The inverse law is the coordinate-exchange image of a forward stationary law.
This draft has not yet been compiled; checking is deferred by the user. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology

theorem exists_forwardStationary (law : PotentialLaw) (E : ℝ) :
    ∃ ν : ProbabilityMeasure ProjectivePoint, ForwardStationary law E ν := by
  let ν₀ : ProbabilityMeasure ProjectivePoint := ⟨Measure.dirac horizontalProjective, inferInstance⟩
  let μ : ℕ → ProbabilityMeasure ProjectivePoint := fun n => empiricalCesaro law E ν₀ n
  obtain ⟨ν, _, hν⟩ := (isCompact_univ :
    IsCompact (univ : Set (ProbabilityMeasure ProjectivePoint))).exists_mapClusterPt
      (show Filter.map μ atTop ≤ 𝓟 (univ : Set (ProbabilityMeasure ProjectivePoint)) from by simp)
  refine ⟨ν, forward_stationary_of_cluster_vanishing_defect law E μ ν hν ?_⟩
  intro f
  exact empiricalCesaro_test_defect_tendsto law E (fun _ => ν₀) f

theorem exists_inverseStationary (law : PotentialLaw) (E : ℝ) :
    ∃ ν : ProbabilityMeasure ProjectivePoint, InverseStationary law E ν := by
  obtain ⟨ν, hν⟩ := exists_forwardStationary law E
  exact ⟨flipDistribution ν, inverseStationary_flip law E ν hν⟩

theorem exists_forward_inverse_stationary (law : PotentialLaw) (E : ℝ) :
    ∃ ν : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E ν ∧ InverseStationary law E (flipDistribution ν) := by
  obtain ⟨ν, hν⟩ := exists_forwardStationary law E
  exact ⟨ν, hν, inverseStationary_flip law E ν hν⟩

end FixedCouplingPoisson.Furstenberg
