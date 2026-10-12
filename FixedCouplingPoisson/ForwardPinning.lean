import FixedCouplingPoisson.PhaseMixing
import FixedCouplingPoisson.EnergyContinuity
import FixedCouplingPoisson.ProjectiveMetric
import FixedCouplingPoisson.ProjectivePinningTools

/-!
# Forward nonatomic pinning at a fixed projective anchor

The continuous anchor kernels use the actual Euclidean determinant distance.
Their integrals vanish by dominated convergence and the supplied qualitative
absence of atoms. No finite-time phase law is assumed to be atomless.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

/-- The actual iid product law is pinned away from every fixed cut in this precise sense. -/
theorem projectiveProcessDistribution_anchor_pinning (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (p β : ProjectivePoint) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      (projectiveProcessDistribution law E p n : Measure ProjectivePoint)
        {r | projectiveDistance r β ≤ δ} < ENNReal.ofReal ε :=
  exists_anchor_pinning_of_tendsto _ data.forwardMeasure
    (projectiveProcessDistribution_tendsto_forwardMeasure law E data p) β
    (data.forward_null_singletons β) ε hε

/-- Pinning expressed on the original iid sample space and the actual real lift. -/
theorem iid_canonicalPhase_anchor_pinning (law : PotentialLaw) (E θ : ℝ)
    (data : QualitativeData law E) (β : ProjectivePoint) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      iidMeasure law {ω | projectiveDistance
        (phaseProjective (canonicalPhaseProcess E θ n ω)) β ≤ δ} < ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hpin⟩ := projectiveProcessDistribution_anchor_pinning law E data
    (phaseProjective θ) β ε hε
  refine ⟨δ, hδ, hpin.mono fun n hn => ?_⟩
  change ((iidMeasure law).map (projectiveProcess E (phaseProjective θ) n))
    {p | projectiveDistance p β ≤ δ} < ENNReal.ofReal ε at hn
  rw [Measure.map_apply (projectiveProcess_measurable E (phaseProjective θ) n)
    (isClosed_le (continuous_projectiveDistance_right β) continuous_const).measurableSet] at hn
  have heq : {ω | projectiveDistance
      (phaseProjective (canonicalPhaseProcess E θ n ω)) β ≤ δ} =
      (projectiveProcess E (phaseProjective θ) n) ⁻¹' {p | projectiveDistance p β ≤ δ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [phaseProjective_canonicalPhaseProcess]
  rw [heq]
  exact hn

end FixedCouplingPoisson.Furstenberg
