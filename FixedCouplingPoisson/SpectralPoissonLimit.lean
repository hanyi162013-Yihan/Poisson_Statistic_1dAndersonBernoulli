import FixedCouplingPoisson.ActualSpectralLaplace
import FixedCouplingPoisson.RealVagueTargetTightWeak
import FixedCouplingPoisson.SpectralCountingModel
import FixedCouplingPoisson.RealCountingWeak
import FixedCouplingPoisson.BernoulliBulk

/-! The original normalized spectral point processes converge in distribution
for the genuine vague topology. Only the declared qualitative Furstenberg
input remains external; no Poisson, stopping, tightness, or spectral interface
is assumed. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter Furstenberg
open scoped Topology CompactlySupported

/-- IDS unfolding at a locally strictly increasing center, with no derivative
assumption. This is ordinary weak convergence of the original vague laws. -/
theorem idsSpectralVagueLaw_tendsto_poissonVagueLaw
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J) :
    Tendsto (idsSpectralVagueLaw law E) atTop (𝓝 poissonVagueLaw) :=
  RealVagueMeasure.laws_tendsto_of_target_tight_of_laplace
    (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (idsSpectralVagueProcess law E) (measurable_idsSpectralVagueProcess law E)
    poissonVagueLaw isTightMeasureSet_poissonVagueLaw
    (fun f hf => idsSpectralVagueProcess_laplace_tendsto law input hJ hstrict f hf)

/-- Linear microscopic scaling needs just a finite positive derivative at
the reference energy. -/
theorem linearSpectralVagueLaw_tendsto_poissonVagueLaw
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ) :
    Tendsto (linearSpectralVagueLaw law E ρ) atTop (𝓝 poissonVagueLaw) :=
  RealVagueMeasure.laws_tendsto_of_target_tight_of_laplace
    (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (linearSpectralVagueProcess E ρ) (measurable_linearSpectralVagueProcess E ρ)
    poissonVagueLaw isTightMeasureSet_poissonVagueLaw
    (fun f hf => linearSpectralVagueProcess_laplace_tendsto law input hderiv hρ f hf)

/-- The IDS result in the actual subspace of locally finite counting
measures, with its induced vague topology. -/
theorem idsSpectralCountingLaw_tendsto_poissonCountingLaw
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J) :
    Tendsto (idsSpectralCountingLaw law E) atTop (𝓝 poissonCountingLaw) := by
  apply probabilityMeasure_tendsto_poissonCountingLaw_of_vague_tendsto
  simpa only [idsSpectralCountingLaw_map_toVague] using
    idsSpectralVagueLaw_tendsto_poissonVagueLaw law input hJ hstrict

/-- The linear result in the actual counting-measure space. -/
theorem linearSpectralCountingLaw_tendsto_poissonCountingLaw
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ) :
    Tendsto (linearSpectralCountingLaw law E ρ) atTop (𝓝 poissonCountingLaw) := by
  apply probabilityMeasure_tendsto_poissonCountingLaw_of_vague_tendsto
  simpa only [linearSpectralCountingLaw_map_toVague] using
    linearSpectralVagueLaw_tendsto_poissonVagueLaw law input hderiv hρ

/-- All interior centers of the two closed Bernoulli bands satisfy the
IDS hypothesis by an actual proof, including a touching band edge. -/
theorem bernoulli_idsSpectralCountingLaw_tendsto_poissonCountingLaw
    (a b : ℝ) (hab : a < b) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (input : Input (bernoulliLaw a b hab p hp0 hp1)) (E : ℝ)
    (hE : E ∈ interior (bernoulliClosedBands a b)) :
    Tendsto (idsSpectralCountingLaw (bernoulliLaw a b hab p hp0 hp1) E)
      atTop (𝓝 poissonCountingLaw) := by
  obtain ⟨J, hJ, hstrict⟩ :=
    bernoulli_idsCandidate_strictMonoOn_nhds a b hab p hp0 hp1 E hE
  exact idsSpectralCountingLaw_tendsto_poissonCountingLaw _ input hJ hstrict

end FixedCouplingPoisson
