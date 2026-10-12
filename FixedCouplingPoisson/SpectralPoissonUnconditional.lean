import FixedCouplingPoisson.SpectralPoissonLimit
import FixedCouplingPoisson.FurstenbergInputProved

/-! Final original spectral process statements after proving the actual
qualitative SL2 input. Verification is recorded by actual compilation
and build receipts. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter Furstenberg
open scoped Topology CompactlySupported

theorem idsSpectralVagueLaw_tendsto_poissonVagueLaw_of_potentialLaw
    (law : PotentialLaw) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J) :
    Tendsto (idsSpectralVagueLaw law E) atTop (𝓝 poissonVagueLaw) :=
  idsSpectralVagueLaw_tendsto_poissonVagueLaw law
    (provedFurstenbergInput law) hJ hstrict

theorem linearSpectralVagueLaw_tendsto_poissonVagueLaw_of_potentialLaw
    (law : PotentialLaw) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ) :
    Tendsto (linearSpectralVagueLaw law E ρ) atTop (𝓝 poissonVagueLaw) :=
  linearSpectralVagueLaw_tendsto_poissonVagueLaw law
    (provedFurstenbergInput law) hderiv hρ

theorem idsSpectralCountingLaw_tendsto_poissonCountingLaw_of_potentialLaw
    (law : PotentialLaw) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J) :
    Tendsto (idsSpectralCountingLaw law E) atTop (𝓝 poissonCountingLaw) :=
  idsSpectralCountingLaw_tendsto_poissonCountingLaw law
    (provedFurstenbergInput law) hJ hstrict

theorem linearSpectralCountingLaw_tendsto_poissonCountingLaw_of_potentialLaw
    (law : PotentialLaw) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ) :
    Tendsto (linearSpectralCountingLaw law E ρ) atTop (𝓝 poissonCountingLaw) :=
  linearSpectralCountingLaw_tendsto_poissonCountingLaw law
    (provedFurstenbergInput law) hderiv hρ

theorem bernoulli_idsSpectralCountingLaw_tendsto_poissonCountingLaw_of_potentialLaw
    (a b : ℝ) (hab : a < b) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (E : ℝ)
    (hE : E ∈ interior (bernoulliClosedBands a b)) :
    Tendsto (idsSpectralCountingLaw (bernoulliLaw a b hab p hp0 hp1) E)
      atTop (𝓝 poissonCountingLaw) :=
  bernoulli_idsSpectralCountingLaw_tendsto_poissonCountingLaw a b hab p hp0 hp1
    (provedFurstenbergInput _) E hE

end FixedCouplingPoisson
