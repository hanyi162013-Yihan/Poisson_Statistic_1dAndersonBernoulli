import FixedCouplingPoisson.SpectralPoissonUnconditional

/-! Full-type guards for the final original spectral-process statements.
These annotations are checked when this module is actually compiled. -/

open FixedCouplingPoisson MeasureTheory Set Filter
open scoped Topology

#check (idsSpectralVagueLaw_tendsto_poissonVagueLaw_of_potentialLaw :
  (law : PotentialLaw) → ∀ {E : ℝ} {J : Set ℝ},
    J ∈ 𝓝 E → StrictMonoOn (idsCandidate law) J →
      Tendsto (idsSpectralVagueLaw law E) atTop (𝓝 poissonVagueLaw))

#check (linearSpectralVagueLaw_tendsto_poissonVagueLaw_of_potentialLaw :
  (law : PotentialLaw) → ∀ {E ρ : ℝ},
    HasDerivAt (idsCandidate law) ρ E → 0 < ρ →
      Tendsto (linearSpectralVagueLaw law E ρ) atTop (𝓝 poissonVagueLaw))

#check (idsSpectralCountingLaw_tendsto_poissonCountingLaw_of_potentialLaw :
  (law : PotentialLaw) → ∀ {E : ℝ} {J : Set ℝ},
    J ∈ 𝓝 E → StrictMonoOn (idsCandidate law) J →
      Tendsto (idsSpectralCountingLaw law E) atTop (𝓝 poissonCountingLaw))

#check (linearSpectralCountingLaw_tendsto_poissonCountingLaw_of_potentialLaw :
  (law : PotentialLaw) → ∀ {E ρ : ℝ},
    HasDerivAt (idsCandidate law) ρ E → 0 < ρ →
      Tendsto (linearSpectralCountingLaw law E ρ) atTop (𝓝 poissonCountingLaw))

#check (bernoulli_idsSpectralCountingLaw_tendsto_poissonCountingLaw_of_potentialLaw :
  (a b : ℝ) → (hab : a < b) → (p : unitInterval) →
    (hp0 : 0 < (p : ℝ)) → (hp1 : (p : ℝ) < 1) → (E : ℝ) →
      E ∈ interior (bernoulliClosedBands a b) →
        Tendsto (idsSpectralCountingLaw (bernoulliLaw a b hab p hp0 hp1) E)
          atTop (𝓝 poissonCountingLaw))
