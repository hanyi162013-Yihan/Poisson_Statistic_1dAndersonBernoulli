import FixedCouplingPoisson.ActualNormalizedJoint
import FixedCouplingPoisson.IntervalToCompactLaplace
import FixedCouplingPoisson.PoissonVagueIntervalLaw

/-! Genuine compact-test Laplace limits for both original spectral models. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter Furstenberg
open scoped Topology CompactlySupported NNReal

theorem poissonVagueLaw_symmetricGrid_projection {R : ℝ} {m : ℕ}
    (hR : 0 < R) (hm : 0 < m) :
    poissonVagueLaw.map (measurable_symmetricGridMassVector R m).aemeasurable =
      poissonRealProduct (partitionPoissonRates (symmetricGrid R m) (2 * m)
        ((symmetricGrid_strictMono hR hm).strictMonoOn (Iic (2 * m)))) := by
  have hx := (symmetricGrid_strictMono hR hm).strictMonoOn (Iic (2 * m))
  have h := poissonVagueIntervalCounts_law
    (fun i : Fin (2 * m) => symmetricGrid R m i.val)
    (fun i => symmetricGrid R m (i.val + 1))
    (fun i => (symmetricGrid_strictMono hR hm (Nat.lt_succ_self i.val)).le)
    (adjacent_Ioc_pairwise_disjoint _ _ hx)
  exact h

theorem idsSpectralVagueLaw_symmetricGrid_projection_tendsto
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J)
    {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m) :
    Tendsto (fun n => (idsSpectralVagueLaw law E n).map
      (measurable_symmetricGridMassVector R m).aemeasurable) atTop
      (𝓝 (poissonVagueLaw.map (measurable_symmetricGridMassVector R m).aemeasurable)) := by
  rw [poissonVagueLaw_symmetricGrid_projection hR hm]
  exact idsSpectralVagueLaw_interval_projection_tendsto_poisson law input hJ hstrict
    (symmetricGrid R m) (2 * m) (by omega)
    ((symmetricGrid_strictMono hR hm).strictMonoOn (Iic (2 * m))) m (by omega)
    (symmetricGrid_endpoints R hm).2.1

theorem linearSpectralVagueLaw_symmetricGrid_projection_tendsto
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ)
    {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m) :
    Tendsto (fun n => (linearSpectralVagueLaw law E ρ n).map
      (measurable_symmetricGridMassVector R m).aemeasurable) atTop
      (𝓝 (poissonVagueLaw.map (measurable_symmetricGridMassVector R m).aemeasurable)) := by
  rw [poissonVagueLaw_symmetricGrid_projection hR hm]
  exact linearSpectralVagueLaw_interval_projection_tendsto_poisson law input hderiv hρ
    (symmetricGrid R m) (2 * m) (by omega)
    ((symmetricGrid_strictMono hR hm).strictMonoOn (Iic (2 * m))) m (by omega)
    (symmetricGrid_endpoints R hm).2.1

theorem idsSpectralVagueProcess_laplace_tendsto
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J)
    (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) :
    Tendsto (fun n => ∫ ω, RealVagueMeasure.laplaceTest f (idsSpectralVagueProcess law E n ω)
      ∂iidMeasure law) atTop
      (𝓝 (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(poissonVagueLaw : Measure RealVagueMeasure))) := by
  have h := compactTestLaplace_integral_tendsto_of_symmetricGrid_laws
    (idsSpectralVagueLaw law E) poissonVagueLaw
    (fun R hR m hm => idsSpectralVagueLaw_symmetricGrid_projection_tendsto
      law input hJ hstrict hR hm) f hf
  have heq (n : ℕ) :
      (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(idsSpectralVagueLaw law E n : Measure RealVagueMeasure)) =
      ∫ ω, RealVagueMeasure.laplaceTest f (idsSpectralVagueProcess law E n ω) ∂iidMeasure law := by
    simpa only [idsSpectralVagueLaw, RealVagueMeasure.laplaceBoundedTest_apply,
      ProbabilityMeasure.coe_mk] using integral_probabilityMeasure_map
      (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
      (measurable_idsSpectralVagueProcess law E n) (RealVagueMeasure.laplaceBoundedTest f hf)
  simpa only [heq] using h

theorem linearSpectralVagueProcess_laplace_tendsto
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ)
    (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) :
    Tendsto (fun n => ∫ ω, RealVagueMeasure.laplaceTest f (linearSpectralVagueProcess E ρ n ω)
      ∂iidMeasure law) atTop
      (𝓝 (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(poissonVagueLaw : Measure RealVagueMeasure))) := by
  have h := compactTestLaplace_integral_tendsto_of_symmetricGrid_laws
    (linearSpectralVagueLaw law E ρ) poissonVagueLaw
    (fun R hR m hm => linearSpectralVagueLaw_symmetricGrid_projection_tendsto
      law input hderiv hρ hR hm) f hf
  have heq (n : ℕ) :
      (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(linearSpectralVagueLaw law E ρ n : Measure RealVagueMeasure)) =
      ∫ ω, RealVagueMeasure.laplaceTest f (linearSpectralVagueProcess E ρ n ω) ∂iidMeasure law := by
    simpa only [linearSpectralVagueLaw, RealVagueMeasure.laplaceBoundedTest_apply,
      ProbabilityMeasure.coe_mk] using integral_probabilityMeasure_map
      (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
      (measurable_linearSpectralVagueProcess E ρ n) (RealVagueMeasure.laplaceBoundedTest f hf)
  simpa only [heq] using h

end FixedCouplingPoisson
