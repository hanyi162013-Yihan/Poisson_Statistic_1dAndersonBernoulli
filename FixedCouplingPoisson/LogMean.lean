import FixedCouplingPoisson.ProjectiveCesaro

/-!
# Continuous Euclidean log means and positive finite averages

The actual transfer/inverse log-norm cocycles have uniformly bounded
integrands under the bounded potential law. Dominated convergence and Fubini
connect the continuous one-step mean to the actual stationary mean. A
positive finite forward Cesàro block follows from the preceding ordinary
Cesàro theorem. Identification with an iid product expectation is proved in
the subsequent product-cocycle module.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Filter
open scoped Topology

def oneStepLogMean (law : PotentialLaw) (E : ℝ) (p : ProjectivePoint) : ℝ :=
  ∫ v, transferLogCocycle E v p ∂law.measure

theorem continuous_projectiveGrowth_fixed (A : Matrix2) :
    Continuous (projectiveGrowth A) := by
  apply projectivize_isQuotientMap.continuous_iff.mpr
  change Continuous (fun u : NonzeroVector =>
    euclideanNorm (A *ᵥ (u : Vector2)) / euclideanNorm (u : Vector2))
  have hv : Continuous (fun u : NonzeroVector => (u : Vector2)) := continuous_subtype_val
  have hnum : Continuous (fun u : NonzeroVector => euclideanNorm (A *ᵥ (u : Vector2))) :=
    continuous_euclideanNorm.comp (continuous_const.matrix_mulVec hv)
  have hden : Continuous (fun u : NonzeroVector => euclideanNorm (u : Vector2)) :=
    continuous_euclideanNorm.comp hv
  exact hnum.div hden (fun u => (euclideanNorm_pos u u.2).ne')

theorem continuous_transferLogCocycle_direction (E v : ℝ) :
    Continuous (fun p : ProjectivePoint => transferLogCocycle E v p) := by
  change Continuous (fun p : ProjectivePoint => Real.log (projectiveGrowth (transfer E v) p))
  exact (continuous_projectiveGrowth_fixed (transfer E v)).log
    (fun p => (projectiveGrowth_transfer_pos E v p).ne')

theorem continuous_oneStepLogMean (law : PotentialLaw) (E : ℝ) :
    Continuous (oneStepLogMean law E) := by
  obtain ⟨C, _, hb⟩ := ae_uniform_logCocycle_bound law E
  change Continuous (fun p : ProjectivePoint => ∫ v, transferLogCocycle E v p ∂law.measure)
  apply continuous_of_dominated (bound := fun _ : ℝ => C)
  · intro p
    exact ((continuous_transferLogCocycle E).comp
      (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  · intro p
    exact hb.mono fun v hv => by simpa only [Real.norm_eq_abs] using hv p
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun v => continuous_transferLogCocycle_direction E v

def oneStepContinuousLogMean (law : PotentialLaw) (E : ℝ) : C(ProjectivePoint, ℝ) :=
  ⟨oneStepLogMean law E, continuous_oneStepLogMean law E⟩

theorem stationaryMean_eq_integral_oneStep (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    stationaryMean law E ν =
      ∫ p, oneStepLogMean law E p ∂(ν : Measure ProjectivePoint) :=
  integral_prod_symm _ (integrable_transferLogCocycle law E ν)

/-- Positivity of a finite average is derived, rather than included in the
external interface. It concerns actual integrals under actual iterated laws.
The block has length `n + 1`, so no zero-length exception occurs. -/
theorem exists_uniform_positive_log_cesaro (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) :
    ∃ n : ℕ, ∀ ν : ProbabilityMeasure ProjectivePoint,
      stationaryMean law E data.forwardMeasure / 2 ≤
        ∫ p, oneStepLogMean law E p
          ∂(empiricalCesaro law E ν n : Measure ProjectivePoint) := by
  have hp : 0 < ∫ p, (oneStepContinuousLogMean law E) p
      ∂(data.forwardMeasure : Measure ProjectivePoint) := by
    exact (stationaryMean_eq_integral_oneStep law E data.forwardMeasure) ▸
      data.stationary_mean_pos
  obtain ⟨n, hn⟩ := exists_positive_average_block law E data
    (oneStepContinuousLogMean law E) hp
  refine ⟨n, fun ν => ?_⟩
  simpa only [oneStepContinuousLogMean, ContinuousMap.coe_mk,
    ← stationaryMean_eq_integral_oneStep] using hn ν

def oneStepInverseLogMean (law : PotentialLaw) (E : ℝ) (p : ProjectivePoint) : ℝ :=
  ∫ v, inverseTransferLogCocycle E v p ∂law.measure

theorem continuous_inverseTransferLogCocycle_direction (E v : ℝ) :
    Continuous (fun p : ProjectivePoint => inverseTransferLogCocycle E v p) := by
  change Continuous (fun p : ProjectivePoint => Real.log (projectiveGrowth (transferInv E v) p))
  exact (continuous_projectiveGrowth_fixed (transferInv E v)).log
    (fun p => (projectiveGrowth_transferInv_pos E v p).ne')

theorem continuous_oneStepInverseLogMean (law : PotentialLaw) (E : ℝ) :
    Continuous (oneStepInverseLogMean law E) := by
  obtain ⟨C, _, hb⟩ := ae_uniform_inverseLogCocycle_bound law E
  change Continuous (fun p : ProjectivePoint => ∫ v, inverseTransferLogCocycle E v p ∂law.measure)
  apply continuous_of_dominated (bound := fun _ : ℝ => C)
  · intro p
    exact ((continuous_inverseTransferLogCocycle E).comp
      (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  · intro p
    exact hb.mono fun v hv => by simpa only [Real.norm_eq_abs] using hv p
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun v => continuous_inverseTransferLogCocycle_direction E v

theorem inverseStationaryMean_eq_integral_oneStep (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    inverseStationaryMean law E ν =
      ∫ p, oneStepInverseLogMean law E p ∂(ν : Measure ProjectivePoint) :=
  integral_prod_symm _ (integrable_inverseTransferLogCocycle law E ν)

end FixedCouplingPoisson.Furstenberg
