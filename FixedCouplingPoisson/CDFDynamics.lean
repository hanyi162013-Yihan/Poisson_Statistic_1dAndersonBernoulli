import FixedCouplingPoisson.HarmonicCDF
import FixedCouplingPoisson.PhaseWeakTools
import FixedCouplingPoisson.IIDKernel
import FixedCouplingPoisson.PhaseProcess
import FixedCouplingPoisson.PhaseIDS
import FixedCouplingPoisson.StoppingLimit


/-! Factored proof group: CDFDrift. -/

/-!
Work draft. The actual one-step CDF increment has a finite mean independent
of the starting angle. Rotation/IDS identification is a separate next step.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Real

theorem abs_sub_le_sum_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc
    _ = |a + (-b)| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = _ := by rw [abs_neg]

theorem norm_stationaryCDFLift_canonicalPhase_le (ν : ProbabilityMeasure ProjectivePoint)
    (E v θ : ℝ) :
    ‖stationaryCDFLift ν (canonicalPhase E v θ)‖ ≤ |θ| + 3 * Real.pi := by
  have h₁ : |stationaryCDFLift ν (canonicalPhase E v θ)| ≤
      |stationaryCDFLift ν (canonicalPhase E v θ) - canonicalPhase E v θ| +
        |canonicalPhase E v θ| := by
    calc
      _ = |(stationaryCDFLift ν (canonicalPhase E v θ) - canonicalPhase E v θ) +
          canonicalPhase E v θ| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have h₂ : |canonicalPhase E v θ| ≤ |canonicalPhase E v θ - θ| + |θ| := by
    calc
      _ = |(canonicalPhase E v θ - θ) + θ| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  rw [Real.norm_eq_abs]
  nlinarith [stationaryCDFLift_close_identity ν (canonicalPhase E v θ),
    canonicalPhase_displacement_le E v θ]

theorem integrable_stationaryCDFLift_canonicalPhase (law : PotentialLaw) (E θ : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    Integrable (fun v => stationaryCDFLift ν (canonicalPhase E v θ)) law.measure := by
  apply (integrable_const (|θ| + 3 * Real.pi)).mono'
  · exact ((stationaryCDFLift_monotone ν).measurable.comp
      ((canonicalPhase_measurable_potential_angle E).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · exact ae_of_all _ fun v => norm_stationaryCDFLift_canonicalPhase_le ν E v θ

def cdfOneStepMean (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) : ℝ :=
  ∫ v, stationaryCDFLift ν (canonicalPhase E v θ) - stationaryCDFLift ν θ ∂law.measure

theorem norm_stationaryCDFLift_increment_le (ν : ProbabilityMeasure ProjectivePoint)
    (E v θ : ℝ) :
    ‖stationaryCDFLift ν (canonicalPhase E v θ) - stationaryCDFLift ν θ‖ ≤ 4 * Real.pi := by
  have h := abs_add_le
    (stationaryCDFLift ν (canonicalPhase E v θ) - canonicalPhase E v θ)
    (canonicalPhase E v θ - θ)
  have h' := abs_add_le
    ((stationaryCDFLift ν (canonicalPhase E v θ) - canonicalPhase E v θ) +
      (canonicalPhase E v θ - θ)) (θ - stationaryCDFLift ν θ)
  have heq : (stationaryCDFLift ν (canonicalPhase E v θ) - canonicalPhase E v θ) +
      (canonicalPhase E v θ - θ) + (θ - stationaryCDFLift ν θ) =
      stationaryCDFLift ν (canonicalPhase E v θ) - stationaryCDFLift ν θ := by ring
  rw [heq] at h'
  rw [abs_sub_comm θ] at h'
  rw [Real.norm_eq_abs]
  linarith [stationaryCDFLift_close_identity ν (canonicalPhase E v θ),
    stationaryCDFLift_close_identity ν θ, canonicalPhase_displacement_le E v θ]

theorem cdfOneStepMean_eq (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : InverseStationary law E ν) (θ φ : ℝ) :
    cdfOneStepMean law E ν θ = cdfOneStepMean law E ν φ := by
  have hθ := integrable_stationaryCDFLift_canonicalPhase law E θ ν
  have hφ := integrable_stationaryCDFLift_canonicalPhase law E φ ν
  have hgap := inverse_stationary_exact_gap law E ν hν θ φ
  rw [integral_sub hθ hφ] at hgap
  have hmeanθ : cdfOneStepMean law E ν θ =
      (∫ v, stationaryCDFLift ν (canonicalPhase E v θ) ∂law.measure) - stationaryCDFLift ν θ := by
    rw [cdfOneStepMean, integral_sub hθ (integrable_const _)]
    simp
  have hmeanφ : cdfOneStepMean law E ν φ =
      (∫ v, stationaryCDFLift ν (canonicalPhase E v φ) ∂law.measure) - stationaryCDFLift ν φ := by
    rw [cdfOneStepMean, integral_sub hφ (integrable_const _)]
    simp
  rw [hmeanθ, hmeanφ]
  linarith

def rotationIncrement (law : PotentialLaw) (E : ℝ) (ν : ProbabilityMeasure ProjectivePoint) : ℝ :=
  cdfOneStepMean law E ν 0

theorem inverse_stationary_one_step_identity (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : InverseStationary law E ν) (θ : ℝ) :
    (∫ v, stationaryCDFLift ν (canonicalPhase E v θ) - stationaryCDFLift ν θ ∂law.measure) =
      rotationIncrement law E ν := cdfOneStepMean_eq law E ν hν θ 0

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFProcess. -/

/-! Unchecked work draft. Actual iid harmonic-coordinate conditional drift,
followed by identification of the one-step mean with the actual IDS. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

def cdfProcess (ν : ProbabilityMeasure ProjectivePoint) (E θ : ℝ)
    (n : ℕ) (ω : PotentialSpace) : ℝ :=
  stationaryCDFLift ν (canonicalPhaseProcess E θ n ω)

theorem cdfProcess_past_measurable (ν : ProbabilityMeasure ProjectivePoint)
    (E θ : ℝ) (n : ℕ) : Measurable[pastMeasurableSpace n] (cdfProcess ν E θ n) :=
  (stationaryCDFLift_monotone ν).measurable.comp
    (canonicalPhaseProcess_past_measurable E θ n)

theorem cdfProcess_measurable (ν : ProbabilityMeasure ProjectivePoint)
    (E θ : ℝ) (n : ℕ) : Measurable (cdfProcess ν E θ n) :=
  (cdfProcess_past_measurable ν E θ n).mono (pastMeasurableSpace_le n) le_rfl

def cdfFutureIncrement (ν : ProbabilityMeasure ProjectivePoint) (E : ℝ)
    (p : ℝ × PotentialSpace) : ℝ :=
  stationaryCDFLift ν (canonicalPhase E (p.2 0) p.1) - stationaryCDFLift ν p.1

theorem measurable_cdfFutureIncrement (ν : ProbabilityMeasure ProjectivePoint) (E : ℝ) :
    Measurable (cdfFutureIncrement ν E) := by
  have hsite : Measurable (fun p : ℝ × PotentialSpace => p.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have hpair : Measurable (fun p : ℝ × PotentialSpace => (p.2 0, p.1)) :=
    hsite.prodMk measurable_fst
  have hphase : Measurable (fun p : ℝ × PotentialSpace => canonicalPhase E (p.2 0) p.1) :=
    (canonicalPhase_measurable_potential_angle E).comp hpair
  have hleft : Measurable (fun p : ℝ × PotentialSpace =>
      stationaryCDFLift ν (canonicalPhase E (p.2 0) p.1)) :=
    (stationaryCDFLift_monotone ν).measurable.comp hphase
  exact hleft.sub ((stationaryCDFLift_monotone ν).measurable.comp measurable_fst)

theorem integrable_cdfFutureIncrement (law : PotentialLaw)
    (ν : ProbabilityMeasure ProjectivePoint) (E : ℝ) (η : ProbabilityMeasure ℝ) :
    Integrable (cdfFutureIncrement ν E) ((η : Measure ℝ).prod (iidMeasure law)) :=
  (integrable_const (4 * Real.pi)).mono'
    (measurable_cdfFutureIncrement ν E).aestronglyMeasurable
    (ae_of_all _ fun p => norm_stationaryCDFLift_increment_le ν E (p.2 0) p.1)

theorem integrable_cdfProcess (law : PotentialLaw) (ν : ProbabilityMeasure ProjectivePoint)
    (E θ : ℝ) (n : ℕ) : Integrable (cdfProcess ν E θ n) (iidMeasure law) := by
  induction n with
  | zero =>
    have hzero : cdfProcess ν E θ 0 = (fun _ω : PotentialSpace => stationaryCDFLift ν θ) := by
      funext ω
      simp only [cdfProcess, canonicalPhaseProcess_zero]
    rw [hzero]
    exact integrable_const _
  | succ n ih =>
    have hi : Integrable (fun ω => cdfProcess ν E θ (n + 1) ω - cdfProcess ν E θ n ω)
        (iidMeasure law) :=
      (integrable_const (μ := iidMeasure law) (4 * Real.pi)).mono'
        ((cdfProcess_measurable ν E θ (n + 1)).sub
          (cdfProcess_measurable ν E θ n)).aestronglyMeasurable
        (ae_of_all _ fun ω => norm_stationaryCDFLift_increment_le ν E (ω n)
          (canonicalPhaseProcess E θ n ω))
    have hsum : Integrable (fun ω =>
        (cdfProcess ν E θ (n + 1) ω - cdfProcess ν E θ n ω) + cdfProcess ν E θ n ω)
        (iidMeasure law) := hi.add ih
    simpa only [sub_add_cancel] using hsum

theorem futureKernel_cdfIncrement (law : PotentialLaw) (ν : ProbabilityMeasure ProjectivePoint)
    (E : ℝ) (hν : InverseStationary law E ν) (θ : ℝ) :
    futureKernel law (cdfFutureIncrement ν E) θ = rotationIncrement law E ν := by
  have hm : Measurable (fun v => stationaryCDFLift ν (canonicalPhase E v θ) -
      stationaryCDFLift ν θ) :=
    ((stationaryCDFLift_monotone ν).measurable.comp
      ((canonicalPhase_measurable_potential_angle E).comp
        (measurable_id.prodMk measurable_const))).sub measurable_const
  calc
    _ = ∫ v, stationaryCDFLift ν (canonicalPhase E v θ) - stationaryCDFLift ν θ
        ∂(iidMeasure law).map (fun ω => ω 0) :=
      (integral_map (measurable_site 0).aemeasurable hm.aestronglyMeasurable).symm
    _ = rotationIncrement law E ν := by
      rw [iidMeasure_site_map]
      exact inverse_stationary_one_step_identity law E ν hν θ

theorem cdfProcess_condExp_increment (law : PotentialLaw)
    (ν : ProbabilityMeasure ProjectivePoint) (E θ : ℝ)
    (hν : InverseStationary law E ν) (n : ℕ) :
    (iidMeasure law)[(fun ω => cdfProcess ν E θ (n + 1) ω - cdfProcess ν E θ n ω) |
      pastMeasurableSpace n] =ᵐ[iidMeasure law] (fun _ => rotationIncrement law E ν) := by
  let X := canonicalPhaseProcess E θ n
  let η : ProbabilityMeasure ℝ :=
    ⟨(iidMeasure law).map X, (iidMeasure law).isProbabilityMeasure_map
      (canonicalPhaseProcess_measurable E θ n).aemeasurable⟩
  have hf := integrable_cdfFutureIncrement law ν E η
  have hk := iidMeasure_condExp_past_futureKernel law n
    (canonicalPhaseProcess_past_measurable E θ n)
    (measurable_cdfFutureIncrement ν E) hf
  have heq : (fun ω => cdfFutureIncrement ν E (X ω, potentialShift n ω)) =
      (fun ω => cdfProcess ν E θ (n + 1) ω - cdfProcess ν E θ n ω) := by
    funext ω
    simp only [cdfFutureIncrement, cdfProcess, canonicalPhaseProcess_succ,
      potentialShift, Nat.add_zero, X]
  rw [heq] at hk
  refine hk.trans (ae_of_all _ fun ω => ?_)
  exact futureKernel_cdfIncrement law ν E hν (X ω)

theorem cdfProcess_condExp_step (law : PotentialLaw)
    (ν : ProbabilityMeasure ProjectivePoint) (E θ : ℝ)
    (hν : InverseStationary law E ν) (n : ℕ) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[cdfProcess ν E θ (n + 1) | pastMeasurableSpace n]) ω -
        cdfProcess ν E θ n ω = rotationIncrement law E ν := by
  have hs := condExp_sub (integrable_cdfProcess law ν E θ (n + 1))
    (integrable_cdfProcess law ν E θ n) (pastMeasurableSpace n)
  have hc := condExp_of_stronglyMeasurable (pastMeasurableSpace_le n)
    (cdfProcess_past_measurable ν E θ n).stronglyMeasurable
    (integrable_cdfProcess law ν E θ n)
  filter_upwards [cdfProcess_condExp_increment law ν E θ hν n, hs] with ω hω hsω
  simpa only [hc, Pi.sub_apply] using hsω.symm.trans hω

theorem integral_cdfProcess (law : PotentialLaw) (ν : ProbabilityMeasure ProjectivePoint)
    (E θ : ℝ) (hν : InverseStationary law E ν) (n : ℕ) :
    (∫ ω, cdfProcess ν E θ n ω ∂iidMeasure law) =
      stationaryCDFLift ν θ + (n : ℝ) * rotationIncrement law E ν := by
  induction n with
  | zero => simp [cdfProcess]
  | succ n ih =>
    have hint := integral_congr_ae (cdfProcess_condExp_increment law ν E θ hν n)
    rw [integral_condExp (pastMeasurableSpace_le n),
      integral_sub (integrable_cdfProcess law ν E θ (n + 1))
        (integrable_cdfProcess law ν E θ n)] at hint
    simp only [integral_const, probReal_univ, one_smul] at hint
    rw [ih] at hint
    push_cast
    linarith

theorem integral_cdfProcess_shooting_error (law : PotentialLaw)
    (ν : ProbabilityMeasure ProjectivePoint) (E : ℝ) (n : ℕ) :
    |(∫ ω, cdfProcess ν E 0 n ω ∂iidMeasure law) -
      (∫ ω, shootingPhase E ω n ∂iidMeasure law)| ≤ Real.pi := by
  have h := norm_integral_le_of_norm_le_const (μ := iidMeasure law)
    (f := fun ω => cdfProcess ν E 0 n ω - shootingPhase E ω n)
    (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, cdfProcess, shootingPhase_eq_process] using
        stationaryCDFLift_close_identity ν (canonicalPhaseProcess E 0 n ω))
  rw [integral_sub (integrable_cdfProcess law ν E 0 n)
    (integrable_shootingPhase law E n)] at h
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- The actual harmonic drift equals the actual IDS rotation increment. -/
theorem rotationIncrement_eq_idsCandidate (law : PotentialLaw)
    (ν : ProbabilityMeasure ProjectivePoint) (E : ℝ) (hν : InverseStationary law E ν) :
    rotationIncrement law E ν = Real.pi * (1 - idsCandidate law E) := by
  let A := fun n => ∫ ω, cdfProcess ν E 0 n ω ∂iidMeasure law
  let P := fun n => ∫ ω, shootingPhase E ω n ∂iidMeasure law
  have hd := bounded_div_nat_tendsto_zero (fun n => A n - P n) Real.pi
    (integral_cdfProcess_shooting_error law ν E)
  have hIDS : Tendsto (fun n => A n / (n : ℝ)) atTop
      (nhds (Real.pi * (1 - idsCandidate law E))) := by
    have h := (mean_shootingPhase_tendsto_idsCandidate law E).add hd
    simpa only [add_zero] using h.congr (fun n => by dsimp [A, P]; ring)
  have hconst :=
    (tendsto_const_div_atTop_nhds_zero_nat (stationaryCDFLift ν 0)).add_const
      (rotationIncrement law E ν)
  have hg : Tendsto (fun n => A n / (n : ℝ)) atTop
      (nhds (rotationIncrement law E ν)) := by
    simp only [zero_add] at hconst
    apply hconst.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    dsimp [A]
    rw [integral_cdfProcess law ν E 0 hν n, add_div, mul_div_cancel_left₀ _ hn0]
  exact tendsto_nhds_unique hg hIDS

theorem cdfProcess_condExp_IDS (law : PotentialLaw)
    (ν : ProbabilityMeasure ProjectivePoint) (E θ : ℝ)
    (hν : InverseStationary law E ν) (n : ℕ) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[cdfProcess ν E θ (n + 1) | pastMeasurableSpace n]) ω -
        cdfProcess ν E θ n ω = Real.pi * (1 - idsCandidate law E) := by
  simpa only [rotationIncrement_eq_idsCandidate law ν E hν] using
    cdfProcess_condExp_step law ν E θ hν n

def cdfGapProcess (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (n : ℕ) (ω : PotentialSpace) : ℝ :=
  cdfProcess ν E θ n ω - cdfProcess ν' (E + δ) φ n ω

@[simp] theorem cdfGapProcess_zero (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (ω : PotentialSpace) :
    cdfGapProcess ν ν' E δ θ φ 0 ω = stationaryCDFLift ν θ - stationaryCDFLift ν' φ := rfl

theorem integrable_cdfGapProcess (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ) (n : ℕ) :
    Integrable (cdfGapProcess ν ν' E δ θ φ n) (iidMeasure law) :=
  (integrable_cdfProcess law ν E θ n).sub (integrable_cdfProcess law ν' (E + δ) φ n)

theorem cdfGapProcess_condExp_IDS (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν') (n : ℕ) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[cdfGapProcess ν ν' E δ θ φ (n + 1) | pastMeasurableSpace n]) ω -
        cdfGapProcess ν ν' E δ θ φ n ω =
          Real.pi * (idsCandidate law (E + δ) - idsCandidate law E) := by
  have hs := condExp_sub (integrable_cdfProcess law ν E θ (n + 1))
    (integrable_cdfProcess law ν' (E + δ) φ (n + 1)) (pastMeasurableSpace n)
  filter_upwards [hs, cdfProcess_condExp_IDS law ν E θ hν n,
    cdfProcess_condExp_IDS law ν' (E + δ) φ hν' n] with ω hsω hE hE'
  change ((iidMeasure law)[cdfProcess ν E θ (n + 1) -
      cdfProcess ν' (E + δ) φ (n + 1) | pastMeasurableSpace n]) ω -
    (cdfProcess ν E θ n ω - cdfProcess ν' (E + δ) φ n ω) = _
  rw [hsω]
  change ((iidMeasure law)[cdfProcess ν E θ (n + 1) | pastMeasurableSpace n]) ω -
      ((iidMeasure law)[cdfProcess ν' (E + δ) φ (n + 1) | pastMeasurableSpace n]) ω -
      (cdfProcess ν E θ n ω - cdfProcess ν' (E + δ) φ n ω) = _
  linarith

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFStopping. -/

/-! Unchecked work draft. A rough deterministic bound suffices to prove
finiteness and integrability of the actual first crossing from its positive
IDS drift. The unbounded stopped identity is taken only after this step. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

def crossingTruncIndex (E δ θ φ : ℝ) (N : ℕ) (ω : PotentialSpace) : ℕ :=
  (min (canonicalCrossingTime E δ θ φ ω) (N : WithTop ℕ)).untopD 0

theorem crossingTruncIndex_coe (E δ θ φ : ℝ) (N : ℕ) (ω : PotentialSpace) :
    (crossingTruncIndex E δ θ φ N ω : WithTop ℕ) =
      min (canonicalCrossingTime E δ θ φ ω) (N : WithTop ℕ) := by
  cases h : canonicalCrossingTime E δ θ φ ω with
  | top =>
    simp only [crossingTruncIndex, h, min_top_left]
    rfl
  | coe n =>
    simp only [crossingTruncIndex, h]
    rfl

theorem crossingTruncIndex_le (E δ θ φ : ℝ) (N : ℕ) (ω : PotentialSpace) :
    crossingTruncIndex E δ θ φ N ω ≤ N := by
  have h := min_le_right (canonicalCrossingTime E δ θ φ ω) (N : WithTop ℕ)
  rw [← crossingTruncIndex_coe] at h
  exact_mod_cast h

theorem crossingTruncIndex_event_iff (E δ θ φ : ℝ) (N j : ℕ) (ω : PotentialSpace) :
    j < crossingTruncIndex E δ θ φ N ω ↔
      (j : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω ∧ j < N := by
  have h : j < crossingTruncIndex E δ θ φ N ω ↔
      (j : WithTop ℕ) < (crossingTruncIndex E δ θ φ N ω : WithTop ℕ) := by
    exact WithTop.coe_lt_coe.symm
  exact h.trans (by
    rw [crossingTruncIndex_coe, lt_min_iff]
    exact and_congr Iff.rfl WithTop.coe_lt_coe)

theorem crossingTruncIndex_event_measurable (E δ θ φ : ℝ) (N j : ℕ) :
    MeasurableSet[pastMeasurableSpace j] {ω | j < crossingTruncIndex E δ θ φ N ω} := by
  have heq : {ω | j < crossingTruncIndex E δ θ φ N ω} =
      {ω | (j : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω} ∩
        {ω : PotentialSpace | j < N} := by
    ext ω
    exact crossingTruncIndex_event_iff E δ θ φ N j ω
  rw [heq]
  exact ((canonicalCrossingTime_isStoppingTime E δ θ φ).measurableSet_gt j).inter
    (MeasurableSet.const _)

theorem measurable_crossingTruncIndex (E δ θ φ : ℝ) (N : ℕ) :
    Measurable (crossingTruncIndex E δ θ φ N) :=
  (WithTop.measurable_untopD 0).comp
    ((canonicalCrossingTime_measurable E δ θ φ).min measurable_const)

theorem measurable_cdfGapProcess (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) : Measurable (cdfGapProcess ν ν' E δ θ φ n) :=
  (cdfProcess_measurable ν E θ n).sub (cdfProcess_measurable ν' (E + δ) φ n)

theorem measurable_cdfGapProcess_randomNat (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) {τ : PotentialSpace → ℕ} (hτ : Measurable τ) :
    Measurable (fun ω => cdfGapProcess ν ν' E δ θ φ (τ ω) ω) := by
  have hfield : Measurable (fun p : ℕ × PotentialSpace =>
      cdfGapProcess ν ν' E δ θ φ p.1 p.2) :=
    measurable_from_prod_countable_right (fun n => measurable_cdfGapProcess ν ν' E δ θ φ n)
  have hcomp := hfield.comp (hτ.prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using hcomp

theorem measurable_cdfGapProcess_truncated (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (N : ℕ) :
    Measurable (fun ω => cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω) :=
  measurable_cdfGapProcess_randomNat ν ν' E δ θ φ
    (measurable_crossingTruncIndex E δ θ φ N)

theorem canonicalGapProcess_truncated_bounds (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (N : ℕ) (ω : PotentialSpace) :
    0 ≤ canonicalGapProcess E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω ∧
      canonicalGapProcess E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω ≤ Real.pi + δ := by
  refine ⟨canonicalGapProcess_nonneg E δ θ φ hδ hinit _ ω, ?_⟩
  let t := crossingTruncIndex E δ θ φ N ω
  change canonicalGapProcess E δ θ φ t ω ≤ Real.pi + δ
  have ht : (t : WithTop ℕ) ≤ canonicalCrossingTime E δ θ φ ω := by
    rw [show (t : WithTop ℕ) = min (canonicalCrossingTime E δ θ φ ω) (N : WithTop ℕ)
      from crossingTruncIndex_coe E δ θ φ N ω]
    exact min_le_left _ _
  by_cases hbefore : (t : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω
  · exact (canonicalCrossingTime_before E δ θ φ t ω hbefore).le.trans
      (le_add_of_nonneg_right hδ)
  · have heq : canonicalCrossingTime E δ θ φ ω = t := le_antisymm (le_of_not_gt hbefore) ht
    cases ht0 : t with
    | zero => simpa only [ht0, canonicalGapProcess_zero] using
        hsmall.trans (le_add_of_nonneg_right hδ)
    | succ n =>
      rw [ht0] at heq
      exact (canonicalCrossingTime_overshoot E δ θ φ hδ n ω heq).2

theorem cdfGapProcess_close_canonicalGap (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    |cdfGapProcess ν ν' E δ θ φ n ω - canonicalGapProcess E δ θ φ n ω| ≤ 2 * Real.pi := by
  have heq : cdfGapProcess ν ν' E δ θ φ n ω - canonicalGapProcess E δ θ φ n ω =
      (stationaryCDFLift ν (canonicalPhaseProcess E θ n ω) - canonicalPhaseProcess E θ n ω) -
        (stationaryCDFLift ν' (canonicalPhaseProcess (E + δ) φ n ω) -
          canonicalPhaseProcess (E + δ) φ n ω) := by
    dsimp [cdfGapProcess, cdfProcess, canonicalGapProcess]
    ring
  rw [heq]
  have h := (abs_sub_le_sum_abs
    (stationaryCDFLift ν (canonicalPhaseProcess E θ n ω) - canonicalPhaseProcess E θ n ω)
    (stationaryCDFLift ν' (canonicalPhaseProcess (E + δ) φ n ω) -
      canonicalPhaseProcess (E + δ) φ n ω)).trans
    (add_le_add (stationaryCDFLift_close_identity ν _) (stationaryCDFLift_close_identity ν' _))
  simpa only [two_mul] using h

theorem norm_cdfGapProcess_truncated_le (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (N : ℕ) (ω : PotentialSpace) :
    ‖cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω‖ ≤ 3 * Real.pi + δ := by
  let t := crossingTruncIndex E δ θ φ N ω
  have hb := canonicalGapProcess_truncated_bounds E δ θ φ hδ hinit hsmall N ω
  have he := cdfGapProcess_close_canonicalGap ν ν' E δ θ φ t ω
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |cdfGapProcess ν ν' E δ θ φ t ω - canonicalGapProcess E δ θ φ t ω| +
        |canonicalGapProcess E δ θ φ t ω| := by
          have h := abs_add_le
            (cdfGapProcess ν ν' E δ θ φ t ω - canonicalGapProcess E δ θ φ t ω)
            (canonicalGapProcess E δ θ φ t ω)
          simpa only [sub_add_cancel] using h
    _ ≤ 2 * Real.pi + (Real.pi + δ) := add_le_add he (by rw [abs_of_nonneg hb.1]; exact hb.2)
    _ = _ := by ring

theorem integrable_cdfGapProcess_truncated (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (N : ℕ) :
    Integrable (fun ω => cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω)
      (iidMeasure law) :=
  (integrable_const (3 * Real.pi + δ)).mono'
    (measurable_cdfGapProcess_truncated ν ν' E δ θ φ N).aestronglyMeasurable
    (ae_of_all _ (norm_cdfGapProcess_truncated_le ν ν' E δ θ φ hδ hinit hsmall N))

theorem measurable_cdfGapProcess_atCrossing (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) :
    Measurable (fun ω => cdfGapProcess ν ν' E δ θ φ
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω) :=
  measurable_cdfGapProcess_randomNat ν ν' E δ θ φ
    ((WithTop.measurable_untopD 0).comp (canonicalCrossingTime_measurable E δ θ φ))

theorem integrable_cdfGapProcess_atCrossing (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    Integrable (fun ω => cdfGapProcess ν ν' E δ θ φ
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω) (iidMeasure law) := by
  apply (integrable_const (3 * Real.pi + δ)).mono'
    (measurable_cdfGapProcess_atCrossing ν ν' E δ θ φ).aestronglyMeasurable
  filter_upwards [hfinite] with ω hω
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  have hb := norm_cdfGapProcess_truncated_le ν ν' E δ θ φ hδ hinit hsmall n ω
  have ht : crossingTruncIndex E δ θ φ n ω = n := by
    rw [crossingTruncIndex, ← hn]
    change (min n n : ℕ) = n
    exact min_self n
  simpa only [ht, ← hn, WithTop.untopD_coe] using hb

theorem cdfGapProcess_bounded_stopped_IDS (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (N : ℕ) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
        (∫ ω, Occupation.truncatedTime (canonicalCrossingTime E δ θ φ) N ω ∂iidMeasure law) =
      (∫ ω, cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω ∂iidMeasure law) -
        (stationaryCDFLift ν θ - stationaryCDFLift ν' φ) := by
  have h := Occupation.bounded_stopped_drift_identity
    pastMeasurableSpace pastMeasurableSpace_le (crossingTruncIndex E δ θ φ N) N
    (crossingTruncIndex_le E δ θ φ N) (crossingTruncIndex_event_measurable E δ θ φ N)
    (cdfGapProcess ν ν' E δ θ φ) (integrable_cdfGapProcess law ν ν' E δ θ φ)
    (integrable_cdfGapProcess_truncated law ν ν' E δ θ φ hδ hinit hsmall N)
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))
    (fun j _ => cdfGapProcess_condExp_IDS law ν ν' E δ θ φ hν hν' j)
  have htr : Occupation.truncatedTime (canonicalCrossingTime E δ θ φ) N =
      (fun ω => (crossingTruncIndex E δ θ φ N ω : ℝ)) := rfl
  have hzero : (fun ω => cdfGapProcess ν ν' E δ θ φ 0 ω) =
      (fun _ω : PotentialSpace => stationaryCDFLift ν θ - stationaryCDFLift ν' φ) :=
    funext (cdfGapProcess_zero ν ν' E δ θ φ)
  rw [htr]
  rw [hzero] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem cdfGapProcess_initial_lower (ν ν' : ProbabilityMeasure ProjectivePoint)
    (θ φ : ℝ) (hinit : φ ≤ θ) :
    -(2 * Real.pi) ≤ stationaryCDFLift ν θ - stationaryCDFLift ν' φ := by
  have hθ := (abs_le.mp (stationaryCDFLift_close_identity ν θ)).1
  have hφ := (abs_le.mp (stationaryCDFLift_close_identity ν' φ)).2
  linarith

/-- This scaled truncated mean is bounded before any assumption of
almost-sure finiteness, so there is no circular use of optional stopping. -/
theorem canonicalCrossingTime_scaled_truncated_mean_le (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (N : ℕ) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.truncatedTime (canonicalCrossingTime E δ θ φ) N ω ∂iidMeasure law) ≤
        5 * Real.pi + δ := by
  have hbound : (∫ ω, cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω
      ∂iidMeasure law) ≤ 3 * Real.pi + δ := by
    calc
      _ ≤ ∫ _ω : PotentialSpace, 3 * Real.pi + δ ∂iidMeasure law :=
        integral_mono_ae (integrable_cdfGapProcess_truncated law ν ν' E δ θ φ hδ hinit hsmall N)
          (integrable_const _) (ae_of_all _ fun ω =>
            (le_abs_self _).trans (norm_cdfGapProcess_truncated_le ν ν' E δ θ φ hδ hinit hsmall N ω))
      _ = _ := by simp
  rw [cdfGapProcess_bounded_stopped_IDS law ν ν' E δ θ φ hν hν' hδ hinit hsmall N]
  linarith [cdfGapProcess_initial_lower ν ν' θ φ hinit]

/-- No finiteness of the crossing time is assumed. Positive actual IDS
increment first yields its finite expectation; the exact identity follows. -/
theorem canonicalCrossingTime_finite_mean_IDS (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) :
    (∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) ∧
      Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) (iidMeasure law) ∧
      (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) =
        (∫ ω, cdfGapProcess ν ν' E δ θ φ ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω
          ∂iidMeasure law) - (stationaryCDFLift ν θ - stationaryCDFLift ν' φ) :=
  Occupation.finite_mean_and_stopped_identity
    (canonicalCrossingTime_measurable E δ θ φ) (cdfGapProcess ν ν' E δ θ φ)
    (mul_pos Real.pi_pos hp)
    (fun N => (measurable_cdfGapProcess_truncated ν ν' E δ θ φ N).aestronglyMeasurable)
    (fun N => ae_of_all _ (norm_cdfGapProcess_truncated_le ν ν' E δ θ φ hδ hinit hsmall N))
    (cdfGapProcess_bounded_stopped_IDS law ν ν' E δ θ φ hν hν' hδ hinit hsmall)

theorem canonicalCrossingTime_scaled_mean_le (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤
        5 * Real.pi + δ := by
  obtain ⟨hfinite, hi, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν' E δ θ φ
    hν hν' hδ hinit hsmall hp
  have hlim := (Occupation.truncatedTime_integral_tendsto
    (canonicalCrossingTime_measurable E δ θ φ) hfinite hi).const_mul
      (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall
    (canonicalCrossingTime_scaled_truncated_mean_le law ν ν' E δ θ φ hν hν' hδ hinit hsmall))

end FixedCouplingPoisson.Furstenberg
