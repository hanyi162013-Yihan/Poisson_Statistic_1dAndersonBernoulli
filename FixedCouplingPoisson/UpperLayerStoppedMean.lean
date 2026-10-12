import FixedCouplingPoisson.UpperLayerRemaining
import FixedCouplingPoisson.CDFThreshold
import FixedCouplingPoisson.CDFMean

/-! Work draft: the raw upper-layer budget from two actual stopped identities.
The future restart formula remains available separately for residual arguments. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter

/-- The model-specific remaining time is exactly the generic stopped-time
quantity used in the proved occupation identities. -/
theorem canonicalUpperLayerRemaining_eq_remainingTime (E δ θ φ h : ℝ) :
    canonicalUpperLayerRemaining E δ θ φ h =
      Occupation.remainingTime (canonicalCrossingTime E δ θ φ)
        (canonicalUpperLayerTime E δ θ φ h) := rfl

/-- A lower bound on the physical gap gives a lower bound on the CDF coordinate,
including physical gaps which have already passed the first period. -/
theorem stationaryCDFLift_raw_upper_lower_uniform
    (ν : ℝ → ProbabilityMeasure ProjectivePoint) (hweak : Continuous ν)
    (hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ h ≥ 0, h < d → ∀ θ φ : ℝ, Real.pi - h ≤ θ - φ →
        Real.pi - ε ≤ stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ := by
  obtain ⟨d, hd, hb⟩ := stationaryCDFLift_period_gap_uniform ν hweak hatom hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd h hh hhd θ φ hgap
  have hEE' : |E - (E + δ)| < d := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using hδd
  have hclose : |(φ + Real.pi - h) - φ - (1 : ℤ) * Real.pi| < d := by
    have heq : (φ + Real.pi - h) - φ - (1 : ℤ) * Real.pi = -h := by
      simp only [Int.cast_one, one_mul]
      ring
    simpa only [heq, abs_neg, abs_of_nonneg hh] using hhd
  have hbound := hb E hE (E + δ) hE' hEE' (φ + Real.pi - h) φ 1 hclose
  simp only [Int.cast_one, one_mul] at hbound
  have hmono := stationaryCDFLift_monotone (ν E) (show φ + Real.pi - h ≤ θ by linarith)
  linarith [(abs_lt.mp hbound).1]

/-- The expected complete remaining time after raw upper-layer entrance is small
on the IDS scale, by stopping the same exact drift at entrance and at exit. -/
theorem canonicalUpperLayerRemaining_stopped_mean_uniform (law : PotentialLaw)
    (ν : ℝ → ProbabilityMeasure ProjectivePoint)
    (hweak : Continuous ν) (hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)
    (hstat : ∀ E, InverseStationary law E (ν E))
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
      ∀ h ≥ 0, h < d →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, Occupation.remainingTime (canonicalCrossingTime E δ θ φ)
            (canonicalUpperLayerTime E δ θ φ h) ω ∂iidMeasure law) ≤ ε := by
  obtain ⟨d0, hd0, hentry⟩ := stationaryCDFLift_raw_upper_lower_uniform
    ν hweak hatom hK (half_pos hε)
  obtain ⟨d1, hd1, hexit⟩ := cdfGapProcess_exit_uniform
    ν hweak hatom hK (half_pos hε)
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall h hh hhd hp
  let T := canonicalCrossingTime E δ θ φ
  let σ := canonicalUpperLayerTime E δ θ φ h
  let ν0 := ν E
  let ν1 := ν (E + δ)
  have hσm : Measurable σ := canonicalUpperLayerTime_measurable E δ θ φ h
  have hσle : ∀ ω, σ ω ≤ T ω := canonicalUpperLayerTime_le_crossing E δ θ φ h hh
  obtain ⟨hfiniteT, hiT, hidT⟩ := canonicalCrossingTime_finite_mean_IDS law ν0 ν1
    E δ θ φ (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp
  obtain ⟨hfiniteσ, hiσ, hidσ⟩ := cdfGapProcess_stopped_IDS_of_le_crossing law ν0 ν1
    E δ θ φ (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp
    (canonicalUpperLayerTime_isStoppingTime E δ θ φ h) hσm hσle
  have hiWT := integrable_cdfGapProcess_atCrossing law ν0 ν1
    E δ θ φ hδ hinit hsmall.le hfiniteT
  have hiWσ := integrable_cdfGapProcess_randomTime law ν0 ν1
    E δ θ φ hδ hinit hsmall.le hσm hfiniteσ hσle
  have hTupper : (∫ ω, cdfGapProcess ν0 ν1 E δ θ φ ((T ω).untopD 0) ω
      ∂iidMeasure law) ≤ Real.pi + ε / 2 := by
    calc
      _ ≤ ∫ _ : PotentialSpace, Real.pi + ε / 2 ∂iidMeasure law :=
        integral_mono_ae hiWT (integrable_const _) (by
          filter_upwards [hfiniteT] with ω hω
          obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
          have he := hexit E hE δ hδ hE' (hδd.trans_le (min_le_right _ _))
            θ φ hsmall ω n hn.symm
          have hb := (abs_lt.mp he).2
          simpa only [← hn, WithTop.untopD_coe] using (show
            cdfGapProcess ν0 ν1 E δ θ φ n ω ≤ Real.pi + ε / 2 by linarith))
      _ = _ := by simp
  have hσlower : Real.pi - ε / 2 ≤
      (∫ ω, cdfGapProcess ν0 ν1 E δ θ φ ((σ ω).untopD 0) ω ∂iidMeasure law) := by
    calc
      _ = ∫ _ : PotentialSpace, Real.pi - ε / 2 ∂iidMeasure law := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hiWσ (by
        filter_upwards [hfiniteσ] with ω hω
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
        have hhit := canonicalUpperLayerTime_hits E δ θ φ h n ω hn.symm
        have he := hentry E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
          h hh (hhd.trans_le (min_le_left _ _))
          (canonicalPhaseProcess E θ n ω) (canonicalPhaseProcess (E + δ) φ n ω) hhit
        have hσn : σ ω = (n : WithTop ℕ) := hn.symm
        change Real.pi - ε / 2 ≤ cdfGapProcess ν0 ν1 E δ θ φ n ω at he
        simpa only [hσn, Nat.cast_withTop, WithTop.untopD_coe, Nat.cast_id] using he)
  rw [Occupation.remainingTime_integral_eq_sub hiT hiσ hfiniteT (ae_of_all _ hσle)]
  calc
    _ = (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) -
        (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((σ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) := mul_sub _ _ _
    _ = (∫ ω, cdfGapProcess ν0 ν1 E δ θ φ ((T ω).untopD 0) ω ∂iidMeasure law) -
        (∫ ω, cdfGapProcess ν0 ν1 E δ θ φ ((σ ω).untopD 0) ω ∂iidMeasure law) := by
      rw [hidT, hidσ]
      ring
    _ ≤ (Real.pi + ε / 2) - (Real.pi - ε / 2) := sub_le_sub hTupper hσlower
    _ = ε := by ring

/-- Actual inverse-stationary specialization of the complete raw-upper
remaining-time budget. -/
theorem inverseUpperLayerRemaining_stopped_mean_uniform (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
      ∀ h ≥ 0, h < d →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, Occupation.remainingTime (canonicalCrossingTime E δ θ φ)
            (canonicalUpperLayerTime E δ θ φ h) ω ∂iidMeasure law) ≤ ε :=
  canonicalUpperLayerRemaining_stopped_mean_uniform law
    (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons)
    (fun E => (input.atEnergy E).inverse_stationary) hK hε

end FixedCouplingPoisson.Furstenberg
