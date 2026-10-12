import FixedCouplingPoisson.CDFOccupation

/-! The nonnegative same-energy gap has the same vanishing scaled
occupation as the absolute exact-drift coordinate. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

theorem cdfKilledGapProcess_le_norm_add
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ η : ℝ)
    (hη : 0 ≤ η)
    (henergy : ∀ n ω, |cdfGapProcess ν ν' E δ θ φ n ω -
      cdfSameEnergyGapProcess ν E δ θ φ n ω| ≤ η) (n : ℕ) (ω : PotentialSpace) :
    cdfKilledGapProcess ν E δ θ φ n ω ≤
      cdfKilledNormProcess ν ν' E δ θ φ n ω + η := by
  unfold cdfKilledGapProcess cdfKilledNormProcess
  split_ifs
  · have he := (abs_le.mp (henergy n ω)).1
    linarith [le_abs_self (cdfGapProcess ν ν' E δ θ φ n ω)]
  · exact le_add_of_nonneg_right hη

theorem cdfKilledGapProcess_scaled_occupation_le_of_norm (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ η M K : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (hη : 0 ≤ η)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (henergy : ∀ n ω, |cdfGapProcess ν ν' E δ θ φ n ω -
      cdfSameEnergyGapProcess ν E δ θ φ n ω| ≤ η)
    (hmean : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M)
    (hnorm : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfKilledNormProcess ν ν' E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ K) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfKilledGapProcess ν E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ K + η * M := by
  let T := canonicalCrossingTime E δ θ φ
  let c := Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)
  let B := cdfKilledGapProcess ν E δ θ φ
  let A := cdfKilledNormProcess ν ν' E δ θ φ
  have hc : 0 ≤ c := (mul_pos Real.pi_pos hp).le
  have hTm : Measurable T := canonicalCrossingTime_measurable E δ θ φ
  obtain ⟨_, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  change Integrable (fun ω => (((T ω).untopD 0 : ℕ) : ℝ)) (iidMeasure law) at hiT
  have hiB : Integrable (fun ω => Occupation.sumBefore B ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    integrable_cdfKilledGap_sum law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  have hiA : Integrable (fun ω => Occupation.sumBefore A ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    Occupation.integrable_stoppedSum A (measurable_cdfKilledNormProcess ν ν' E δ θ φ)
      hTm hiT (cdfKilledNormProcess_nonneg ν ν' E δ θ φ)
      (fun n ω => (cdfKilledNormProcess_le_gap_add ν ν' E δ θ φ η hδ hinit hη
        henergy n ω).trans (add_le_add
          (cdfKilledGapProcess_bounds ν E δ θ φ hδ hinit n ω).2 le_rfl))
  have hsum : ∀ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ≤
      Occupation.sumBefore A ((T ω).untopD 0) ω + η * (((T ω).untopD 0 : ℕ) : ℝ) := by
    intro ω
    have h := Occupation.sumBefore_le_affine B A (fun _ _ => 0) η 1 0
      (fun n ω => by
        simpa only [one_mul, zero_mul, add_zero, zero_add, add_comm] using
          cdfKilledGapProcess_le_norm_add ν ν' E δ θ φ η hη henergy n ω)
      ((T ω).untopD 0) ω
    simpa only [one_mul, zero_mul, add_zero, zero_add, add_comm] using h
  have hInt : (∫ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ∂iidMeasure law) ≤
      (∫ ω, Occupation.sumBefore A ((T ω).untopD 0) ω ∂iidMeasure law) +
        η * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) := by
    calc
      _ ≤ ∫ ω, Occupation.sumBefore A ((T ω).untopD 0) ω +
          η * (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law :=
        integral_mono_ae hiB (hiA.add (hiT.const_mul η)) (ae_of_all _ hsum)
      _ = _ := by rw [integral_add hiA (hiT.const_mul η), integral_const_mul]
  calc
    _ ≤ c * ((∫ ω, Occupation.sumBefore A ((T ω).untopD 0) ω ∂iidMeasure law) +
        η * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) :=
      mul_le_mul_of_nonneg_left hInt hc
    _ = c * (∫ ω, Occupation.sumBefore A ((T ω).untopD 0) ω ∂iidMeasure law) +
        η * (c * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) := by ring
    _ ≤ K + η * M := add_le_add hnorm (mul_le_mul_of_nonneg_left hmean hη)

theorem inverseCDFKilledGap_occupation_uniform (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, Occupation.sumBefore
            (cdfKilledGapProcess (input.atEnergy E).inverseMeasure E δ θ φ)
            ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ ε := by
  let M : ℝ := 5 * Real.pi + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let r : ℝ := ε / (2 * (M + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨d0, hd0, hnorm⟩ := inverseCDFKilledNorm_occupation_uniform law input hK hr
  obtain ⟨d1, hd1, henergy⟩ := inverseCDFGap_energy_error_uniform law input hK hr
  refine ⟨min 1 (min d0 d1), lt_min zero_lt_one (lt_min hd0 hd1), ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  have hδ1 : δ < 1 := hδd.trans_le (min_le_left _ _)
  have htail : δ < min d0 d1 := hδd.trans_le (min_le_right _ _)
  have hmean : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M :=
    (canonicalCrossingTime_scaled_mean_le law (input.atEnergy E).inverseMeasure
      (input.atEnergy (E + δ)).inverseMeasure E δ θ φ
      (input.atEnergy E).inverse_stationary (input.atEnergy (E + δ)).inverse_stationary
      hδ hinit hsmall.le hp).trans (add_le_add le_rfl hδ1.le)
  have hbound := cdfKilledGapProcess_scaled_occupation_le_of_norm law
    (input.atEnergy E).inverseMeasure (input.atEnergy (E + δ)).inverseMeasure
    E δ θ φ r M r (input.atEnergy E).inverse_stationary
    (input.atEnergy (E + δ)).inverse_stationary hδ hinit hsmall.le hr.le hp
    (fun n ω => (henergy E hE δ hδ hE' (htail.trans_le (min_le_right _ _)) θ φ n ω).le)
    hmean (hnorm E hE δ hδ hE' (htail.trans_le (min_le_left _ _)) θ φ hinit hsmall hp)
  apply hbound.trans
  have heq : r + r * M = ε / 2 := by
    dsimp [r]
    field_simp [show M + 1 ≠ 0 by positivity]
    <;> ring
  rw [heq]
  exact (half_lt_self hε).le

end FixedCouplingPoisson.Furstenberg
