import FixedCouplingPoisson.CDFExitUniform

/-! The uniform affine Laplace profile in the manuscript's same-energy
initial coordinate follows from the proved exact-drift profile and the
compact-energy CDF modulus. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

theorem inverseCrossingLaplace_sameEnergy_profile_uniform (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    {q : ℝ} (hq : 0 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(∫ ω, Real.exp
            (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
              (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law) -
          (1 + q * cdfSameEnergyGap (input.atEnergy E).inverseMeasure θ φ) /
            (1 + q * Real.pi)| ≤ ε := by
  let ν : ℝ → ProbabilityMeasure ProjectivePoint :=
    fun E => (input.atEnergy E).inverseMeasure
  have hweak : Continuous ν := continuous_selected_inverseMeasure law input
  have hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0 :=
    fun E => (input.atEnergy E).inverse_null_singletons
  let r : ℝ := ε / (2 * (q + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨d0, hd0, hprofile⟩ := inverseCrossingLaplace_profile_uniform
    law input hK hq (half_pos hε)
  obtain ⟨d1, hd1, henergy⟩ := stationaryCDFLift_energy_uniform ν hweak hatom hK hr
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  have hEE' : |E - (E + δ)| < d1 := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using
      hδd.trans_le (min_le_right _ _)
  let w : ℝ := stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ
  let b : ℝ := cdfSameEnergyGap (ν E) θ φ
  let L : ℝ := ∫ ω, Real.exp
    (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
      (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law
  have hmain := hprofile E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
    θ φ hinit hsmall hp
  change |L - (1 + q * w) / (1 + q * Real.pi)| ≤ ε / 2 at hmain
  change |L - (1 + q * b) / (1 + q * Real.pi)| ≤ ε
  have hw : |w - b| ≤ r := by
    have heq : w - b = stationaryCDFLift (ν E) φ -
        stationaryCDFLift (ν (E + δ)) φ := by
      dsimp [w, b, cdfSameEnergyGap]
      ring
    rw [heq]
    exact (henergy E hE (E + δ) hE' hEE' φ).le
  have hden : 0 < 1 + q * Real.pi := by positivity
  have hden1 : 1 ≤ 1 + q * Real.pi :=
    le_add_of_nonneg_right (mul_nonneg hq Real.pi_pos.le)
  have hdiff : |(1 + q * w) / (1 + q * Real.pi) -
      (1 + q * b) / (1 + q * Real.pi)| ≤ ε / 2 := by
    have heq : (1 + q * w) / (1 + q * Real.pi) -
        (1 + q * b) / (1 + q * Real.pi) = q * (w - b) / (1 + q * Real.pi) := by ring
    rw [heq, abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos hden]
    calc
      _ ≤ q * |w - b| := div_le_self (mul_nonneg hq (abs_nonneg _)) hden1
      _ ≤ q * r := mul_le_mul_of_nonneg_left hw hq
      _ ≤ (q + 1) * r :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hr.le
      _ = ε / 2 := by
        dsimp [r]
        field_simp [show q + 1 ≠ 0 by positivity]
        <;> ring
  exact (abs_sub_le L ((1 + q * w) / (1 + q * Real.pi))
    ((1 + q * b) / (1 + q * Real.pi))).trans (by linarith)

end FixedCouplingPoisson.Furstenberg
