import FixedCouplingPoisson.CanonicalResidual
import FixedCouplingPoisson.CDFMean
import FixedCouplingPoisson.IIDMarkov
import FixedCouplingPoisson.UpperLayer


/-! The actual residual phase pair and its deterministic-time restart. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

def canonicalResidualState (E δ θ φ : ℝ) (j : ℕ) (ω : PotentialSpace) : ℝ × ℝ :=
  (canonicalPhaseProcess E θ j ω,
    canonicalPhaseProcess (E + δ) φ j ω +
      (canonicalCrossingCount E δ θ φ j ω : ℝ) * Real.pi)

theorem canonicalResidualState_past_measurable (E δ θ φ : ℝ) (j : ℕ) :
    Measurable[pastMeasurableSpace j] (canonicalResidualState E δ θ φ j) := by
  have hk : Measurable[pastMeasurableSpace j]
      (fun ω => (canonicalCrossingCount E δ θ φ j ω : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      (canonicalCrossingCount_past_measurable E δ θ φ j)
  exact (canonicalPhaseProcess_past_measurable E θ j).prodMk
    ((canonicalPhaseProcess_past_measurable (E + δ) φ j).add (hk.mul_const Real.pi))

theorem canonicalResidualState_measurable (E δ θ φ : ℝ) (j : ℕ) :
    Measurable (canonicalResidualState E δ θ φ j) :=
  (canonicalResidualState_past_measurable E δ θ φ j).mono
    (pastMeasurableSpace_le j) le_rfl

theorem canonicalResidualState_gap (E δ θ φ : ℝ) (j : ℕ) (ω : PotentialSpace) :
    (canonicalResidualState E δ θ φ j ω).1 -
      (canonicalResidualState E δ θ φ j ω).2 =
        canonicalCrossingResidual E δ θ φ j ω := by
  unfold canonicalResidualState canonicalCrossingResidual canonicalGapProcess
  ring

theorem canonicalResidualState_gap_mem (E δ θ φ : ℝ) (j : ℕ) (ω : PotentialSpace) :
    (canonicalResidualState E δ θ φ j ω).1 -
      (canonicalResidualState E δ θ φ j ω).2 ∈ Ico 0 Real.pi := by
  rw [canonicalResidualState_gap]
  exact canonicalCrossingResidual_mem E δ θ φ j ω

/-- An actual fresh first crossing is precisely an increase of the integer
crossing count over this deterministic future interval. -/
theorem canonicalResidualState_crossing_le_iff (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (j L : ℕ) (ω : PotentialSpace) :
    canonicalCrossingTime E δ (canonicalResidualState E δ θ φ j ω).1
      (canonicalResidualState E δ θ φ j ω).2 (potentialShift j ω) ≤ L ↔
        canonicalCrossingCount E δ θ φ j ω <
          canonicalCrossingCount E δ θ φ (j + L) ω := by
  unfold canonicalResidualState
  rw [canonicalCrossingTime_le_iff_gap _ _ _ _ hδ, canonicalGapProcess_restart]
  change Real.pi ≤ canonicalGapProcess E δ θ φ (j + L) ω -
    (canonicalCrossingCount E δ θ φ j ω : ℝ) * Real.pi ↔
      canonicalCrossingCount E δ θ φ j ω <
        ⌊canonicalGapProcess E δ θ φ (j + L) ω / Real.pi⌋
  rw [show canonicalCrossingCount E δ θ φ j ω <
      ⌊canonicalGapProcess E δ θ φ (j + L) ω / Real.pi⌋ ↔
    canonicalCrossingCount E δ θ φ j ω + 1 ≤
      ⌊canonicalGapProcess E δ θ φ (j + L) ω / Real.pi⌋ by omega, Int.le_floor]
  rw [le_div_iff₀ Real.pi_pos]
  push_cast
  constructor <;> intro h <;> nlinarith

theorem canonicalResidualState_survival_iff (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (j L : ℕ) (ω : PotentialSpace) :
    (L : WithTop ℕ) < canonicalCrossingTime E δ
      (canonicalResidualState E δ θ φ j ω).1
      (canonicalResidualState E δ θ φ j ω).2 (potentialShift j ω) ↔
        canonicalCrossingCount E δ θ φ (j + L) ω ≤
          canonicalCrossingCount E δ θ φ j ω := by
  have h := not_congr (canonicalResidualState_crossing_le_iff E δ θ φ hδ j L ω)
  simpa only [not_le, not_lt] using h

end FixedCouplingPoisson.Furstenberg


/-! Fresh-iid survival probabilities for actual upper-layer initial states. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter

/-- Markov's inequality with the actual possibly infinite crossing time.
Its almost-sure finiteness is used explicitly before the default is removed. -/
theorem canonicalCrossingTime_survival_le_scaled_mean (law : PotentialLaw)
    (E δ θ φ : ℝ) (L : ℕ) (p a : ℝ) (hp : 0 ≤ p) (ha : 0 < a)
    (hL : a ≤ p * (L : ℝ))
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤)
    (hi : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    iidMeasure law {ω | (L : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω} ≤
      ENNReal.ofReal ((p / a) * canonicalCrossingMean law E δ θ φ) := by
  let f := fun ω => (p / a) *
    (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)
  have hf : Integrable f (iidMeasure law) := hi.const_mul _
  have hsub : {ω | (L : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω} ≤ᵐ[iidMeasure law]
      {ω | 1 ≤ f ω} := by
    filter_upwards [hfinite] with ω hω
    intro hsurv
    change (L : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω at hsurv
    change 1 ≤ f ω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    have hLn : L ≤ n := by
      rw [← hn] at hsurv
      exact (WithTop.coe_lt_coe.mp hsurv).le
    have hpn : a ≤ p * (n : ℝ) :=
      hL.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hLn) hp)
    dsimp only [f]
    rw [← hn, WithTop.untopD_coe]
    calc
      1 = a / a := (div_self ha.ne').symm
      _ ≤ (p * (n : ℝ)) / a := div_le_div_of_nonneg_right hpn ha.le
      _ = (p / a) * (n : ℝ) := by ring
  have hmarkov := hf.measure_le_integral
    (Eventually.of_forall fun ω => mul_nonneg (div_nonneg hp ha.le) (Nat.cast_nonneg _))
    (s := {ω | 1 ≤ f ω}) (fun _ h => h)
  rw [integral_const_mul] at hmarkov
  exact (measure_mono_ae hsub).trans hmarkov

/-- For any positive lower bound on scaled horizon, an initial gap near
π has uniformly small probability of making no fresh crossing. -/
theorem inverseCrossingTime_upper_survival_uniform (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi → |θ - φ - Real.pi| < d →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        ∀ L : ℕ, a ≤ (idsCandidate law (E + δ) - idsCandidate law E) * (L : ℝ) →
          iidMeasure law {ω | (L : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω} ≤
            ENNReal.ofReal ε := by
  obtain ⟨d, hd, hmean⟩ := inverseCrossingMean_upper_layer_uniform law input hK
    (mul_pos hε ha)
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hclose hp L hL
  obtain ⟨hfinite, hi, _⟩ := canonicalCrossingTime_finite_mean_IDS law
    (input.atEnergy E).inverseMeasure (input.atEnergy (E + δ)).inverseMeasure
    E δ θ φ (input.atEnergy E).inverse_stationary
    (input.atEnergy (E + δ)).inverse_stationary hδ hinit hsmall.le hp
  have hm := hmean E hE δ hδ hE' hδd θ φ hinit hsmall hclose hp
  have hb := canonicalCrossingTime_survival_le_scaled_mean law E δ θ φ L _ a hp.le ha hL
    hfinite hi
  apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have heq : ((idsCandidate law (E + δ) - idsCandidate law E) / a) *
      canonicalCrossingMean law E δ θ φ =
        ((idsCandidate law (E + δ) - idsCandidate law E) *
          canonicalCrossingMean law E δ θ φ) / a := by ring
  rw [heq]
  exact (div_le_iff₀ ha).mpr hm

end FixedCouplingPoisson.Furstenberg


/-! Actual deterministic-past upper-residual bounds from fresh iid survival. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

theorem iidMeasure_residual_state_future_map (law : PotentialLaw)
    (E δ θ φ : ℝ) (j : ℕ) :
    (iidMeasure law).map (fun ω =>
      (canonicalResidualState E δ θ φ j ω, potentialShift j ω)) =
        ((iidMeasure law).map (canonicalResidualState E δ θ φ j)).prod (iidMeasure law) := by
  have hτ := isStoppingTime_const potentialFiltration j
  have hfinite : ∀ᵐ ω ∂iidMeasure law,
      (fun _ : PotentialSpace => (j : WithTop ℕ)) ω ≠ ⊤ :=
    Eventually.of_forall fun _ => WithTop.coe_ne_top
  have hspace : hτ.measurableSpace = pastMeasurableSpace j :=
    IsStoppingTime.measurableSpace_const potentialFiltration j
  have hX : Measurable[hτ.measurableSpace] (canonicalResidualState E δ θ φ j) := by
    rw [hspace]
    exact canonicalResidualState_past_measurable E δ θ φ j
  simpa only [stoppedPotentialFuture, WithTop.untopD_coe] using
    iidMeasure_stopped_state_future_map law hτ hfinite hX

/-- A uniform bound for fresh deterministic states transfers to the actual
past-dependent recentered state through the proved state/future product law. -/
theorem iidMeasure_upper_residual_survival_le (law : PotentialLaw)
    (E δ θ φ h : ℝ) (hδ : 0 ≤ δ) (j L : ℕ) (b : ℝ≥0∞)
    (hkernel : ∀ x : ℝ × ℝ, x.1 - x.2 ∈ Ico 0 Real.pi →
      Real.pi - h ≤ x.1 - x.2 →
        iidMeasure law {ξ | (L : WithTop ℕ) < canonicalCrossingTime E δ x.1 x.2 ξ} ≤ b) :
    iidMeasure law {ω | Real.pi - h ≤ canonicalCrossingResidual E δ θ φ j ω ∧
      canonicalCrossingCount E δ θ φ (j + L) ω ≤ canonicalCrossingCount E δ θ φ j ω} ≤ b := by
  let X := canonicalResidualState E δ θ φ j
  let A : Set ((ℝ × ℝ) × PotentialSpace) :=
    {z | Real.pi - h ≤ z.1.1 - z.1.2 ∧
      (L : WithTop ℕ) < canonicalCrossingTime E δ z.1.1 z.1.2 z.2}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const (measurable_fst.fst.sub measurable_fst.snd)).inter
      (measurableSet_lt measurable_const (canonicalCrossingTime_measurable_initial_path E δ))
  have hXm : Measurable X := canonicalResidualState_measurable E δ θ φ j
  have hpair : Measurable (fun ω => (X ω, potentialShift j ω)) :=
    hXm.prodMk (measurable_potentialShift j)
  have heq : {ω | Real.pi - h ≤ canonicalCrossingResidual E δ θ φ j ω ∧
      canonicalCrossingCount E δ θ φ (j + L) ω ≤ canonicalCrossingCount E δ θ φ j ω} =
        (fun ω => (X ω, potentialShift j ω)) ⁻¹' A := by
    ext ω
    change (_ ∧ _) ↔ (Real.pi - h ≤ (X ω).1 - (X ω).2 ∧ _)
    rw [canonicalResidualState_gap, canonicalResidualState_survival_iff E δ θ φ hδ]
  rw [heq, ← Measure.map_apply hpair hA, iidMeasure_residual_state_future_map,
    Measure.prod_apply hA]
  have hsupport : ∀ᵐ x ∂(iidMeasure law).map X, x.1 - x.2 ∈ Ico 0 Real.pi := by
    apply (ae_map_iff hXm.aemeasurable
      ((measurableSet_Ico.preimage (measurable_fst.sub measurable_snd)))).mpr
    exact Eventually.of_forall fun ω => canonicalResidualState_gap_mem E δ θ φ j ω
  have hbound : (∫⁻ x, iidMeasure law (Prod.mk x ⁻¹' A) ∂(iidMeasure law).map X) ≤
      ∫⁻ _x, b ∂(iidMeasure law).map X := by
    apply lintegral_mono_ae
    filter_upwards [hsupport] with x hx
    by_cases hnear : Real.pi - h ≤ x.1 - x.2
    · have heq : Prod.mk x ⁻¹' A =
          {ξ | (L : WithTop ℕ) < canonicalCrossingTime E δ x.1 x.2 ξ} := by
        ext ξ
        exact and_iff_right hnear
      rw [heq]
      exact hkernel x hx hnear
    · have heq : Prod.mk x ⁻¹' A = ∅ := by
        ext ξ
        simp only [A, mem_preimage, mem_setOf_eq, not_false_eq_true, mem_empty_iff_false,
          iff_false, not_and]
        exact fun h => (hnear h).elim
      rw [heq, measure_empty]
      exact bot_le
  haveI : IsProbabilityMeasure ((iidMeasure law).map X) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  simpa only [lintegral_const, measure_univ, mul_one] using hbound

/-- The upper residual probability is bounded by an actual crossing in the
subsequent interval plus a uniformly small survival error. -/
theorem inverse_upper_residual_probability_uniform (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, 0 < idsCandidate law (E + δ) - idsCandidate law E →
      ∀ j L : ℕ, a ≤ (idsCandidate law (E + δ) - idsCandidate law E) * (L : ℝ) →
        iidMeasure law {ω | Real.pi - d / 2 ≤ canonicalCrossingResidual E δ θ φ j ω} ≤
          iidMeasure law {ω | canonicalCrossingCount E δ θ φ j ω <
            canonicalCrossingCount E δ θ φ (j + L) ω} + ENNReal.ofReal ε := by
  obtain ⟨d, hd, hsurv⟩ := inverseCrossingTime_upper_survival_uniform law input hK hε ha
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hp j L hL
  have hkernel : ∀ x : ℝ × ℝ, x.1 - x.2 ∈ Ico 0 Real.pi →
      Real.pi - d / 2 ≤ x.1 - x.2 →
        iidMeasure law {ξ | (L : WithTop ℕ) < canonicalCrossingTime E δ x.1 x.2 ξ} ≤
          ENNReal.ofReal ε := by
    intro x hx hnear
    apply hsurv E hE δ hδ hE' hδd x.1 x.2 (sub_nonneg.mp hx.1) hx.2 ?_ hp L hL
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2.le)]
    linarith
  have hb := iidMeasure_upper_residual_survival_le law E δ θ φ (d / 2) hδ j L
    (ENNReal.ofReal ε) hkernel
  have hsub : {ω | Real.pi - d / 2 ≤ canonicalCrossingResidual E δ θ φ j ω} ⊆
        {ω | canonicalCrossingCount E δ θ φ j ω <
          canonicalCrossingCount E δ θ φ (j + L) ω} ∪
        {ω | Real.pi - d / 2 ≤ canonicalCrossingResidual E δ θ φ j ω ∧
          canonicalCrossingCount E δ θ φ (j + L) ω ≤ canonicalCrossingCount E δ θ φ j ω} := by
    intro ω hω
    by_cases hinc : canonicalCrossingCount E δ θ φ j ω <
          canonicalCrossingCount E δ θ φ (j + L) ω
    · exact Or.inl hinc
    · exact Or.inr ⟨hω, le_of_not_gt hinc⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hb))

end FixedCouplingPoisson.Furstenberg
