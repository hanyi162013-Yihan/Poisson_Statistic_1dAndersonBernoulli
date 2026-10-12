import FixedCouplingPoisson.CDFDynamics


/-! Factored proof group: StoppedSum. -/

/-! Unchecked work draft. Removing a truncation from a nonnegative
stopped occupation is justified by an integrable waiting time. This is
used for the actual pair occupation, after finite mean has been proved. -/
noncomputable section
namespace FixedCouplingPoisson.Occupation
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def stoppingTruncIndex (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) : ℕ :=
  (min (τ ω) (N : WithTop ℕ)).untopD 0

theorem stoppingTruncIndex_coe (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) :
    (stoppingTruncIndex τ N ω : WithTop ℕ) = min (τ ω) (N : WithTop ℕ) := by
  cases h : τ ω with
  | top =>
    simp only [stoppingTruncIndex, h, min_top_left]
    rfl
  | coe n =>
    simp only [stoppingTruncIndex, h]
    rfl

theorem stoppingTruncIndex_le (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) :
    stoppingTruncIndex τ N ω ≤ N := by
  have h := min_le_right (τ ω) (N : WithTop ℕ)
  rw [← stoppingTruncIndex_coe] at h
  exact_mod_cast h

theorem stoppingTruncIndex_le_time (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) :
    (stoppingTruncIndex τ N ω : WithTop ℕ) ≤ τ ω := by
  rw [stoppingTruncIndex_coe]
  exact min_le_left _ _

theorem stoppingTruncIndex_event_iff (τ : Ω → WithTop ℕ) (N j : ℕ) (ω : Ω) :
    j < stoppingTruncIndex τ N ω ↔ (j : WithTop ℕ) < τ ω ∧ j < N := by
  have h : j < stoppingTruncIndex τ N ω ↔
      (j : WithTop ℕ) < (stoppingTruncIndex τ N ω : WithTop ℕ) :=
    WithTop.coe_lt_coe.symm
  exact h.trans (by
    rw [stoppingTruncIndex_coe, lt_min_iff]
    exact and_congr Iff.rfl WithTop.coe_lt_coe)

theorem stoppingTruncIndex_event_measurable
    {F : Filtration ℕ ‹MeasurableSpace Ω›} {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime F τ) (N j : ℕ) :
    MeasurableSet[F j] {ω | j < stoppingTruncIndex τ N ω} := by
  have heq : {ω | j < stoppingTruncIndex τ N ω} =
      {ω | (j : WithTop ℕ) < τ ω} ∩ {ω : Ω | j < N} := by
    ext ω
    exact stoppingTruncIndex_event_iff τ N j ω
  rw [heq]
  exact (hτ.measurableSet_gt j).inter (MeasurableSet.const _)

theorem measurable_stoppingTruncIndex {τ : Ω → WithTop ℕ} (hτ : Measurable τ) (N : ℕ) :
    Measurable (stoppingTruncIndex τ N) :=
  (WithTop.measurable_untopD 0).comp (hτ.min measurable_const)

def sumBefore (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, f j ω

theorem measurable_sumBefore (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j)) (n : ℕ) :
    Measurable (sumBefore f n) := by
  apply Finset.measurable_sum
  intro j _
  exact hf j

theorem sumBefore_nonneg (f : ℕ → Ω → ℝ) (hf : ∀ j ω, 0 ≤ f j ω) (n : ℕ) (ω : Ω) :
    0 ≤ sumBefore f n ω :=
  Finset.sum_nonneg (fun j _ => hf j ω)

theorem sumBefore_le (f : ℕ → Ω → ℝ) {C : ℝ} (hf : ∀ j ω, f j ω ≤ C)
    (n : ℕ) (ω : Ω) : sumBefore f n ω ≤ C * (n : ℝ) := by
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => hf j ω)
  simpa only [sumBefore, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_comm C] using h

theorem norm_sumBefore_le (f : ℕ → Ω → ℝ) {C : ℝ} (hf : ∀ j ω, ‖f j ω‖ ≤ C)
    (n : ℕ) (ω : Ω) : ‖sumBefore f n ω‖ ≤ C * (n : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖f j ω‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, C := Finset.sum_le_sum (fun j _ => hf j ω)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm C]

theorem sumBefore_le_affine (f g u : ℕ → Ω → ℝ) (a b c : ℝ)
    (h : ∀ j ω, f j ω ≤ a + b * g j ω + c * u j ω) (n : ℕ) (ω : Ω) :
    sumBefore f n ω ≤ a * (n : ℝ) + b * sumBefore g n ω + c * sumBefore u n ω := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, (a + b * g j ω + c * u j ω) :=
      Finset.sum_le_sum (fun j _ => h j ω)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, sumBefore]
      ring

/-- A pathwise budget counts every later visit, including returns after
the first threshold entrance. Only the vanishing before entrance matters. -/
theorem sumBefore_le_after (f : ℕ → Ω → ℝ) {C : ℝ}
    (hfC : ∀ j ω, f j ω ≤ C) (k : ℕ) (ω : Ω)
    (hzero : ∀ j < k, f j ω = 0) (n : ℕ) :
    sumBefore f n ω ≤ C * ((n - k : ℕ) : ℝ) := by
  induction n with
  | zero => simp [sumBefore]
  | succ n ih =>
    change (∑ j ∈ Finset.range (n + 1), f j ω) ≤ _
    rw [Finset.sum_range_succ]
    change sumBefore f n ω + f n ω ≤ _
    by_cases hn : k ≤ n
    · rw [Nat.succ_sub hn, Nat.cast_succ]
      calc
        _ ≤ C * ((n - k : ℕ) : ℝ) + C := add_le_add ih (hfC n ω)
        _ = _ := by ring
    · have hnk : n < k := Nat.lt_of_not_ge hn
      rw [hzero n hnk, add_zero, Nat.sub_eq_zero_of_le hnk, Nat.cast_zero, mul_zero]
      simpa only [Nat.sub_eq_zero_of_le (le_of_lt hnk), Nat.cast_zero, mul_zero] using ih

def remainingTime (τ σ : Ω → WithTop ℕ) (ω : Ω) : ℝ :=
  (((τ ω).untopD 0 - (σ ω).untopD 0 : ℕ) : ℝ)

theorem measurable_remainingTime {τ σ : Ω → WithTop ℕ}
    (hτ : Measurable τ) (hσ : Measurable σ) : Measurable (remainingTime τ σ) :=
  (measurable_of_countable (fun z : ℕ × ℕ => ((z.1 - z.2 : ℕ) : ℝ))).comp
    (((WithTop.measurable_untopD 0).comp hτ).prodMk
      ((WithTop.measurable_untopD 0).comp hσ))

theorem remainingTime_nonneg (τ σ : Ω → WithTop ℕ) (ω : Ω) :
    0 ≤ remainingTime τ σ ω := Nat.cast_nonneg _

theorem remainingTime_le (τ σ : Ω → WithTop ℕ) (ω : Ω) :
    remainingTime τ σ ω ≤ (((τ ω).untopD 0 : ℕ) : ℝ) := by
  unfold remainingTime
  exact_mod_cast Nat.sub_le ((τ ω).untopD 0) ((σ ω).untopD 0)

theorem integrable_remainingTime {τ σ : Ω → WithTop ℕ}
    (hτ : Measurable τ) (hσ : Measurable σ)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ) :
    Integrable (remainingTime τ σ) μ := by
  apply hi.mono' (measurable_remainingTime hτ hσ).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (remainingTime_nonneg τ σ ω)]
    exact remainingTime_le τ σ ω

theorem remainingTime_integral_eq_sub {τ σ : Ω → WithTop ℕ}
    (hiτ : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ)
    (hiσ : Integrable (fun ω => (((σ ω).untopD 0 : ℕ) : ℝ)) μ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hle : ∀ᵐ ω ∂μ, σ ω ≤ τ ω) :
    (∫ ω, remainingTime τ σ ω ∂μ) =
      (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ) -
        (∫ ω, (((σ ω).untopD 0 : ℕ) : ℝ) ∂μ) := by
  rw [← integral_sub hiτ hiσ]
  apply integral_congr_ae
  filter_upwards [hfinite, hle] with ω hω hleω
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  have hσfinite : σ ω ≠ ⊤ := ne_top_of_le_ne_top hω hleω
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hσfinite
  have hmn : m ≤ n := by
    rw [← hn, ← hm] at hleω
    exact WithTop.coe_le_coe.mp hleω
  simp only [remainingTime, ← hn, ← hm, WithTop.untopD_coe, Nat.cast_sub hmn]

theorem measurable_sumBefore_random (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    {τ : Ω → ℕ} (hτ : Measurable τ) : Measurable (fun ω => sumBefore f (τ ω) ω) := by
  have hfield : Measurable (fun p : ℕ × Ω => sumBefore f p.1 p.2) :=
    measurable_from_prod_countable_right (fun n => measurable_sumBefore f hf n)
  have hcomp := hfield.comp (hτ.prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using hcomp

theorem integrable_sumBefore_random (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    {τ : Ω → ℕ} (hτ : Measurable τ) (hi : Integrable (fun ω => (τ ω : ℝ)) μ)
    {C : ℝ} (hf0 : ∀ j ω, 0 ≤ f j ω) (hfC : ∀ j ω, f j ω ≤ C) :
    Integrable (fun ω => sumBefore f (τ ω) ω) μ := by
  apply (hi.const_mul C).mono'
    (measurable_sumBefore_random f hf hτ).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sumBefore_nonneg f hf0 _ ω)]
    exact sumBefore_le f hfC _ ω

theorem integrable_stoppedSum (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ)
    {C : ℝ} (hf0 : ∀ j ω, 0 ≤ f j ω) (hfC : ∀ j ω, f j ω ≤ C) :
    Integrable (fun ω => sumBefore f ((τ ω).untopD 0) ω) μ :=
  integrable_sumBefore_random f hf ((WithTop.measurable_untopD 0).comp hτ) hi hf0 hfC

theorem integrable_signed_stoppedSum (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ)
    {C : ℝ} (hfC : ∀ j ω, ‖f j ω‖ ≤ C) :
    Integrable (fun ω => sumBefore f ((τ ω).untopD 0) ω) μ := by
  apply (hi.const_mul C).mono'
    (measurable_sumBefore_random f hf ((WithTop.measurable_untopD 0).comp hτ)).aestronglyMeasurable
  exact ae_of_all _ fun ω => norm_sumBefore_le f hfC _ ω

/-- This limit is used only after the actual waiting time is finite
almost surely and integrable. No optional-stopping integrability is assumed. -/
theorem stoppedSum_integral_tendsto (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ)
    {C : ℝ} (hC : 0 ≤ C) (hf0 : ∀ j ω, 0 ≤ f j ω) (hfC : ∀ j ω, f j ω ≤ C) :
    Tendsto (fun N : ℕ => ∫ ω, sumBefore f ((min (τ ω) (N : WithTop ℕ)).untopD 0) ω ∂μ)
      atTop (𝓝 (∫ ω, sumBefore f ((τ ω).untopD 0) ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun ω => C * (((τ ω).untopD 0 : ℕ) : ℝ))
    (fun N => (measurable_sumBefore_random f hf
      ((WithTop.measurable_untopD 0).comp (hτ.min measurable_const))).aestronglyMeasurable)
    (hi.const_mul C)
  · intro N
    filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    simp only [Function.comp_apply]
    rw [← hn]
    simp only [Nat.cast_withTop, ← WithTop.coe_min, WithTop.untopD_coe]
    rw [Real.norm_eq_abs, abs_of_nonneg (sumBefore_nonneg f hf0 _ ω)]
    exact (sumBefore_le f hfC _ ω).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (min_le_left n N)) hC)
  · filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    simp only [Function.comp_apply]
    rw [← hn]
    simp only [Nat.cast_withTop, ← WithTop.coe_min, WithTop.untopD_coe, min_eq_left hN]

/-- Signed discounted coordinates use the same integrable waiting-time
dominator. Positivity of the summand is not required. -/
theorem stoppedSum_signed_integral_tendsto (f : ℕ → Ω → ℝ) (hf : ∀ j, Measurable (f j))
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ)
    {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ j ω, ‖f j ω‖ ≤ C) :
    Tendsto (fun N : ℕ => ∫ ω, sumBefore f ((min (τ ω) (N : WithTop ℕ)).untopD 0) ω ∂μ)
      atTop (𝓝 (∫ ω, sumBefore f ((τ ω).untopD 0) ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun ω => C * (((τ ω).untopD 0 : ℕ) : ℝ))
    (fun N => (measurable_sumBefore_random f hf
      ((WithTop.measurable_untopD 0).comp (hτ.min measurable_const))).aestronglyMeasurable)
    (hi.const_mul C)
  · intro N
    filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    simp only [Function.comp_apply]
    rw [← hn]
    simp only [Nat.cast_withTop, ← WithTop.coe_min, WithTop.untopD_coe]
    exact (norm_sumBefore_le f hfC _ ω).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (min_le_left n N)) hC)
  · filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    simp only [Function.comp_apply]
    rw [← hn]
    simp only [Nat.cast_withTop, ← WithTop.coe_min, WithTop.untopD_coe, min_eq_left hN]

end FixedCouplingPoisson.Occupation

/-! Factored proof group: CDFStopComparison. -/

/-! Unchecked work draft. The actual CDF drift can be stopped at any
stopping time preceding the first raw crossing. Its coordinate bound and
positive drift prove finite mean before removing the truncation. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

theorem norm_cdfGapProcess_le_of_time_le_crossing
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (n : ℕ) (ω : PotentialSpace)
    (hn : (n : WithTop ℕ) ≤ canonicalCrossingTime E δ θ φ ω) :
    ‖cdfGapProcess ν ν' E δ θ φ n ω‖ ≤ 3 * Real.pi + δ := by
  have ht : crossingTruncIndex E δ θ φ n ω = n := by
    rw [crossingTruncIndex, min_eq_right hn, Nat.cast_withTop]
    rfl
  simpa only [ht] using norm_cdfGapProcess_truncated_le
    ν ν' E δ θ φ hδ hinit hsmall n ω

theorem measurable_cdfGapProcess_randomTime (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) {τ : PotentialSpace → ℕ} (hτ : Measurable τ) :
    Measurable (fun ω => cdfGapProcess ν ν' E δ θ φ (τ ω) ω) :=
  measurable_cdfGapProcess_randomNat ν ν' E δ θ φ hτ

theorem integrable_cdfGapProcess_random_trunc (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    {τ : PotentialSpace → WithTop ℕ} (hτm : Measurable τ)
    (hτle : ∀ ω, τ ω ≤ canonicalCrossingTime E δ θ φ ω) (N : ℕ) :
    Integrable (fun ω => cdfGapProcess ν ν' E δ θ φ
      (Occupation.stoppingTruncIndex τ N ω) ω) (iidMeasure law) := by
  apply (integrable_const (μ := iidMeasure law) (3 * Real.pi + δ)).mono'
    (measurable_cdfGapProcess_randomTime ν ν' E δ θ φ
      (Occupation.measurable_stoppingTruncIndex hτm N)).aestronglyMeasurable
  exact ae_of_all _ fun ω => norm_cdfGapProcess_le_of_time_le_crossing
    ν ν' E δ θ φ hδ hinit hsmall _ ω
    ((Occupation.stoppingTruncIndex_le_time τ N ω).trans (hτle ω))

theorem integrable_cdfGapProcess_randomTime (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    {τ : PotentialSpace → WithTop ℕ} (hτm : Measurable τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    (hτle : ∀ ω, τ ω ≤ canonicalCrossingTime E δ θ φ ω) :
    Integrable (fun ω => cdfGapProcess ν ν' E δ θ φ ((τ ω).untopD 0) ω)
      (iidMeasure law) := by
  apply (integrable_const (μ := iidMeasure law) (3 * Real.pi + δ)).mono'
    (measurable_cdfGapProcess_randomTime ν ν' E δ θ φ
      ((WithTop.measurable_untopD 0).comp hτm)).aestronglyMeasurable
  filter_upwards [hfinite] with ω hω
  simp only [Function.comp_apply]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  have hle : (n : WithTop ℕ) ≤ canonicalCrossingTime E δ θ φ ω := by
    simpa only [← hn, Nat.cast_withTop] using hτle ω
  simpa only [← hn, WithTop.untopD_coe] using norm_cdfGapProcess_le_of_time_le_crossing
    ν ν' E δ θ φ hδ hinit hsmall n ω hle

theorem cdfGapProcess_bounded_stopped_IDS_of_le_crossing (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hτm : Measurable τ) (hτle : ∀ ω, τ ω ≤ canonicalCrossingTime E δ θ φ ω) (N : ℕ) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
        (∫ ω, Occupation.truncatedTime τ N ω ∂iidMeasure law) =
      (∫ ω, cdfGapProcess ν ν' E δ θ φ
        (Occupation.stoppingTruncIndex τ N ω) ω ∂iidMeasure law) -
        (stationaryCDFLift ν θ - stationaryCDFLift ν' φ) := by
  have h := Occupation.bounded_stopped_drift_identity
    pastMeasurableSpace pastMeasurableSpace_le (Occupation.stoppingTruncIndex τ N) N
    (Occupation.stoppingTruncIndex_le τ N)
    (Occupation.stoppingTruncIndex_event_measurable hτ N)
    (cdfGapProcess ν ν' E δ θ φ) (integrable_cdfGapProcess law ν ν' E δ θ φ)
    (integrable_cdfGapProcess_random_trunc law ν ν' E δ θ φ hδ hinit hsmall hτm hτle N)
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))
    (fun j _ => cdfGapProcess_condExp_IDS law ν ν' E δ θ φ hν hν' j)
  have htr : Occupation.truncatedTime τ N =
      (fun ω => (Occupation.stoppingTruncIndex τ N ω : ℝ)) := rfl
  have hzero : (fun ω => cdfGapProcess ν ν' E δ θ φ 0 ω) =
      (fun _ω : PotentialSpace => stationaryCDFLift ν θ - stationaryCDFLift ν' φ) :=
    funext (cdfGapProcess_zero ν ν' E δ θ φ)
  rw [htr]
  rw [hzero] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- The same proved IDS drift applies at every preceding actual stopping
time. No fresh-future law or extra Markov hypothesis is required here. -/
theorem cdfGapProcess_stopped_IDS_of_le_crossing (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hτm : Measurable τ) (hτle : ∀ ω, τ ω ≤ canonicalCrossingTime E δ θ φ ω) :
    (∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) ∧
      Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) (iidMeasure law) ∧
      (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) =
        (∫ ω, cdfGapProcess ν ν' E δ θ φ ((τ ω).untopD 0) ω ∂iidMeasure law) -
          (stationaryCDFLift ν θ - stationaryCDFLift ν' φ) := by
  apply Occupation.finite_mean_and_stopped_identity hτm (cdfGapProcess ν ν' E δ θ φ)
    (mul_pos Real.pi_pos hp)
  · intro N
    exact (measurable_cdfGapProcess_randomTime ν ν' E δ θ φ
      (Occupation.measurable_stoppingTruncIndex hτm N)).aestronglyMeasurable
  · intro N
    exact ae_of_all _ fun ω => norm_cdfGapProcess_le_of_time_le_crossing
      ν ν' E δ θ φ hδ hinit hsmall _ ω
      ((Occupation.stoppingTruncIndex_le_time τ N ω).trans (hτle ω))
  · exact cdfGapProcess_bounded_stopped_IDS_of_le_crossing law ν ν' E δ θ φ
      hν hν' hδ hinit hsmall hτ hτm hτle

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFThreshold. -/

/-! Unchecked work draft. A first upper threshold of the actual exact-drift
CDF coordinate controls all remaining time by two stopped identities.
The argument includes returns below the threshold after its first hit. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set

def cdfThresholdTime (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) : PotentialSpace → WithTop ℕ :=
  hittingAfter (cdfGapProcess ν ν' E δ θ φ) (Ici (Real.pi - a)) 0

theorem cdfGapProcess_adapted (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) : Adapted potentialFiltration (cdfGapProcess ν ν' E δ θ φ) :=
  fun n => (cdfProcess_past_measurable ν E θ n).sub
    (cdfProcess_past_measurable ν' (E + δ) φ n)

theorem cdfThresholdTime_isStoppingTime (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) :
    IsStoppingTime potentialFiltration (cdfThresholdTime ν ν' E δ θ φ a) :=
  (cdfGapProcess_adapted ν ν' E δ θ φ).isStoppingTime_hittingAfter measurableSet_Ici

theorem cdfThresholdTime_measurable (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) : Measurable (cdfThresholdTime ν ν' E δ θ φ a) := by
  apply measurable_of_Iic
  intro n
  induction n using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    exact pastMeasurableSpace_le n _
      ((cdfThresholdTime_isStoppingTime ν ν' E δ θ φ a).measurableSet_le n)

theorem cdfThresholdTime_le_of_mem (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω) :
    cdfThresholdTime ν ν' E δ θ φ a ω ≤ n :=
  hittingAfter_le_of_mem (Nat.zero_le n) hn

theorem cdfThresholdTime_le_crossing (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ)
    (hexit : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω) (ω : PotentialSpace) :
    cdfThresholdTime ν ν' E δ θ φ a ω ≤ canonicalCrossingTime E δ θ φ ω := by
  cases ht : canonicalCrossingTime E δ θ φ ω with
  | top => exact le_top
  | coe n =>
    exact cdfThresholdTime_le_of_mem ν ν' E δ θ φ a n ω (hexit ω n ht)

theorem cdfThresholdTime_hits (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : cdfThresholdTime ν ν' E δ θ φ a ω = n) :
    Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω := by
  have hfinite : cdfThresholdTime ν ν' E δ θ φ a ω ≠ ⊤ := by
    rw [hn]
    exact WithTop.coe_ne_top
  have hm : cdfGapProcess ν ν' E δ θ φ
      (cdfThresholdTime ν ν' E δ θ φ a ω).untopA ω ∈ Ici (Real.pi - a) :=
    hittingAfter_mem_set_of_ne_top hfinite
  rw [hn] at hm
  simp only [Nat.cast_withTop] at hm
  change Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω at hm
  exact hm

/-- Counts every visit above the threshold, rather than only the first
consecutive run there. -/
def cdfUpperVisit (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  if Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω then 1 else 0

theorem measurable_cdfUpperVisit (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) : Measurable (cdfUpperVisit ν ν' E δ θ φ a n) :=
  measurable_const.ite
    (measurableSet_le measurable_const (measurable_cdfGapProcess ν ν' E δ θ φ n))
    measurable_const

theorem cdfUpperVisit_nonneg (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) (ω : PotentialSpace) :
    0 ≤ cdfUpperVisit ν ν' E δ θ φ a n ω := by
  simp only [cdfUpperVisit]
  split_ifs <;> norm_num

theorem cdfUpperVisit_le_one (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) (ω : PotentialSpace) :
    cdfUpperVisit ν ν' E δ θ φ a n ω ≤ 1 := by
  simp only [cdfUpperVisit]
  split_ifs <;> norm_num

theorem cdfUpperVisit_eq_zero_before (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : (n : WithTop ℕ) < cdfThresholdTime ν ν' E δ θ φ a ω) :
    cdfUpperVisit ν ν' E δ θ φ a n ω = 0 := by
  have hnot : ¬ Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω := fun hm =>
    (not_le_of_gt hn) (cdfThresholdTime_le_of_mem ν ν' E δ θ φ a n ω hm)
  simp only [cdfUpperVisit, if_neg hnot]

theorem cdfUpperVisit_sum_le_remaining (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ a : ℝ) (ω : PotentialSpace)
    (hfiniteσ : cdfThresholdTime ν ν' E δ θ φ a ω ≠ ⊤) :
    Occupation.sumBefore (cdfUpperVisit ν ν' E δ θ φ a)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ≤
      Occupation.remainingTime (canonicalCrossingTime E δ θ φ)
        (cdfThresholdTime ν ν' E δ θ φ a) ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfiniteσ
  have hzero : ∀ j < k, cdfUpperVisit ν ν' E δ θ φ a j ω = 0 := by
    intro j hj
    apply cdfUpperVisit_eq_zero_before
    rw [← hk]
    simp only [Nat.cast_withTop]
    exact WithTop.coe_lt_coe.mpr hj
  simpa only [Occupation.remainingTime, ← hk, WithTop.untopD_coe, one_mul] using
    Occupation.sumBefore_le_after (cdfUpperVisit ν ν' E δ θ φ a)
      (cdfUpperVisit_le_one ν ν' E δ θ φ a) k ω hzero
      ((canonicalCrossingTime E δ θ φ ω).untopD 0)

/-- These two stopped means control the whole future after the first
upper threshold. There is no monotonicity assumption on the CDF process. -/
theorem cdfThresholdTime_remaining_mean_le (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ a b : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (hexitLower : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω)
    (hexitUpper : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      cdfGapProcess ν ν' E δ θ φ n ω ≤ Real.pi + b) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      ((∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) -
        (∫ ω, (((cdfThresholdTime ν ν' E δ θ φ a ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) ≤ a + b := by
  let σ := cdfThresholdTime ν ν' E δ θ φ a
  have hσ := cdfThresholdTime_isStoppingTime ν ν' E δ θ φ a
  have hσm := cdfThresholdTime_measurable ν ν' E δ θ φ a
  have hσle : ∀ ω, σ ω ≤ canonicalCrossingTime E δ θ φ ω :=
    cdfThresholdTime_le_crossing ν ν' E δ θ φ a hexitLower
  obtain ⟨hfiniteT, _, hidT⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  obtain ⟨hfiniteσ, _, hidσ⟩ := cdfGapProcess_stopped_IDS_of_le_crossing law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp hσ hσm hσle
  have hiT := integrable_cdfGapProcess_atCrossing law ν ν'
    E δ θ φ hδ hinit hsmall hfiniteT
  have hiσ := integrable_cdfGapProcess_randomTime law ν ν'
    E δ θ φ hδ hinit hsmall hσm hfiniteσ hσle
  have hTupper : (∫ ω, cdfGapProcess ν ν' E δ θ φ
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ Real.pi + b := by
    calc
      _ ≤ ∫ _ω : PotentialSpace, Real.pi + b ∂iidMeasure law :=
        integral_mono_ae hiT (integrable_const _) (by
          filter_upwards [hfiniteT] with ω hω
          obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
          simpa only [← hn, WithTop.untopD_coe] using hexitUpper ω n hn.symm)
      _ = _ := by simp
  have hσlower : Real.pi - a ≤ (∫ ω, cdfGapProcess ν ν' E δ θ φ
      ((σ ω).untopD 0) ω ∂iidMeasure law) := by
    calc
      _ = ∫ _ω : PotentialSpace, Real.pi - a ∂iidMeasure law := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hiσ (by
        filter_upwards [hfiniteσ] with ω hω
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
        have hh := cdfThresholdTime_hits ν ν' E δ θ φ a n ω hn.symm
        simpa only [← hn, WithTop.untopD_coe] using hh)
  calc
    _ = (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) -
        (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((σ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) := mul_sub _ _ _
    _ = (∫ ω, cdfGapProcess ν ν' E δ θ φ
          ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) -
        (∫ ω, cdfGapProcess ν ν' E δ θ φ ((σ ω).untopD 0) ω ∂iidMeasure law) := by
      rw [hidT, hidσ]
      ring
    _ ≤ (Real.pi + b) - (Real.pi - a) := sub_le_sub hTupper hσlower
    _ = a + b := by ring

/-- The expected number of all upper visits has the same small scaled
budget as the entire time after the first threshold hit. -/
theorem cdfUpperVisit_occupation_IDS_le (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ a b : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (hexitLower : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω)
    (hexitUpper : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      cdfGapProcess ν ν' E δ θ φ n ω ≤ Real.pi + b) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfUpperVisit ν ν' E δ θ φ a)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ a + b := by
  let T := canonicalCrossingTime E δ θ φ
  let σ := cdfThresholdTime ν ν' E δ θ φ a
  have hTm : Measurable T := canonicalCrossingTime_measurable E δ θ φ
  have hσm : Measurable σ := cdfThresholdTime_measurable ν ν' E δ θ φ a
  have hσle : ∀ ω, σ ω ≤ T ω :=
    cdfThresholdTime_le_crossing ν ν' E δ θ φ a hexitLower
  obtain ⟨hfiniteT, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  obtain ⟨hfiniteσ, hiσ, _⟩ := cdfGapProcess_stopped_IDS_of_le_crossing law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
    (cdfThresholdTime_isStoppingTime ν ν' E δ θ φ a) hσm hσle
  have hiV := Occupation.integrable_stoppedSum (cdfUpperVisit ν ν' E δ θ φ a)
    (measurable_cdfUpperVisit ν ν' E δ θ φ a) hTm hiT
    (cdfUpperVisit_nonneg ν ν' E δ θ φ a) (cdfUpperVisit_le_one ν ν' E δ θ φ a)
  have hiR := Occupation.integrable_remainingTime hTm hσm hiT
  have hbudget := cdfThresholdTime_remaining_mean_le law ν ν' E δ θ φ a b
    hν hν' hδ hinit hsmall hp hexitLower hexitUpper
  rw [← Occupation.remainingTime_integral_eq_sub hiT hiσ hfiniteT
    (ae_of_all _ hσle)] at hbudget
  apply le_trans (mul_le_mul_of_nonneg_left
    (integral_mono_ae hiV hiR (by
      filter_upwards [hfiniteσ] with ω hω
      exact cdfUpperVisit_sum_le_remaining ν ν' E δ θ φ a ω hω))
    (le_of_lt (mul_pos Real.pi_pos hp))) hbudget

end FixedCouplingPoisson.Furstenberg
