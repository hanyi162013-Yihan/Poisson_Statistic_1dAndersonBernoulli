import FixedCouplingPoisson.LogMean
import FixedCouplingPoisson.IIDModel

/-!
# Actual iid projective evolution and product-log expectation

Every new transfer step multiplies on the left. The projective evolution is
measurable in the actual finite past; next-site independence is derived from
the infinite iid law. Its distribution equals the actual Markov iterate.
The genuine Euclidean product log telescopes into single-step log cocycles,
which identifies its integral and yields a uniform positive finite block.
No iid/Markov bridge is an extra hypothesis.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

def projectiveProcess (E : ℝ) (p : ProjectivePoint) : ℕ → PotentialSpace → ProjectivePoint
  | 0, _ => p
  | n + 1, ω => transferProjective E (ω n) (projectiveProcess E p n ω)

@[simp] theorem projectiveProcess_zero (E : ℝ) (p : ProjectivePoint) (ω : PotentialSpace) :
    projectiveProcess E p 0 ω = p := rfl

@[simp] theorem projectiveProcess_succ (E : ℝ) (p : ProjectivePoint)
    (n : ℕ) (ω : PotentialSpace) :
    projectiveProcess E p (n + 1) ω =
      transferProjective E (ω n) (projectiveProcess E p n ω) := rfl

theorem projectiveProcess_past_measurable (E : ℝ) (p : ProjectivePoint) (n : ℕ) :
    @Measurable PotentialSpace ProjectivePoint (pastMeasurableSpace n) inferInstance
      (projectiveProcess E p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hsite : @Measurable PotentialSpace ℝ (pastMeasurableSpace (n + 1)) inferInstance
        (fun ω => ω n) := by
      apply Measurable.of_comap_le
      change siteMeasurableSpace n ≤ pastMeasurableSpace (n + 1)
      exact le_iSup_of_le n (le_iSup_of_le (Nat.lt_succ_self n) le_rfl)
    have hprev : @Measurable PotentialSpace ProjectivePoint
        (pastMeasurableSpace (n + 1)) inferInstance (projectiveProcess E p n) :=
      ih.mono (pastMeasurableSpace_mono (Nat.le_succ n)) le_rfl
    have hm := (measurable_forwardStep E).comp (hsite.prodMk hprev)
    have hfun : projectiveProcess E p (n + 1) =
        forwardStep E ∘ (fun ω => (ω n, projectiveProcess E p n ω)) := by
      funext ω
      rfl
    rw [hfun]
    exact hm

theorem projectiveProcess_measurable (E : ℝ) (p : ProjectivePoint) (n : ℕ) :
    Measurable (projectiveProcess E p n) :=
  (projectiveProcess_past_measurable E p n).mono (pastMeasurableSpace_le n) le_rfl

theorem iidMeasure_past_state_site_independent {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) (n : ℕ) {X : PotentialSpace → S}
    (hX : @Measurable PotentialSpace S (pastMeasurableSpace n) inferInstance X) :
    IndepFun (fun ω : PotentialSpace => ω n) X (iidMeasure law) := by
  have hsite : @Measurable PotentialSpace ℝ (futureMeasurableSpace n) inferInstance
      (fun ω => ω n) := by
    apply Measurable.of_comap_le
    change siteMeasurableSpace n ≤ futureMeasurableSpace n
    exact le_iSup_of_le n (le_iSup_of_le (Nat.le_refl n) le_rfl)
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (iidMeasure_past_future_independent law n).symm hsite.comap_le)
    hX.comap_le

theorem iidMeasure_past_state_site_map {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) (n : ℕ) {X : PotentialSpace → S}
    (hX : @Measurable PotentialSpace S (pastMeasurableSpace n) inferInstance X) :
    (iidMeasure law).map (fun ω => (ω n, X ω)) =
      law.measure.prod ((iidMeasure law).map X) := by
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le n) le_rfl
  rw [(iidMeasure_past_state_site_independent law n hX).map_prod_eq_prod_map_map
    (measurable_site n).aemeasurable hXm.aemeasurable, iidMeasure_site_map]

def projectiveProcessDistribution (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) : ProbabilityMeasure ProjectivePoint :=
  ⟨(iidMeasure law).map (projectiveProcess E p n),
    Measure.isProbabilityMeasure_map (projectiveProcess_measurable E p n).aemeasurable⟩

def pointDistribution (p : ProjectivePoint) : ProbabilityMeasure ProjectivePoint :=
  ⟨Measure.dirac p, inferInstance⟩

@[simp] theorem projectiveProcessDistribution_zero (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) :
    projectiveProcessDistribution law E p 0 = pointDistribution p := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidMeasure law).map (fun _ => p) = Measure.dirac p
  simp

theorem projectiveProcessDistribution_succ (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    projectiveProcessDistribution law E p (n + 1) =
      forwardDistribution law E (projectiveProcessDistribution law E p n) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidMeasure law).map (projectiveProcess E p (n + 1)) =
    (law.measure.prod ((iidMeasure law).map (projectiveProcess E p n))).map (forwardStep E)
  rw [← iidMeasure_past_state_site_map law n (projectiveProcess_past_measurable E p n),
    Measure.map_map (measurable_forwardStep E)
      ((measurable_site n).prodMk (projectiveProcess_measurable E p n))]
  rfl

/-- The actual iid projective-product law equals the genuine Markov iterate. -/
theorem projectiveProcessDistribution_eq_orbit (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    projectiveProcessDistribution law E p n = probabilityOrbit law E (pointDistribution p) n := by
  induction n with
  | zero => exact projectiveProcessDistribution_zero law E p
  | succ n ih => rw [projectiveProcessDistribution_succ, probabilityOrbit_succ, ih]

/-- The projective evolution is the actual matrix product, with every new
transfer step multiplied on the left. -/
theorem projectiveProcess_eq_mk_product (E : ℝ) (p : ProjectivePoint)
    (n : ℕ) (ω : PotentialSpace) :
    projectiveProcess E p n ω = Projectivization.mk ℝ
      (transferProduct E ω n *ᵥ p.rep)
      (sl2_mulVec_ne_zero _ (transferProduct_det E ω n) p.rep p.rep_nonzero) := by
  induction n with
  | zero => simpa only [projectiveProcess_zero, transferProduct, Matrix.one_mulVec] using
      (Projectivization.mk_rep p).symm
  | succ n ih =>
    rw [projectiveProcess_succ, ih, transferProjective_mk]
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
    refine ⟨1, ?_⟩
    simp only [one_smul, transferProduct, Matrix.mulVec_mulVec]

theorem projectiveGrowth_product_pos (E : ℝ) (ω : PotentialSpace)
    (n : ℕ) (p : ProjectivePoint) :
    0 < projectiveGrowth (transferProduct E ω n) p := by
  conv_rhs => rw [← Projectivization.mk_rep p]
  rw [projectiveGrowth_mk, vectorGrowth]
  exact div_pos (euclideanNorm_pos _
    (sl2_mulVec_ne_zero _ (transferProduct_det E ω n) p.rep p.rep_nonzero))
    (euclideanNorm_pos p.rep p.rep_nonzero)

@[simp] theorem projectiveLogGrowth_product_zero (E : ℝ) (ω : PotentialSpace)
    (p : ProjectivePoint) :
    projectiveLogGrowth (transferProduct E ω 0) p = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  simp only [projectiveLogGrowth, transferProduct, projectiveGrowth_mk, vectorGrowth,
    Matrix.one_mulVec, div_self (euclideanNorm_pos p.rep p.rep_nonzero).ne', Real.log_one]

theorem projectiveLogGrowth_product_succ (E : ℝ) (ω : PotentialSpace)
    (n : ℕ) (p : ProjectivePoint) :
    projectiveLogGrowth (transferProduct E ω (n + 1)) p =
      transferLogCocycle E (ω n) (projectiveProcess E p n ω) +
        projectiveLogGrowth (transferProduct E ω n) p := by
  have hn : euclideanNorm (transferProduct E ω n *ᵥ p.rep) ≠ 0 :=
    (euclideanNorm_pos _ (sl2_mulVec_ne_zero _ (transferProduct_det E ω n)
      p.rep p.rep_nonzero)).ne'
  have hp : euclideanNorm p.rep ≠ 0 := (euclideanNorm_pos p.rep p.rep_nonzero).ne'
  have heq : projectiveGrowth (transferProduct E ω (n + 1)) p =
      projectiveGrowth (transfer E (ω n)) (projectiveProcess E p n ω) *
        projectiveGrowth (transferProduct E ω n) p := by
    rw [projectiveProcess_eq_mk_product, projectiveGrowth_mk]
    conv_lhs => rw [← Projectivization.mk_rep p]
    rw [projectiveGrowth_mk]
    conv_rhs => rhs; rw [← Projectivization.mk_rep p]
    rw [projectiveGrowth_mk]
    simp only [vectorGrowth, transferProduct, ← Matrix.mulVec_mulVec]
    field_simp [hn, hp]
  change Real.log (projectiveGrowth (transferProduct E ω (n + 1)) p) =
    Real.log (projectiveGrowth (transfer E (ω n)) (projectiveProcess E p n ω)) +
      Real.log (projectiveGrowth (transferProduct E ω n) p)
  rw [heq, Real.log_mul (projectiveGrowth_transfer_pos _ _ _).ne'
    (projectiveGrowth_product_pos E ω n p).ne']

theorem projectiveLogGrowth_product_sum (E : ℝ) (ω : PotentialSpace)
    (n : ℕ) (p : ProjectivePoint) :
    projectiveLogGrowth (transferProduct E ω n) p =
      ∑ k ∈ Finset.range n, transferLogCocycle E (ω k) (projectiveProcess E p k ω) := by
  induction n with
  | zero => simp
  | succ n ih => rw [projectiveLogGrowth_product_succ, Finset.sum_range_succ, ih, add_comm]

theorem integrable_projectiveProcess_step (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    Integrable (fun ω => transferLogCocycle E (ω n) (projectiveProcess E p n ω))
      (iidMeasure law) := by
  have hm := iidMeasure_past_state_site_map law n (projectiveProcess_past_measurable E p n)
  have hi : Integrable (fun z : ℝ × ProjectivePoint => transferLogCocycle E z.1 z.2)
      ((iidMeasure law).map (fun ω => (ω n, projectiveProcess E p n ω))) := by
    rw [hm]
    exact integrable_transferLogCocycle law E (projectiveProcessDistribution law E p n)
  exact hi.comp_measurable ((measurable_site n).prodMk (projectiveProcess_measurable E p n))

theorem integral_projectiveProcess_step (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    (∫ ω, transferLogCocycle E (ω n) (projectiveProcess E p n ω) ∂iidMeasure law) =
      ∫ q, oneStepLogMean law E q
        ∂(probabilityOrbit law E (pointDistribution p) n : Measure ProjectivePoint) := by
  have hm := iidMeasure_past_state_site_map law n (projectiveProcess_past_measurable E p n)
  have hpair : Measurable (fun ω : PotentialSpace => (ω n, projectiveProcess E p n ω)) :=
    (measurable_site n).prodMk (projectiveProcess_measurable E p n)
  calc
    (∫ ω, transferLogCocycle E (ω n) (projectiveProcess E p n ω) ∂iidMeasure law) =
        ∫ z, transferLogCocycle E z.1 z.2
          ∂((iidMeasure law).map (fun ω => (ω n, projectiveProcess E p n ω))) :=
      (integral_map hpair.aemeasurable
        (continuous_transferLogCocycle E).measurable.aestronglyMeasurable).symm
    _ = stationaryMean law E (projectiveProcessDistribution law E p n) := by rw [hm]; rfl
    _ = ∫ q, oneStepLogMean law E q
        ∂(projectiveProcessDistribution law E p n : Measure ProjectivePoint) :=
      stationaryMean_eq_integral_oneStep law E _
    _ = _ := by rw [projectiveProcessDistribution_eq_orbit]

theorem integrable_projectiveLogGrowth_product (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    Integrable (fun ω => projectiveLogGrowth (transferProduct E ω n) p) (iidMeasure law) := by
  have heq : (fun ω => projectiveLogGrowth (transferProduct E ω n) p) =
      (fun ω => ∑ k ∈ Finset.range n,
        transferLogCocycle E (ω k) (projectiveProcess E p k ω)) :=
    funext fun ω => projectiveLogGrowth_product_sum E ω n p
  rw [heq]
  exact integrable_finsetSum (Finset.range n)
    (fun k _ => integrable_projectiveProcess_step law E p k)

/-- Actual iid expectation of the actual Euclidean product cocycle, not an
abstract expectation operator or an unproved Markov identification. -/
theorem integral_projectiveLogGrowth_product (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    (∫ ω, projectiveLogGrowth (transferProduct E ω n) p ∂iidMeasure law) =
      ∑ k ∈ Finset.range n, ∫ q, oneStepLogMean law E q
        ∂(probabilityOrbit law E (pointDistribution p) k : Measure ProjectivePoint) := by
  have heq : (fun ω => projectiveLogGrowth (transferProduct E ω n) p) =
      (fun ω => ∑ k ∈ Finset.range n,
        transferLogCocycle E (ω k) (projectiveProcess E p k ω)) :=
    funext fun ω => projectiveLogGrowth_product_sum E ω n p
  rw [heq, integral_finsetSum (Finset.range n)
    (fun k _ => integrable_projectiveProcess_step law E p k)]
  exact Finset.sum_congr rfl (fun k _ => integral_projectiveProcess_step law E p k)

theorem measurable_projectiveLogGrowth_product (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) :
    Measurable (fun ω : PotentialSpace => projectiveLogGrowth (transferProduct E ω n) p) := by
  have heq : (fun ω => projectiveLogGrowth (transferProduct E ω n) p) =
      (fun ω => ∑ k ∈ Finset.range n,
        transferLogCocycle E (ω k) (projectiveProcess E p k ω)) :=
    funext fun ω => projectiveLogGrowth_product_sum E ω n p
  rw [heq]
  apply Finset.measurable_sum
  intro k _
  have hm := (continuous_transferLogCocycle E).measurable.comp
    ((measurable_site k).prodMk (projectiveProcess_measurable E p k))
  simpa only [Function.comp_def] using hm

/-- A single almost-sure event gives the same product-log bound for every
initial projective direction. This is elementary bounded-law bookkeeping. -/
theorem ae_uniform_product_log_bound (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂iidMeasure law, ∀ p : ProjectivePoint,
      |projectiveLogGrowth (transferProduct E ω n) p| ≤ K := by
  obtain ⟨M, hM, hb⟩ := iidMeasure_bounded_all_sites law
  have hC : 0 ≤ Real.log (|E| + M + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg E])
  refine ⟨(n : ℝ) * Real.log (|E| + M + 2), mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  filter_upwards [hb] with ω hω p
  rw [projectiveLogGrowth_product_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        |transferLogCocycle E (ω k) (projectiveProcess E p k ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, Real.log (|E| + M + 2) :=
      Finset.sum_le_sum fun k _ =>
        abs_transferLogCocycle_le E (ω k) M hM (hω k) _
    _ = _ := by simp

/-- The derived finite block is uniform over every initial projective line.
The qualitative interface supplies only stationary uniqueness and positive
stationary mean. Negative-moment contraction is a subsequent analytic step. -/
theorem exists_uniform_positive_product_log_mean (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : ProjectivePoint,
      (N : ℝ) * stationaryMean law E data.forwardMeasure / 2 ≤
        ∫ ω, projectiveLogGrowth (transferProduct E ω N) p ∂iidMeasure law := by
  obtain ⟨n, hn⟩ := exists_uniform_positive_log_cesaro law E data
  refine ⟨n + 1, Nat.succ_pos n, fun p => ?_⟩
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hi := integral_empiricalCesaro law E (pointDistribution p) n
    (oneStepContinuousLogMean law E)
  have h : stationaryMean law E data.forwardMeasure / 2 ≤
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        (∫ ω, projectiveLogGrowth (transferProduct E ω (n + 1)) p ∂iidMeasure law) := by
    rw [integral_projectiveLogGrowth_product]
    exact hi ▸ hn (pointDistribution p)
  have hmul := mul_le_mul_of_nonneg_left h hN.le
  simpa only [mul_div_assoc, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] using hmul

end FixedCouplingPoisson.Furstenberg
