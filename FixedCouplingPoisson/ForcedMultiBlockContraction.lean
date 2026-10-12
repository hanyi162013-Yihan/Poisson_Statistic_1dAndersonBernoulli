import FixedCouplingPoisson.MultiBlockContraction
import FixedCouplingPoisson.PairBlockContraction
import FixedCouplingPoisson.IIDRestart

/-!
# Repeated forced blocks for the actual shared-potential product

Deterministic-time iid restart propagates the proved forced block estimate. The error stays bounded by eta/(1-q), without an
IDS denominator. Initial pairs may have any joint law independent of the
fresh future; the stopped-past bridge uses the actual iid restart theorem.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

def twoEnergyPairDistanceMoment (law : PotentialLaw) (E E' s : ℝ)
    (p r : ProjectivePoint) (n : ℕ) : ℝ :=
  ∫ ω, (projectiveDistance (projectiveProcess E p n ω)
    (projectiveProcess E' r n ω)) ^ s ∂iidMeasure law

theorem measurable_twoEnergy_pairDistance_block (E E' s : ℝ) (hs : 0 ≤ s) (N : ℕ) :
    Measurable (fun z : ProjectivePair × PotentialSpace =>
      (projectiveDistance (projectiveProcess E z.1.1 N z.2)
        (projectiveProcess E' z.1.2 N z.2)) ^ s) := by
  have hargp : Measurable (fun z : ProjectivePair × PotentialSpace => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hargr : Measurable (fun z : ProjectivePair × PotentialSpace => (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hp := (measurable_projectiveProcess_joint E N).comp hargp
  have hr := (measurable_projectiveProcess_joint E' N).comp hargr
  have hdist {Ω : Type} [MeasurableSpace Ω] {f g : Ω → ProjectivePoint}
      (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun ω => projectiveDistance (f ω) (g ω)) := by
    have hd : Measurable (fun z : ProjectivePair => projectiveDistance z.1 z.2) :=
      continuous_projectiveDistance_joint.measurable
    have hpair : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
    exact hd.comp hpair
  have hD := hdist hp hr
  have hm := (Real.continuous_rpow_const hs).measurable.comp hD
  simpa only [Function.comp_def] using hm

theorem integrable_twoEnergy_pairDistance_block (law : PotentialLaw)
    (E E' s : ℝ) (hs : 0 ≤ s) (N : ℕ) (ν : ProbabilityMeasure ProjectivePair) :
    Integrable (fun z : ProjectivePair × PotentialSpace =>
      (projectiveDistance (projectiveProcess E z.1.1 N z.2)
        (projectiveProcess E' z.1.2 N z.2)) ^ s)
      ((ν : Measure ProjectivePair).prod (iidMeasure law)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_twoEnergy_pairDistance_block E E' s hs N).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
    exact projectiveDistance_rpow_le_one _ _ s hs

theorem twoEnergyPairDistanceMoment_le_one (law : PotentialLaw) (E E' s : ℝ)
    (hs : 0 ≤ s) (p r : ProjectivePoint) (n : ℕ) :
    twoEnergyPairDistanceMoment law E E' s p r n ≤ 1 := by
  have h := integral_mono_ae
    (integrable_two_energy_projectiveDistance_rpow law E E' s hs p r n)
    (integrable_const (1 : ℝ))
    (Eventually.of_forall fun _ => projectiveDistance_rpow_le_one _ _ s hs)
  simpa only [twoEnergyPairDistanceMoment, integral_const, probReal_univ, one_smul] using h

theorem twoEnergyPairDistanceMoment_add_block_le (law : PotentialLaw)
    (E E' s q η : ℝ) (N : ℕ) (hs : 0 ≤ s)
    (hblock : ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r N ≤ q * (projectiveDistance p r) ^ s + η)
    (p r : ProjectivePoint) (n : ℕ) :
    twoEnergyPairDistanceMoment law E E' s p r (n + N) ≤
      q * twoEnergyPairDistanceMoment law E E' s p r n + η := by
  let X : PotentialSpace → ProjectivePair := fun ω =>
    (projectiveProcess E p n ω, projectiveProcess E' r n ω)
  have hX : @Measurable PotentialSpace ProjectivePair
      (pastMeasurableSpace n) inferInstance X :=
    (projectiveProcess_past_measurable E p n).prodMk (projectiveProcess_past_measurable E' r n)
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le n) le_rfl
  letI : IsProbabilityMeasure ((iidMeasure law).map X) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  let f : ProjectivePair × PotentialSpace → ℝ := fun z =>
    (projectiveDistance (projectiveProcess E z.1.1 N z.2)
      (projectiveProcess E' z.1.2 N z.2)) ^ s
  have hfm : Measurable f := measurable_twoEnergy_pairDistance_block E E' s hs N
  have hfi : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)) := by
    apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
      exact projectiveDistance_rpow_le_one _ _ s hs
  have hgmcomp :=
    (Real.continuous_rpow_const hs).measurable.comp continuous_projectiveDistance_joint.measurable
  have hgm : Measurable (fun z : ProjectivePair => (projectiveDistance z.1 z.2) ^ s) := by
    simpa only [Function.comp_def] using hgmcomp
  have hgi : Integrable (fun z : ProjectivePair => (projectiveDistance z.1 z.2) ^ s)
      ((iidMeasure law).map X) := by
    apply (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
      exact projectiveDistance_rpow_le_one _ _ s hs
  have hAffine : Integrable (fun z : ProjectivePair => q * (projectiveDistance z.1 z.2) ^ s + η)
      ((iidMeasure law).map X) := (hgi.const_mul q).add (integrable_const η)
  have hrestart : twoEnergyPairDistanceMoment law E E' s p r (n + N) =
      ∫ z, twoEnergyPairDistanceMoment law E E' s z.1 z.2 N ∂(iidMeasure law).map X := by
    calc
      _ = ∫ ω, f (X ω, potentialShift n ω) ∂iidMeasure law := by
        unfold twoEnergyPairDistanceMoment
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by simp only [f, X, projectiveProcess_add]
      _ = _ := iidMeasure_integral_past_state_future law n hX hfm hfi
  rw [hrestart]
  calc
    _ ≤ ∫ z, q * (projectiveDistance z.1 z.2) ^ s + η ∂(iidMeasure law).map X :=
      integral_mono_ae hfi.integral_prod_left hAffine
        (Eventually.of_forall fun z => hblock z.1 z.2)
    _ = q * twoEnergyPairDistanceMoment law E E' s p r n + η := by
      rw [integral_add (hgi.const_mul q) (integrable_const η), integral_const_mul,
        integral_const, probReal_univ, one_smul,
        integral_map hXm.aemeasurable hgm.aestronglyMeasurable]
      rfl

theorem twoEnergyPairDistanceMoment_repeated_blocks_le (law : PotentialLaw)
    (E E' s q η : ℝ) (N : ℕ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hq1 : q < 1) (hη : 0 ≤ η)
    (hblock : ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r N ≤ q * (projectiveDistance p r) ^ s + η)
    (p r : ProjectivePoint) (k a : ℕ) :
    twoEnergyPairDistanceMoment law E E' s p r (a + k * N) ≤ q ^ k + η / (1 - q) := by
  have hgap : 0 < 1 - q := sub_pos.mpr hq1
  have herr : 0 ≤ η / (1 - q) := div_nonneg hη hgap.le
  induction k with
  | zero =>
    simpa only [Nat.zero_mul, Nat.add_zero, pow_zero] using
      (twoEnergyPairDistanceMoment_le_one law E E' s hs p r a).trans
        (le_add_of_nonneg_right herr)
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    calc
      _ ≤ q * twoEnergyPairDistanceMoment law E E' s p r (a + k * N) + η :=
        twoEnergyPairDistanceMoment_add_block_le law E E' s q η N hs hblock p r _
      _ ≤ q * (q ^ k + η / (1 - q)) + η :=
        add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
      _ = q ^ (k + 1) + η / (1 - q) := by
        rw [pow_succ]
        field_simp [hgap.ne']
        <;> ring

theorem twoEnergyPairDistanceMoment_geometric_bound (law : PotentialLaw)
    (E E' s q η : ℝ) (N : ℕ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hq1 : q < 1) (hη : 0 ≤ η)
    (hblock : ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r N ≤ q * (projectiveDistance p r) ^ s + η)
    (p r : ProjectivePoint) (n : ℕ) :
    twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η / (1 - q) := by
  have h := twoEnergyPairDistanceMoment_repeated_blocks_le law E E' s q η N hs hq hq1 hη
    hblock p r (n / N) (n % N)
  have hn : n % N + (n / N) * N = n := by
    rw [Nat.mul_comm (n / N) N, Nat.mod_add_div]
  rwa [hn] at h

/-- Every time and every initial pair, uniformly over reference energies in K. -/
theorem exists_uniform_forced_multiblock_moment (law : PotentialLaw) (input : Input law)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' : ℝ, ∀ n : ℕ, ∀ p r : ProjectivePoint,
        twoEnergyPairDistanceMoment law E E' s p r n ≤
          q ^ (n / N) + C * |E - E'| ^ s := by
  obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hblock⟩ :=
    exists_uniform_forced_projective_block_contraction law input K hK hne
  have hgap : 0 < 1 - q := sub_pos.mpr hq1
  refine ⟨N, hN, s, q, C / (1 - q), hs, hs1, hq0, hq1, div_nonneg hC hgap.le,
    fun E hE E' n p r => ?_⟩
  have h := twoEnergyPairDistanceMoment_geometric_bound law E E' s q
    (C * |E - E'| ^ s) N hs.le hq0 hq1
    (mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) s)) (hblock E hE E') p r n
  simpa only [div_mul_eq_mul_div₀] using h

/-- A direct probability tail bound for the actual projective pair. -/
theorem twoEnergyPairDistanceMoment_measure_distance_ge_le (law : PotentialLaw)
    (E E' s h B : ℝ) (hs : 0 ≤ s) (hh : 0 < h)
    (p r : ProjectivePoint) (n : ℕ)
    (hB : twoEnergyPairDistanceMoment law E E' s p r n ≤ B) :
    (iidMeasure law).real {ω | h ≤ projectiveDistance
      (projectiveProcess E p n ω) (projectiveProcess E' r n ω)} ≤ B / h ^ s := by
  have hset : {ω | h ≤ projectiveDistance
      (projectiveProcess E p n ω) (projectiveProcess E' r n ω)} ⊆
      {ω | h ^ s ≤ (projectiveDistance
        (projectiveProcess E p n ω) (projectiveProcess E' r n ω)) ^ s} := by
    intro ω hω
    exact Real.rpow_le_rpow hh.le hω hs
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hh s)).mpr
  calc
    _ ≤ (iidMeasure law).real {ω | h ^ s ≤ (projectiveDistance
        (projectiveProcess E p n ω) (projectiveProcess E' r n ω)) ^ s} * h ^ s :=
      mul_le_mul_of_nonneg_right (measureReal_mono hset) (Real.rpow_nonneg hh.le s)
    _ = h ^ s * (iidMeasure law).real {ω | h ^ s ≤ (projectiveDistance
        (projectiveProcess E p n ω) (projectiveProcess E' r n ω)) ^ s} := mul_comm _ _
    _ ≤ twoEnergyPairDistanceMoment law E E' s p r n :=
      mul_meas_ge_le_integral_of_nonneg
        (ae_of_all _ fun _ => Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)
        (integrable_two_energy_projectiveDistance_rpow law E E' s hs p r n) (h ^ s)
    _ ≤ B := hB

/-- An arbitrary joint initial law may be coupled to an independent fresh iid future. -/
theorem twoEnergyPairDistanceMoment_initial_law_bound (law : PotentialLaw)
    (E E' s B : ℝ) (hs : 0 ≤ s) (n : ℕ) (ν : ProbabilityMeasure ProjectivePair)
    (hbound : ∀ p r : ProjectivePoint, twoEnergyPairDistanceMoment law E E' s p r n ≤ B) :
    (∫ z : ProjectivePair × PotentialSpace,
      (projectiveDistance (projectiveProcess E z.1.1 n z.2)
        (projectiveProcess E' z.1.2 n z.2)) ^ s
      ∂((ν : Measure ProjectivePair).prod (iidMeasure law))) ≤ B := by
  have hi := integrable_twoEnergy_pairDistance_block law E E' s hs n ν
  rw [integral_prod _ hi]
  have h := integral_mono_ae hi.integral_prod_left (integrable_const B)
    (Eventually.of_forall fun z : ProjectivePair => hbound z.1 z.2)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Actual stopped-past states, with freshness derived from the iid law. -/
theorem twoEnergyPairDistanceMoment_stopped_state_bound (law : PotentialLaw)
    (E E' s B : ℝ) (hs : 0 ≤ s) (n : ℕ)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair} (hX : Measurable[hτ.measurableSpace] X)
    (hbound : ∀ p r : ProjectivePoint, twoEnergyPairDistanceMoment law E E' s p r n ≤ B) :
    (∫ ω, (projectiveDistance
      (projectiveProcess E (X ω).1 n (stoppedPotentialFuture τ ω))
      (projectiveProcess E' (X ω).2 n (stoppedPotentialFuture τ ω))) ^ s ∂iidMeasure law) ≤ B := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  letI : IsProbabilityMeasure ((iidMeasure law).map X) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  let ν : ProbabilityMeasure ProjectivePair := ⟨(iidMeasure law).map X,
    Measure.isProbabilityMeasure_map hXm.aemeasurable⟩
  let f : ProjectivePair × PotentialSpace → ℝ := fun z =>
    (projectiveDistance (projectiveProcess E z.1.1 n z.2)
      (projectiveProcess E' z.1.2 n z.2)) ^ s
  have hi : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)) :=
    integrable_twoEnergy_pairDistance_block law E E' s hs n ν
  have heq := iidMeasure_integral_stopped_state_future law hτ hfinite hX hi
  change (∫ ω, f (X ω, stoppedPotentialFuture τ ω) ∂iidMeasure law) ≤ B
  rw [heq]
  exact (show (∫ z, futureKernel law f z ∂(iidMeasure law).map X) ≤ B from by
    have h := integral_mono_ae hi.integral_prod_left (integrable_const B)
      (Eventually.of_forall fun z : ProjectivePair => hbound z.1 z.2)
    simpa only [integral_const, probReal_univ, one_smul, futureKernel] using h)

end FixedCouplingPoisson.Furstenberg
