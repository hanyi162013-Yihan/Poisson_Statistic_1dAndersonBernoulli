import FixedCouplingPoisson.BlockContraction
import FixedCouplingPoisson.UniformBlockContraction
import FixedCouplingPoisson.ProjectiveRestart
import FixedCouplingPoisson.PhaseWeakTools
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Multi-block geometric contraction under the actual iid law

Actual deterministic-time iid restart upgrades a derived one-block
contraction to geometric contraction over repeated blocks.
The potential sequence is the genuine infinite product law. This module
does not assume an abstract Markov expectation or a restart identity.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

def pairDistanceMoment (law : PotentialLaw) (E s : ℝ) (p r : ProjectivePoint) (n : ℕ) : ℝ :=
  ∫ ω, (projectiveDistance (projectiveProcess E p n ω)
    (projectiveProcess E r n ω)) ^ s ∂iidMeasure law

theorem measurable_pairDistance_block (E s : ℝ) (hs : 0 ≤ s) (N : ℕ) :
    Measurable (fun z : (ProjectivePoint × ProjectivePoint) × PotentialSpace =>
      (projectiveDistance (projectiveProcess E z.1.1 N z.2)
        (projectiveProcess E z.1.2 N z.2)) ^ s) := by
  have hargp : Measurable (fun z : (ProjectivePoint × ProjectivePoint) × PotentialSpace =>
      (z.1.1, z.2)) := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hargr : Measurable (fun z : (ProjectivePoint × ProjectivePoint) × PotentialSpace =>
      (z.1.2, z.2)) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hp := (measurable_projectiveProcess_joint E N).comp hargp
  have hr := (measurable_projectiveProcess_joint E N).comp hargr
  have hdist {Ω : Type} [MeasurableSpace Ω] {f g : Ω → ProjectivePoint}
      (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun ω => projectiveDistance (f ω) (g ω)) := by
    have hd : Measurable (fun z : ProjectivePoint × ProjectivePoint =>
        projectiveDistance z.1 z.2) := continuous_projectiveDistance_joint.measurable
    have hpair : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
    exact hd.comp hpair
  have hD := hdist hp hr
  have hm := (Real.continuous_rpow_const hs).measurable.comp
    hD
  simpa only [Function.comp_def] using hm

theorem projectiveDistance_rpow_le_one (p r : ProjectivePoint) (s : ℝ) (hs : 0 ≤ s) :
    (projectiveDistance p r) ^ s ≤ 1 :=
  Real.rpow_le_one (projectiveDistance_nonneg p r) (projectiveDistance_le_one p r) hs

theorem pairDistanceMoment_nonneg (law : PotentialLaw) (E s : ℝ)
    (p r : ProjectivePoint) (n : ℕ) : 0 ≤ pairDistanceMoment law E s p r n :=
  integral_nonneg fun _ => Real.rpow_nonneg (projectiveDistance_nonneg _ _) _

theorem pairDistanceMoment_le_one (law : PotentialLaw) (E s : ℝ) (hs : 0 ≤ s)
    (p r : ProjectivePoint) (n : ℕ) : pairDistanceMoment law E s p r n ≤ 1 := by
  have h := integral_mono_ae (integrable_projectiveDistance_product_rpow law E n p r s hs)
    (integrable_const (1 : ℝ)) (Eventually.of_forall fun _ => projectiveDistance_rpow_le_one _ _ s hs)
  simpa only [pairDistanceMoment, integral_const, probReal_univ, one_smul] using h

/-- The fixed-block contraction applies conditionally on the actual past
pair. This integrated form is enough for multi-block weak convergence. -/
theorem pairDistanceMoment_add_block_le (law : PotentialLaw) (E s q : ℝ)
    (N : ℕ) (hs : 0 ≤ s)
    (hblock : ∀ p r : ProjectivePoint,
      pairDistanceMoment law E s p r N ≤ q * (projectiveDistance p r) ^ s)
    (p r : ProjectivePoint) (n : ℕ) :
    pairDistanceMoment law E s p r (n + N) ≤ q * pairDistanceMoment law E s p r n := by
  let X : PotentialSpace → ProjectivePoint × ProjectivePoint := fun ω =>
    (projectiveProcess E p n ω, projectiveProcess E r n ω)
  have hX : @Measurable PotentialSpace (ProjectivePoint × ProjectivePoint)
      (pastMeasurableSpace n) inferInstance X :=
    (projectiveProcess_past_measurable E p n).prodMk (projectiveProcess_past_measurable E r n)
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le n) le_rfl
  letI : IsProbabilityMeasure ((iidMeasure law).map X) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  let f : (ProjectivePoint × ProjectivePoint) × PotentialSpace → ℝ := fun z =>
    (projectiveDistance (projectiveProcess E z.1.1 N z.2)
      (projectiveProcess E z.1.2 N z.2)) ^ s
  have hfm : Measurable f := measurable_pairDistance_block E s hs N
  have hfi : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)) := by
    apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
      exact projectiveDistance_rpow_le_one _ _ s hs
  have hgmcomp :=
    (Real.continuous_rpow_const hs).measurable.comp continuous_projectiveDistance_joint.measurable
  have hgm : Measurable (fun z : ProjectivePoint × ProjectivePoint =>
      (projectiveDistance z.1 z.2) ^ s) := by
    simpa only [Function.comp_def] using hgmcomp
  have hgi : Integrable (fun z : ProjectivePoint × ProjectivePoint =>
      (projectiveDistance z.1 z.2) ^ s) ((iidMeasure law).map X) := by
    apply (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
      exact projectiveDistance_rpow_le_one _ _ s hs
  have hrestart : pairDistanceMoment law E s p r (n + N) =
      ∫ z, pairDistanceMoment law E s z.1 z.2 N ∂(iidMeasure law).map X := by
    calc
      _ = ∫ ω, f (X ω, potentialShift n ω) ∂iidMeasure law := by
        unfold pairDistanceMoment
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by
          simp only [f, X, projectiveProcess_add]
      _ = _ := iidMeasure_integral_past_state_future law n hX hfm hfi
  rw [hrestart]
  calc
    _ ≤ ∫ z, q * (projectiveDistance z.1 z.2) ^ s ∂(iidMeasure law).map X :=
      integral_mono_ae hfi.integral_prod_left (hgi.const_mul q)
        (Eventually.of_forall fun z => hblock z.1 z.2)
    _ = q * pairDistanceMoment law E s p r n := by
      rw [integral_const_mul, integral_map hXm.aemeasurable hgm.aestronglyMeasurable]
      rfl

theorem pairDistanceMoment_repeated_blocks_le (law : PotentialLaw) (E s q : ℝ)
    (N : ℕ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (hblock : ∀ p r : ProjectivePoint,
      pairDistanceMoment law E s p r N ≤ q * (projectiveDistance p r) ^ s)
    (p r : ProjectivePoint) (k a : ℕ) :
    pairDistanceMoment law E s p r (a + k * N) ≤ q ^ k := by
  induction k with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero, pow_zero] using
      pairDistanceMoment_le_one law E s hs p r a
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    calc
      _ ≤ q * pairDistanceMoment law E s p r (a + k * N) :=
        pairDistanceMoment_add_block_le law E s q N hs hblock p r _
      _ ≤ q * q ^ k := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (k + 1) := by rw [pow_succ, mul_comm]

theorem pairDistanceMoment_geometric_bound (law : PotentialLaw) (E s q : ℝ)
    (N : ℕ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (hblock : ∀ p r : ProjectivePoint,
      pairDistanceMoment law E s p r N ≤ q * (projectiveDistance p r) ^ s)
    (p r : ProjectivePoint) (n : ℕ) :
    pairDistanceMoment law E s p r n ≤ q ^ (n / N) := by
  have h := pairDistanceMoment_repeated_blocks_le law E s q N hs hq hblock p r
    (n / N) (n % N)
  have hn : n % N + (n / N) * N = n := by
    rw [Nat.mul_comm (n / N) N, Nat.mod_add_div]
  rw [hn] at h
  exact h

theorem pairDistanceMoment_tendsto_uniform_sequences (law : PotentialLaw) (E s q : ℝ)
    (N : ℕ) (hN : 0 < N) (hs : 0 ≤ s) (hq : 0 ≤ q) (hq1 : q < 1)
    (hblock : ∀ p r : ProjectivePoint,
      pairDistanceMoment law E s p r N ≤ q * (projectiveDistance p r) ^ s)
    (p r : ℕ → ProjectivePoint) :
    Tendsto (fun n => pairDistanceMoment law E s (p n) (r n) n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => pairDistanceMoment_nonneg law E s _ _ n)
    (fun n => pairDistanceMoment_geometric_bound law E s q N hs hq hblock _ _ n)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).comp
    (Nat.tendsto_div_const_atTop hN.ne')

/-- A geometric bound on every actual iid same-energy pair, uniform over
the two initial directions and every time (not only block endpoints). -/
theorem exists_projective_product_moment_geometric_bound (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ n : ℕ, ∀ p r : ProjectivePoint,
        pairDistanceMoment law E s p r n ≤ q ^ (n / N) := by
  obtain ⟨N, hN, s, q, hs, hs1, hq0, hq1, hblock⟩ :=
    exists_uniform_projective_block_contraction law E data
  exact ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun n p r =>
    pairDistanceMoment_geometric_bound law E s q N hs.le hq0 hblock p r n⟩

theorem exists_projective_product_moment_uniform_decay_on_compact (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ E ∈ K, ∀ p r : ProjectivePoint,
        pairDistanceMoment law E s p r n < ε := by
  obtain ⟨N, hN, s, q, hs, hs1, hq0, hq1, hblock⟩ :=
    exists_uniform_projective_block_contraction_on_compact law input K hK hne
  refine ⟨s, hs, hs1, fun ε hε => ?_⟩
  have ht : Tendsto (fun n : ℕ => q ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (Nat.tendsto_div_const_atTop hN.ne')
  exact (ht.eventually (gt_mem_nhds hε)).mono fun n hn E hE p r =>
    (pairDistanceMoment_geometric_bound law E s q N hs.le hq0 (hblock E hE) p r n).trans_lt hn

end FixedCouplingPoisson.Furstenberg
