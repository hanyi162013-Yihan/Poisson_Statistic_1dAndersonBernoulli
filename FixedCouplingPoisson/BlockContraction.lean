import FixedCouplingPoisson.NegativeMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Same-energy fixed-block contraction for actual iid transfer products

The actual determinant-distance identity combines with the actual iid
negative-moment estimate. Fixed-block contraction is derived conditional on
qualitative Furstenberg data at the selected energy; it is not a field in the
external interface. Uniformity in energy and the two-energy perturbation,
occupation, and Poisson arguments remain separate.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix

theorem projectiveDistance_nonneg (p r : ProjectivePoint) :
    0 ≤ projectiveDistance p r := by
  unfold projectiveDistance determinantDistance
  exact div_nonneg (abs_nonneg _) (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))

theorem projectiveDistance_product_identity (E : ℝ) (ω : PotentialSpace)
    (n : ℕ) (p r : ProjectivePoint) :
    projectiveDistance (projectiveProcess E p n ω) (projectiveProcess E r n ω) =
      projectiveDistance p r /
        (projectiveGrowth (transferProduct E ω n) p *
          projectiveGrowth (transferProduct E ω n) r) := by
  have hp : euclideanNorm p.rep ≠ 0 := (euclideanNorm_pos p.rep p.rep_nonzero).ne'
  have hr : euclideanNorm r.rep ≠ 0 := (euclideanNorm_pos r.rep r.rep_nonzero).ne'
  have hAp : euclideanNorm (transferProduct E ω n *ᵥ p.rep) ≠ 0 :=
    (euclideanNorm_pos _ (sl2_mulVec_ne_zero _ (transferProduct_det E ω n)
      p.rep p.rep_nonzero)).ne'
  have hAr : euclideanNorm (transferProduct E ω n *ᵥ r.rep) ≠ 0 :=
    (euclideanNorm_pos _ (sl2_mulVec_ne_zero _ (transferProduct_det E ω n)
      r.rep r.rep_nonzero)).ne'
  have hgp : projectiveGrowth (transferProduct E ω n) p =
      vectorGrowth (transferProduct E ω n) p.rep := by
    conv_lhs => rw [← Projectivization.mk_rep p]
    rfl
  have hgr : projectiveGrowth (transferProduct E ω n) r =
      vectorGrowth (transferProduct E ω n) r.rep := by
    conv_lhs => rw [← Projectivization.mk_rep r]
    rfl
  rw [projectiveProcess_eq_mk_product, projectiveProcess_eq_mk_product,
    projectiveDistance_mk, hgp, hgr]
  simp only [projectiveDistance, determinantDistance, vectorGrowth, wedge_mulVec,
    transferProduct_det, one_mul]
  field_simp [hp, hr, hAp, hAr] <;> ring

theorem projectiveDistance_product_rpow_identity (E : ℝ) (ω : PotentialSpace)
    (n : ℕ) (p r : ProjectivePoint) (s : ℝ) :
    (projectiveDistance (projectiveProcess E p n ω) (projectiveProcess E r n ω)) ^ s =
      (projectiveDistance p r) ^ s * Real.exp (-s *
        (projectiveLogGrowth (transferProduct E ω n) p +
          projectiveLogGrowth (transferProduct E ω n) r)) := by
  have hp := projectiveGrowth_product_pos E ω n p
  have hr := projectiveGrowth_product_pos E ω n r
  rw [projectiveDistance_product_identity,
    Real.div_rpow (projectiveDistance_nonneg p r) (mul_pos hp hr).le,
    Real.rpow_def_of_pos (mul_pos hp hr), Real.log_mul hp.ne' hr.ne',
    div_eq_mul_inv, ← Real.exp_neg]
  congr 1
  congr 1
  unfold projectiveLogGrowth
  ring

theorem integrable_projectiveDistance_product_rpow (law : PotentialLaw) (E : ℝ)
    (n : ℕ) (p r : ProjectivePoint) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => (projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E r n ω)) ^ s) (iidMeasure law) := by
  obtain ⟨K, _, hb⟩ := ae_uniform_product_log_bound law E n
  have hXm := (measurable_projectiveLogGrowth_product E p n).add
    (measurable_projectiveLogGrowth_product E r n)
  have hXb : ∀ᵐ ω ∂iidMeasure law,
      |projectiveLogGrowth (transferProduct E ω n) p +
        projectiveLogGrowth (transferProduct E ω n) r| ≤ 2 * K :=
    hb.mono fun ω hω => (abs_add_le _ _).trans (by linarith [hω p, hω r])
  have hi := integrable_exp_negative_of_abs_bound (iidMeasure law) _ hXm (2 * K) s hs hXb
  have heq : (fun ω => (projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E r n ω)) ^ s) =
      (fun ω => (projectiveDistance p r) ^ s * Real.exp (-s *
        (projectiveLogGrowth (transferProduct E ω n) p +
          projectiveLogGrowth (transferProduct E ω n) r))) :=
    funext fun ω => projectiveDistance_product_rpow_identity E ω n p r s
  rw [heq]
  exact hi.const_mul _

/-- Same-energy fixed-block contraction for the actual iid transfer matrices,
uniform over both starting projective directions, including equal directions.
No stopping-time, two-energy, IDS, Sturm, or Poisson conclusion is asserted. -/
theorem exists_uniform_projective_block_contraction (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ p r : ProjectivePoint,
        (∫ ω, (projectiveDistance (projectiveProcess E p N ω)
          (projectiveProcess E r N ω)) ^ s ∂iidMeasure law) ≤
            q * (projectiveDistance p r) ^ s := by
  obtain ⟨N, hN, s, q, hs, hs1, hq0, hq1, hq⟩ :=
    exists_uniform_product_negative_log_moment law E data
  refine ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun p r => ?_⟩
  have heq : (fun ω => (projectiveDistance (projectiveProcess E p N ω)
      (projectiveProcess E r N ω)) ^ s) =
      (fun ω => (projectiveDistance p r) ^ s * Real.exp (-s *
        (projectiveLogGrowth (transferProduct E ω N) p +
          projectiveLogGrowth (transferProduct E ω N) r))) :=
    funext fun ω => projectiveDistance_product_rpow_identity E ω N p r s
  rw [heq, integral_const_mul]
  calc
    _ ≤ (projectiveDistance p r) ^ s * q :=
      mul_le_mul_of_nonneg_left (hq p r) (Real.rpow_nonneg (projectiveDistance_nonneg p r) s)
    _ = _ := mul_comm _ _

end FixedCouplingPoisson.Furstenberg
