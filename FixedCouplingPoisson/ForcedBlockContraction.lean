import FixedCouplingPoisson.UniformBlockContraction
import FixedCouplingPoisson.ProjectiveMetric
import FixedCouplingPoisson.PhaseWeakTools
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Actual two-energy fixed-block contraction with an additive perturbation

The determinant identity and the bounded inverse give the ordinary
same-energy one-step direction bound. The actual metric triangle inequality
and actual one-step energy bound propagate an energy error through the finite
block. Fractional-power subadditivity then combines this deterministic error
with the proved same-energy iid block contraction. No perturbation estimate
is an extra external hypothesis.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Filter

theorem projectiveDistance_transfer_identity (E v : ℝ) (p r : ProjectivePoint) :
    projectiveDistance (transferProjective E v p) (transferProjective E v r) =
      projectiveDistance p r /
        (projectiveGrowth (transfer E v) p * projectiveGrowth (transfer E v) r) := by
  simpa only [projectiveProcess, transferProduct, Matrix.mul_one] using
    projectiveDistance_product_identity E (fun _ => v) 1 p r

theorem projectiveDistance_transfer_lipschitz (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M)
    (p r : ProjectivePoint) :
    projectiveDistance (transferProjective E v p) (transferProjective E v r) ≤
      (|E| + M + 2) ^ 2 * projectiveDistance p r := by
  let C : ℝ := |E| + M + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hp := projectiveGrowth_transfer_pos E v p
  have hr := projectiveGrowth_transfer_pos E v r
  have hpl : 1 ≤ C * projectiveGrowth (transfer E v) p := by
    have h : C * C⁻¹ ≤ C * projectiveGrowth (transfer E v) p :=
      mul_le_mul_of_nonneg_left (transfer_growth_bounds E v M hM hv p).1 hC.le
    simpa only [mul_inv_cancel₀ hC.ne'] using h
  have hrl : 1 ≤ C * projectiveGrowth (transfer E v) r := by
    have h : C * C⁻¹ ≤ C * projectiveGrowth (transfer E v) r :=
      mul_le_mul_of_nonneg_left (transfer_growth_bounds E v M hM hv r).1 hC.le
    simpa only [mul_inv_cancel₀ hC.ne'] using h
  have hprod : 1 ≤ C ^ 2 *
      (projectiveGrowth (transfer E v) p * projectiveGrowth (transfer E v) r) := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (C * projectiveGrowth (transfer E v) p) *
          (C * projectiveGrowth (transfer E v) r) :=
        mul_le_mul hpl hrl (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      _ = _ := by ring
  rw [projectiveDistance_transfer_identity]
  apply (div_le_iff₀ (mul_pos hp hr)).mpr
  have h := mul_le_mul_of_nonneg_left hprod (projectiveDistance_nonneg p r)
  change projectiveDistance p r ≤ C ^ 2 * projectiveDistance p r *
    (projectiveGrowth (transfer E v) p * projectiveGrowth (transfer E v) r)
  calc
    _ = projectiveDistance p r * 1 := by ring
    _ ≤ projectiveDistance p r * (C ^ 2 *
        (projectiveGrowth (transfer E v) p * projectiveGrowth (transfer E v) r)) := h
    _ = _ := by ring

theorem projectiveDistance_transfer_lipschitz_of_abs_energy_le (E v R M : ℝ)
    (hR : 0 ≤ R) (hE : |E| ≤ R) (hM : 0 ≤ M) (hv : |v| ≤ M)
    (p r : ProjectivePoint) :
    projectiveDistance (transferProjective E v p) (transferProjective E v r) ≤
      (R + M + 2) ^ 2 * projectiveDistance p r := by
  have hs : (|E| + M + 2) ^ 2 ≤ (R + M + 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  exact (projectiveDistance_transfer_lipschitz E v M hM hv p r).trans
    (mul_le_mul_of_nonneg_right hs (projectiveDistance_nonneg p r))

def energyErrorConstant (a : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a * energyErrorConstant a n + 1

theorem energyErrorConstant_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ energyErrorConstant a n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (mul_nonneg ha ih) zero_le_one

theorem projectiveProcess_energy_distance_le (E E' R M : ℝ) (hR : 0 ≤ R)
    (hE : |E| ≤ R) (hM : 0 ≤ M) (ω : PotentialSpace) (hb : ∀ j, |ω j| ≤ M)
    (p : ProjectivePoint) (n : ℕ) :
    projectiveDistance (projectiveProcess E p n ω) (projectiveProcess E' p n ω) ≤
      energyErrorConstant ((R + M + 2) ^ 2) n * |E - E'| := by
  induction n with
  | zero => simpa only [projectiveProcess_zero, energyErrorConstant, zero_mul] using
      ((projectiveDistance_eq_zero_iff p p).mpr rfl).le
  | succ n ih =>
    rw [projectiveProcess_succ, projectiveProcess_succ]
    calc
      _ ≤ projectiveDistance
          (transferProjective E (ω n) (projectiveProcess E p n ω))
          (transferProjective E (ω n) (projectiveProcess E' p n ω)) + |E - E'| :=
        projectiveDistance_transfer_pair_energy_le E E' (ω n) _ _
      _ ≤ (R + M + 2) ^ 2 * projectiveDistance
          (projectiveProcess E p n ω) (projectiveProcess E' p n ω) + |E - E'| :=
        add_le_add (projectiveDistance_transfer_lipschitz_of_abs_energy_le
          E (ω n) R M hR hE hM (hb n) _ _) le_rfl
      _ ≤ (R + M + 2) ^ 2 *
          (energyErrorConstant ((R + M + 2) ^ 2) n * |E - E'|) + |E - E'| :=
        add_le_add (mul_le_mul_of_nonneg_left ih (sq_nonneg (R + M + 2))) le_rfl
      _ = _ := by rw [energyErrorConstant]; ring

theorem integrable_two_energy_projectiveDistance_rpow (law : PotentialLaw)
    (E E' s : ℝ) (hs : 0 ≤ s) (p r : ProjectivePoint) (n : ℕ) :
    Integrable (fun ω => (projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E' r n ω)) ^ s) (iidMeasure law) := by
  have hdist {Ω : Type} [MeasurableSpace Ω] {f g : Ω → ProjectivePoint}
      (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun ω => projectiveDistance (f ω) (g ω)) := by
    have hd : Measurable (fun z : ProjectivePoint × ProjectivePoint =>
        projectiveDistance z.1 z.2) := continuous_projectiveDistance_joint.measurable
    have hpair : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
    exact hd.comp hpair
  have hD := hdist (f := projectiveProcess E p n) (g := projectiveProcess E' r n)
    (projectiveProcess_measurable E p n) (projectiveProcess_measurable E' r n)
  have hmcomp := (Real.continuous_rpow_const hs).measurable.comp hD
  have hm : Measurable (fun ω : PotentialSpace =>
      (projectiveDistance (projectiveProcess E p n ω) (projectiveProcess E' r n ω)) ^ s) := by
    simpa only [Function.comp_def] using hmcomp
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
    exact Real.rpow_le_one (projectiveDistance_nonneg _ _) (projectiveDistance_le_one _ _) hs

/-- A common forced contraction block on a compact energy set. The second
energy may be any real number; boundedness is needed only for the reference
energy's same-energy direction bound. The two evolutions share the actual
iid potential sequence. -/
theorem exists_uniform_forced_projective_block_contraction (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' : ℝ, ∀ p r : ProjectivePoint,
        (∫ ω, (projectiveDistance (projectiveProcess E p N ω)
          (projectiveProcess E' r N ω)) ^ s ∂iidMeasure law) ≤
            q * (projectiveDistance p r) ^ s + C * |E - E'| ^ s := by
  obtain ⟨N, hN, s, q, hs, hs1, hq0, hq1, hblock⟩ :=
    exists_uniform_projective_block_contraction_on_compact law input K hK hne
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_abs.continuousOn
  let R : ℝ := max B 0
  have hR : 0 ≤ R := le_max_right _ _
  have hER : ∀ E ∈ K, |E| ≤ R := fun E hE =>
    (hB ⟨E, hE, rfl⟩).trans (le_max_left _ _)
  obtain ⟨M, hM, hb⟩ := iidMeasure_bounded_all_sites law
  let L : ℝ := energyErrorConstant ((R + M + 2) ^ 2) N
  have hL : 0 ≤ L := energyErrorConstant_nonneg _ (sq_nonneg _) N
  refine ⟨N, hN, s, q, L ^ s, hs, hs1, hq0, hq1, Real.rpow_nonneg hL s,
    fun E hE E' p r => ?_⟩
  have hpoint : ∀ᵐ ω ∂iidMeasure law,
      (projectiveDistance (projectiveProcess E p N ω) (projectiveProcess E' r N ω)) ^ s ≤
        (projectiveDistance (projectiveProcess E p N ω) (projectiveProcess E r N ω)) ^ s +
          L ^ s * |E - E'| ^ s := by
    filter_upwards [hb] with ω hω
    have hd := (projectiveDistance_triangle (projectiveProcess E p N ω)
      (projectiveProcess E r N ω) (projectiveProcess E' r N ω)).trans
      (add_le_add le_rfl (projectiveProcess_energy_distance_le E E' R M hR (hER E hE)
        hM ω hω r N))
    calc
      _ ≤ (projectiveDistance (projectiveProcess E p N ω)
          (projectiveProcess E r N ω) + L * |E - E'|) ^ s :=
        Real.rpow_le_rpow (projectiveDistance_nonneg _ _) hd hs.le
      _ ≤ (projectiveDistance (projectiveProcess E p N ω)
          (projectiveProcess E r N ω)) ^ s + (L * |E - E'|) ^ s :=
        Real.rpow_add_le_add_rpow (projectiveDistance_nonneg _ _)
          (mul_nonneg hL (abs_nonneg _)) hs.le hs1
      _ = _ := by rw [Real.mul_rpow hL (abs_nonneg _)]
  have hiSum : Integrable (fun ω =>
      (projectiveDistance (projectiveProcess E p N ω) (projectiveProcess E r N ω)) ^ s +
        L ^ s * |E - E'| ^ s) (iidMeasure law) :=
    (integrable_projectiveDistance_product_rpow law E N p r s hs.le).add
      (integrable_const (L ^ s * |E - E'| ^ s))
  have hi := integral_mono_ae
    (integrable_two_energy_projectiveDistance_rpow law E E' s hs.le p r N)
    hiSum hpoint
  rw [integral_add (integrable_projectiveDistance_product_rpow law E N p r s hs.le)
    (integrable_const (L ^ s * |E - E'| ^ s)), integral_const] at hi
  simp only [probReal_univ, one_smul] at hi
  exact hi.trans (add_le_add (hblock E hE p r) le_rfl)

end FixedCouplingPoisson.Furstenberg
