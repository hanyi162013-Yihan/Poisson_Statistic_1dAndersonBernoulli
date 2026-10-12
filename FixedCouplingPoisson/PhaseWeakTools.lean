import FixedCouplingPoisson.ProjectiveTopology
import FixedCouplingPoisson.CanonicalPhase
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual determinant-distance tools for weak phase convergence

This work draft proves joint continuity and compact test-function control of
our genuine Euclidean projective determinant distance. It does not assume or
assert stochastic contraction, which belongs to the separate actual-product
argument.
-/
noncomputable section
namespace FixedCouplingPoisson

/-- A uniform actual one-step displacement bound, independent of energy and potential. -/
theorem canonicalPhase_displacement_le (E v θ : ℝ) :
    |canonicalPhase E v θ - θ| ≤ 2 * Real.pi := by
  have hr := reducedPhase_mem θ
  have hf := closedChartPhase_mem E v (reducedPhase θ) hr
  have hdiff : canonicalPhase E v θ - θ =
      closedChartPhase E v (reducedPhase θ) - reducedPhase θ := by
    rw [canonicalPhase_cell_formula]
    unfold reducedPhase
    ring
  rw [hdiff, abs_le]
  constructor <;> linarith [hr.1, hr.2, hf.1, hf.2, Real.pi_pos]

end FixedCouplingPoisson
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix
open scoped Topology

/-- The open nonzero-vector quotient remains a quotient under a pair of copies. -/
theorem projectivize_pair_isQuotientMap :
    Topology.IsQuotientMap (Prod.map projectivize projectivize) := by
  have hq : IsOpenQuotientMap projectivize :=
    ⟨projectivize_isQuotientMap.surjective, continuous_projectivize,
      isOpenMap_projectivize⟩
  exact (hq.prodMap hq).isQuotientMap

/-- The genuine determinant distance is jointly continuous on the projective line. -/
theorem continuous_projectiveDistance_joint :
    Continuous (fun z : ProjectivePoint × ProjectivePoint => projectiveDistance z.1 z.2) := by
  apply projectivize_pair_isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : NonzeroVector × NonzeroVector =>
    projectiveDistance (projectivize z.1) (projectivize z.2))
  have heq : (fun z : NonzeroVector × NonzeroVector =>
      projectiveDistance (projectivize z.1) (projectivize z.2)) =
      (fun z : NonzeroVector × NonzeroVector => determinantDistance z.1 z.2) := by
    funext z
    exact projectiveDistance_mk z.1 z.2 z.1.2 z.2.2
  rw [heq]
  have hu : Continuous (fun z : NonzeroVector × NonzeroVector => (z.1 : Vector2)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun z : NonzeroVector × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hu0 := (continuous_apply 0).comp hu
  have hu1 := (continuous_apply 1).comp hu
  have hv0 := (continuous_apply 0).comp hv
  have hv1 := (continuous_apply 1).comp hv
  have hw : Continuous (fun z : NonzeroVector × NonzeroVector => wedge z.1 z.2) :=
    (hu0.mul hv1).sub (hu1.mul hv0)
  exact hw.abs.div ((continuous_euclideanNorm.comp hu).mul (continuous_euclideanNorm.comp hv))
    (fun z => (mul_pos (euclideanNorm_pos z.1 z.1.2) (euclideanNorm_pos z.2 z.2.2)).ne')

/-- Squared determinant plus squared scalar product is the product of Euclidean squares. -/
theorem wedge_euclidean_identity (u v : Vector2) :
    (euclideanNorm u * euclideanNorm v) ^ 2 - wedge u v ^ 2 =
      (u 0 * v 0 + u 1 * v 1) ^ 2 := by
  rw [mul_pow, euclideanNorm_sq, euclideanNorm_sq]
  unfold euclideanNormSq wedge
  ring

theorem wedge_abs_le_euclideanNorm_mul (u v : Vector2) :
    |wedge u v| ≤ euclideanNorm u * euclideanNorm v := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg (euclideanNorm_nonneg u) (euclideanNorm_nonneg v))
  have h := wedge_euclidean_identity u v
  linarith [sq_nonneg (u 0 * v 0 + u 1 * v 1)]

/-- This distance is at most one with the actual Euclidean normalization. -/
theorem projectiveDistance_le_one (p q : ProjectivePoint) : projectiveDistance p q ≤ 1 := by
  unfold projectiveDistance determinantDistance
  apply (div_le_one (mul_pos (euclideanNorm_pos p.rep p.rep_nonzero)
    (euclideanNorm_pos q.rep q.rep_nonzero))).mpr
  exact wedge_abs_le_euclideanNorm_mul p.rep q.rep

theorem projectiveDistance_pos_iff (p q : ProjectivePoint) :
    0 < projectiveDistance p q ↔ p ≠ q := by
  have hnonneg : 0 ≤ projectiveDistance p q := by
    unfold projectiveDistance determinantDistance
    exact div_nonneg (abs_nonneg _) (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))
  constructor
  · intro hpq heq
    have hz := (projectiveDistance_eq_zero_iff p q).mpr heq
    exact hpq.ne' hz
  · intro hpq
    exact lt_of_le_of_ne hnonneg (Ne.symm ((projectiveDistance_eq_zero_iff p q).not.mpr hpq))

/-- Compactness converts genuine determinant-distance smallness into smallness
for any continuous real test, without replacing it by a sup-norm metric. -/
theorem continuous_test_projective_modulus (f : C(ProjectivePoint, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ProjectivePoint,
      projectiveDistance p q < δ → |f p - f q| < ε := by
  let bad : Set (ProjectivePoint × ProjectivePoint) := {z | ε ≤ |f z.1 - f z.2|}
  have hbad : IsClosed bad := isClosed_le continuous_const
    ((f.continuous.comp continuous_fst).sub (f.continuous.comp continuous_snd)).abs
  have hpos : ∀ z ∈ bad, 0 < projectiveDistance z.1 z.2 := by
    intro z hz
    apply (projectiveDistance_pos_iff z.1 z.2).mpr
    intro heq
    have hz' : ε ≤ |f z.1 - f z.2| := hz
    rw [heq, sub_self, abs_zero] at hz'
    linarith
  obtain ⟨δ, hδ, hbound⟩ := hbad.isCompact.exists_forall_le'
    continuous_projectiveDistance_joint.continuousOn hpos
  refine ⟨δ, hδ, fun p q hpq => ?_⟩
  by_contra hf
  have hmem : (p, q) ∈ bad := le_of_not_gt hf
  exact (hbound (p, q) hmem).not_gt hpq

/-- A continuous test admits an additive modulus controlled by any positive
power of the genuine determinant distance. -/
theorem continuous_test_projective_moment_bound (f : C(ProjectivePoint, ℝ))
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ProjectivePoint,
      |f p - f q| ≤ ε + C * projectiveDistance p q ^ s := by
  obtain ⟨δ, hδ, hmod⟩ := continuous_test_projective_modulus f ε hε
  have hδpow : 0 < δ ^ s := Real.rpow_pos_of_pos hδ s
  let C := 2 * ‖f‖ / δ ^ s
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) (norm_nonneg f)) hδpow.le
  refine ⟨C, hC, fun p q => ?_⟩
  have hD : 0 ≤ projectiveDistance p q := by
    by_cases hpq : p = q
    · exact ((projectiveDistance_eq_zero_iff p q).mpr hpq).symm.le
    · exact ((projectiveDistance_pos_iff p q).mpr hpq).le
  by_cases hsmall : projectiveDistance p q < δ
  · have hnear := hmod p q hsmall
    have hnonneg := mul_nonneg hC (Real.rpow_nonneg hD s)
    linarith
  · have hpow := Real.rpow_le_rpow hδ.le (le_of_not_gt hsmall) hs
    have hlarge : 2 * ‖f‖ ≤ C * projectiveDistance p q ^ s := by
      calc
        2 * ‖f‖ = C * δ ^ s := (div_mul_cancel₀ _ hδpow.ne').symm
        _ ≤ C * projectiveDistance p q ^ s := mul_le_mul_of_nonneg_left hpow hC
    have hbound : |f p - f q| ≤ 2 * ‖f‖ := by
      calc
        |f p - f q| = ‖f p - f q‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖f p‖ + ‖f q‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm p) (f.norm_coe_le_norm q)
        _ = 2 * ‖f‖ := by ring
    linarith

end FixedCouplingPoisson.Furstenberg
