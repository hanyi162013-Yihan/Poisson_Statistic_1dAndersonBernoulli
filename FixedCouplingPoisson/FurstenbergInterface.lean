import FixedCouplingPoisson.Projective
import FixedCouplingPoisson.Law
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The external qualitative Furstenberg input, on the actual model

The topology below is the quotient topology of the actual nonzero vectors
`Fin 2 → ℝ`, and the measurable structure is its Borel sigma algebra.
The transition law is an actual product-measure pushforward under the proved
transfer and inverse-transfer projective actions. The log cocycle uses the
explicit Euclidean norm from `Projective`, never the function type's sup norm.

`QualitativeData` and `Input` are CONDITIONAL interfaces. No inhabitant is
constructed or assumed globally. Their only external conclusions are the
unique forward/inverse stationary probabilities, vanishing point masses, and
the positive forward/inverse stationary log-norm means. These mean assumptions
are the qualitative Furstenberg formula/positivity inputs for the respective
random products; they do not assert a contraction conclusion. Assuming them
directly removes the need for an Oseledets stable-line input in the fixed-block
argument. All log-ratio bounds and integrability below are instead proved from
the bounded potential law and the explicit inverse identities.
Uniform Cesàro convergence, fixed-block contraction, occupation, IDS, Sturm,
and Poisson conclusions are deliberately absent from this interface.
-/

noncomputable section

namespace FixedCouplingPoisson.Furstenberg

open MeasureTheory Matrix
open scoped Topology

abbrev NonzeroVector := {u : Vector2 // u ≠ 0}

/-- The standard quotient topology, explicitly on the algebraic projective
space already used by the deterministic transfer lemmas. -/
instance projectiveTopology : TopologicalSpace ProjectivePoint :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℝ Vector2)))

/-- Only the Borel sigma algebra of that quotient topology is used. -/
instance projectiveMeasurableSpace : MeasurableSpace ProjectivePoint := borel ProjectivePoint

instance projectiveBorelSpace : BorelSpace ProjectivePoint := ⟨rfl⟩

def projectivize : NonzeroVector → ProjectivePoint := Projectivization.mk' ℝ

theorem projectivize_isQuotientMap : Topology.IsQuotientMap projectivize :=
  isQuotientMap_quotient_mk'

theorem continuous_projectivize : Continuous projectivize :=
  projectivize_isQuotientMap.continuous

theorem continuous_euclideanNorm : Continuous euclideanNorm :=
  Real.continuous_sqrt.comp
    (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))

theorem continuous_transfer : Continuous (fun z : ℝ × ℝ => transfer z.1 z.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_fst.sub continuous_snd | exact continuous_const

theorem continuous_transferInv : Continuous (fun z : ℝ × ℝ => transferInv z.1 z.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_fst.sub continuous_snd | exact continuous_const

/-- A normalized nonzero vector has Euclidean norm one. -/
def normalizeVector (u : Vector2) : Vector2 := (euclideanNorm u)⁻¹ • u

theorem euclideanNorm_normalize (u : Vector2) (hu : u ≠ 0) :
    euclideanNorm (normalizeVector u) = 1 := by
  rw [normalizeVector, euclideanNorm_smul,
    abs_of_pos (inv_pos.mpr (euclideanNorm_pos u hu))]
  exact inv_mul_cancel₀ (euclideanNorm_pos u hu).ne'

/-- The actual Euclidean norm ratio for a matrix and a nonzero vector. -/
def vectorGrowth (A : Matrix2) (u : Vector2) : ℝ :=
  euclideanNorm (A *ᵥ u) / euclideanNorm u

theorem vectorGrowth_smul (A : Matrix2) (a : ℝ) (ha : a ≠ 0) (u : Vector2) :
    vectorGrowth A (a • u) = vectorGrowth A u := by
  simp only [vectorGrowth, Matrix.mulVec_smul, euclideanNorm_smul]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr ha)

theorem vectorGrowth_eq_normalized (A : Matrix2) (u : Vector2) :
    vectorGrowth A u = euclideanNorm (A *ᵥ normalizeVector u) := by
  rw [normalizeVector, Matrix.mulVec_smul, euclideanNorm_smul,
    abs_of_nonneg (inv_nonneg.mpr (euclideanNorm_nonneg u))]
  exact div_eq_inv_mul _ _

/-- The Euclidean growth ratio descends by proved scale invariance. -/
def projectiveGrowth (A : Matrix2) : ProjectivePoint → ℝ :=
  Projectivization.lift (fun u : NonzeroVector => vectorGrowth A u)
    (by
      intro u w a h
      have ha : a ≠ 0 := by
        intro ha
        exact u.2 (by simpa [ha] using h)
      change vectorGrowth A (u : Vector2) = vectorGrowth A (w : Vector2)
      rw [h]
      exact vectorGrowth_smul A a ha w)

@[simp] theorem projectiveGrowth_mk (A : Matrix2) (u : Vector2) (hu : u ≠ 0) :
    projectiveGrowth A (Projectivization.mk ℝ u hu) = vectorGrowth A u := rfl

def projectiveLogGrowth (A : Matrix2) (p : ProjectivePoint) : ℝ :=
  Real.log (projectiveGrowth A p)

/-- This representative is used only to display the normalized formula;
continuity is proved through the quotient, without a measurable choice of rep. -/
def unitRepresentative (p : ProjectivePoint) : Vector2 := normalizeVector p.rep

theorem unitRepresentative_norm (p : ProjectivePoint) :
    euclideanNorm (unitRepresentative p) = 1 :=
  euclideanNorm_normalize p.rep p.rep_nonzero

theorem projectiveLogGrowth_eq_unitRepresentative (A : Matrix2) (p : ProjectivePoint) :
    projectiveLogGrowth A p = Real.log (euclideanNorm (A *ᵥ unitRepresentative p)) := by
  have h : projectiveGrowth A p = vectorGrowth A p.rep := by
    conv_lhs => rw [← Projectivization.mk_rep p]
    rfl
  rw [projectiveLogGrowth, h, vectorGrowth_eq_normalized]
  rfl

theorem continuous_projectiveGrowth {S : Type*} [TopologicalSpace S]
    [LocallyCompactSpace S] (A : S → Matrix2) (hA : Continuous A) :
    Continuous (fun z : S × ProjectivePoint => projectiveGrowth (A z.1) z.2) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : S × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hnum := continuous_euclideanNorm.comp ((hA.comp continuous_fst).matrix_mulVec hv)
  have hden := continuous_euclideanNorm.comp hv
  exact hnum.div hden (fun z => (euclideanNorm_pos z.2 z.2.2).ne')

theorem continuous_transferProjective_joint :
    Continuous (fun z : (ℝ × ℝ) × ProjectivePoint =>
      transferProjective z.1.1 z.1.2 z.2) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : (ℝ × ℝ) × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hmul := (continuous_transfer.comp continuous_fst).matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun z =>
    sl2_mulVec_ne_zero (transfer z.1.1 z.1.2) (transfer_det _ _) z.2 z.2.2)

theorem continuous_transferInverseProjective_joint :
    Continuous (fun z : (ℝ × ℝ) × ProjectivePoint =>
      transferInverseProjective z.1.1 z.1.2 z.2) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : (ℝ × ℝ) × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hmul := (continuous_transferInv.comp continuous_fst).matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun z =>
    transferInv_mulVec_ne_zero z.1.1 z.1.2 z.2 z.2.2)

theorem projectiveGrowth_transfer_pos (E v : ℝ) (p : ProjectivePoint) :
    0 < projectiveGrowth (transfer E v) p := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [projectiveGrowth_mk, vectorGrowth]
    exact div_pos
      (euclideanNorm_pos _ (sl2_mulVec_ne_zero _ (transfer_det E v) u hu))
      (euclideanNorm_pos u hu)

theorem projectiveGrowth_transferInv_pos (E v : ℝ) (p : ProjectivePoint) :
    0 < projectiveGrowth (transferInv E v) p := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [projectiveGrowth_mk, vectorGrowth]
    exact div_pos (euclideanNorm_pos _ (transferInv_mulVec_ne_zero E v u hu))
      (euclideanNorm_pos u hu)

def transferLogCocycle (E v : ℝ) (p : ProjectivePoint) : ℝ :=
  projectiveLogGrowth (transfer E v) p

def inverseTransferLogCocycle (E v : ℝ) (p : ProjectivePoint) : ℝ :=
  projectiveLogGrowth (transferInv E v) p

theorem continuous_transferLogCocycle_joint :
    Continuous (fun z : (ℝ × ℝ) × ProjectivePoint => transferLogCocycle z.1.1 z.1.2 z.2) :=
  (continuous_projectiveGrowth (fun z : ℝ × ℝ => transfer z.1 z.2) continuous_transfer).log
    (fun z => (projectiveGrowth_transfer_pos z.1.1 z.1.2 z.2).ne')

theorem continuous_inverseTransferLogCocycle_joint :
    Continuous (fun z : (ℝ × ℝ) × ProjectivePoint =>
      inverseTransferLogCocycle z.1.1 z.1.2 z.2) :=
  (continuous_projectiveGrowth (fun z : ℝ × ℝ => transferInv z.1 z.2) continuous_transferInv).log
    (fun z => (projectiveGrowth_transferInv_pos z.1.1 z.1.2 z.2).ne')

def forwardStep (E : ℝ) (z : ℝ × ProjectivePoint) : ProjectivePoint :=
  transferProjective E z.1 z.2

def inverseStep (E : ℝ) (z : ℝ × ProjectivePoint) : ProjectivePoint :=
  transferInverseProjective E z.1 z.2

theorem continuous_energyInsertion (E : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => ((E, z.1), z.2)) := by
  have h : Continuous (fun z : ℝ × ProjectivePoint => (E, z.1)) :=
    continuous_const.prodMk continuous_fst
  exact h.prodMk continuous_snd

theorem continuous_transfer_fixed (E : ℝ) : Continuous (transfer E) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_const.sub continuous_id | exact continuous_const

theorem continuous_transferInv_fixed (E : ℝ) : Continuous (transferInv E) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_const.sub continuous_id | exact continuous_const

theorem continuous_forwardStep (E : ℝ) : Continuous (forwardStep E) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : ℝ × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hmul := ((continuous_transfer_fixed E).comp continuous_fst).matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun z =>
    sl2_mulVec_ne_zero (transfer E z.1) (transfer_det _ _) z.2 z.2.2)

theorem continuous_inverseStep (E : ℝ) : Continuous (inverseStep E) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : ℝ × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hmul := ((continuous_transferInv_fixed E).comp continuous_fst).matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun z =>
    transferInv_mulVec_ne_zero E z.1 z.2 z.2.2)

theorem measurable_forwardStep (E : ℝ) : Measurable (forwardStep E) :=
  (continuous_forwardStep E).measurable

theorem measurable_inverseStep (E : ℝ) : Measurable (inverseStep E) :=
  (continuous_inverseStep E).measurable

/-- Squared Frobenius norm, used only for an elementary coordinate bound. -/
def coefficientSquareSum (A : Matrix2) : ℝ :=
  A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2

theorem euclideanNormSq_mulVec_le (A : Matrix2) (u : Vector2) :
    euclideanNormSq (A *ᵥ u) ≤ coefficientSquareSum A * euclideanNormSq u := by
  have hid : coefficientSquareSum A * euclideanNormSq u - euclideanNormSq (A *ᵥ u) =
      (A 0 0 * u 1 - A 0 1 * u 0) ^ 2 +
        (A 1 0 * u 1 - A 1 1 * u 0) ^ 2 := by
    simp only [coefficientSquareSum, euclideanNormSq, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring
  exact sub_nonneg.mp (hid ▸ add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem euclideanNorm_mulVec_le (A : Matrix2) (C : ℝ) (hC : 0 ≤ C)
    (hA : coefficientSquareSum A ≤ C ^ 2) (u : Vector2) :
    euclideanNorm (A *ᵥ u) ≤ C * euclideanNorm u := by
  apply le_of_sq_le_sq _ (mul_nonneg hC (euclideanNorm_nonneg u))
  calc
    euclideanNorm (A *ᵥ u) ^ 2 = euclideanNormSq (A *ᵥ u) := euclideanNorm_sq _
    _ ≤ coefficientSquareSum A * euclideanNormSq u := euclideanNormSq_mulVec_le A u
    _ ≤ C ^ 2 * euclideanNormSq u := mul_le_mul_of_nonneg_right hA (euclideanNormSq_nonneg u)
    _ = (C * euclideanNorm u) ^ 2 := by rw [mul_pow, euclideanNorm_sq]

theorem coefficientSquareSum_transfer (E v : ℝ) :
    coefficientSquareSum (transfer E v) = (E - v) ^ 2 + 2 := by
  simp [coefficientSquareSum, transfer]
  ring

theorem coefficientSquareSum_transferInv (E v : ℝ) :
    coefficientSquareSum (transferInv E v) = (E - v) ^ 2 + 2 := by
  simp [coefficientSquareSum, transferInv]
  ring

theorem transfer_coefficient_bound (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M) :
    (E - v) ^ 2 + 2 ≤ (|E| + M + 2) ^ 2 := by
  have ha : |E - v| ≤ |E| + M := (abs_sub E v).trans (add_le_add (le_refl |E|) hv)
  have hsq : |E - v| ^ 2 ≤ (|E| + M) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) hM)).mpr ha
  rw [sq_abs] at hsq
  nlinarith [abs_nonneg E]

theorem transfer_norm_bound (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M) (u : Vector2) :
    euclideanNorm (transfer E v *ᵥ u) ≤ (|E| + M + 2) * euclideanNorm u := by
  apply euclideanNorm_mulVec_le _ _ (by positivity)
  rw [coefficientSquareSum_transfer]
  exact transfer_coefficient_bound E v M hM hv

theorem inverse_norm_bound (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M) (u : Vector2) :
    euclideanNorm (transferInv E v *ᵥ u) ≤ (|E| + M + 2) * euclideanNorm u := by
  apply euclideanNorm_mulVec_le _ _ (by positivity)
  rw [coefficientSquareSum_transferInv]
  exact transfer_coefficient_bound E v M hM hv

theorem transfer_growth_bounds (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M)
    (p : ProjectivePoint) :
    (|E| + M + 2)⁻¹ ≤ projectiveGrowth (transfer E v) p ∧
      projectiveGrowth (transfer E v) p ≤ |E| + M + 2 := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [projectiveGrowth_mk, vectorGrowth]
    have hn := euclideanNorm_pos u hu
    have hC : 0 < |E| + M + 2 := by positivity
    have hupper := transfer_norm_bound E v M hM hv u
    have hlower := inverse_norm_bound E v M hM hv (transfer E v *ᵥ u)
    simp only [Matrix.mulVec_mulVec, transferInv_mul_transfer, Matrix.one_mulVec] at hlower
    constructor
    · apply (le_div_iff₀ hn).mpr
      apply (inv_mul_le_iff₀ hC).mpr
      simpa only [mul_comm] using hlower
    · exact (div_le_iff₀ hn).mpr hupper

theorem inverse_growth_bounds (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M)
    (p : ProjectivePoint) :
    (|E| + M + 2)⁻¹ ≤ projectiveGrowth (transferInv E v) p ∧
      projectiveGrowth (transferInv E v) p ≤ |E| + M + 2 := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [projectiveGrowth_mk, vectorGrowth]
    have hn := euclideanNorm_pos u hu
    have hC : 0 < |E| + M + 2 := by positivity
    have hupper := inverse_norm_bound E v M hM hv u
    have hlower := transfer_norm_bound E v M hM hv (transferInv E v *ᵥ u)
    simp only [Matrix.mulVec_mulVec, transfer_mul_transferInv, Matrix.one_mulVec] at hlower
    constructor
    · apply (le_div_iff₀ hn).mpr
      apply (inv_mul_le_iff₀ hC).mpr
      simpa only [mul_comm] using hlower
    · exact (div_le_iff₀ hn).mpr hupper

/-- The logarithm bound follows from the explicit bounded potential and the
proved two-sided inverse. It is not part of the external Furstenberg input. -/
theorem abs_transferLogCocycle_le (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M)
    (p : ProjectivePoint) : |transferLogCocycle E v p| ≤ Real.log (|E| + M + 2) := by
  change |Real.log (projectiveGrowth (transfer E v) p)| ≤ Real.log (|E| + M + 2)
  have hb := transfer_growth_bounds E v M hM hv p
  have hC : 0 < |E| + M + 2 := by positivity
  have hg := projectiveGrowth_transfer_pos E v p
  apply abs_le.mpr
  constructor
  · have h := Real.log_le_log (inv_pos.mpr hC) hb.1
    simpa only [Real.log_inv] using h
  · exact Real.log_le_log hg hb.2

theorem abs_inverseTransferLogCocycle_le (E v M : ℝ) (hM : 0 ≤ M) (hv : |v| ≤ M)
    (p : ProjectivePoint) :
    |inverseTransferLogCocycle E v p| ≤ Real.log (|E| + M + 2) := by
  change |Real.log (projectiveGrowth (transferInv E v) p)| ≤ Real.log (|E| + M + 2)
  have hb := inverse_growth_bounds E v M hM hv p
  have hC : 0 < |E| + M + 2 := by positivity
  have hg := projectiveGrowth_transferInv_pos E v p
  apply abs_le.mpr
  constructor
  · have h := Real.log_le_log (inv_pos.mpr hC) hb.1
    simpa only [Real.log_inv] using h
  · exact Real.log_le_log hg hb.2

/-- The next potential and initial projective direction are independent here. -/
def inputDistribution (law : PotentialLaw) (ν : ProbabilityMeasure ProjectivePoint) :
    ProbabilityMeasure (ℝ × ProjectivePoint) :=
  ⟨law.measure.prod (ν : Measure ProjectivePoint), inferInstance⟩

theorem continuous_transferLogCocycle (E : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => transferLogCocycle E z.1 z.2) :=
  (continuous_projectiveGrowth (transfer E) (continuous_transfer_fixed E)).log
    (fun z => (projectiveGrowth_transfer_pos E z.1 z.2).ne')

theorem continuous_inverseTransferLogCocycle (E : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => inverseTransferLogCocycle E z.1 z.2) :=
  (continuous_projectiveGrowth (transferInv E) (continuous_transferInv_fixed E)).log
    (fun z => (projectiveGrowth_transferInv_pos E z.1 z.2).ne')

/-- Uniformity is over every projective direction and almost every potential. -/
theorem ae_uniform_logCocycle_bound (law : PotentialLaw) (E : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ v ∂law.measure, ∀ p : ProjectivePoint,
      |transferLogCocycle E v p| ≤ C := by
  obtain ⟨M, hM, hb⟩ := law.bounded
  have hC : 1 ≤ |E| + M + 2 := by linarith [abs_nonneg E]
  refine ⟨Real.log (|E| + M + 2), Real.log_nonneg hC, ?_⟩
  exact hb.mono fun v hv p => abs_transferLogCocycle_le E v M hM hv p

theorem ae_uniform_inverseLogCocycle_bound (law : PotentialLaw) (E : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ v ∂law.measure, ∀ p : ProjectivePoint,
      |inverseTransferLogCocycle E v p| ≤ C := by
  obtain ⟨M, hM, hb⟩ := law.bounded
  have hC : 1 ≤ |E| + M + 2 := by linarith [abs_nonneg E]
  refine ⟨Real.log (|E| + M + 2), Real.log_nonneg hC, ?_⟩
  exact hb.mono fun v hv p => abs_inverseTransferLogCocycle_le E v M hM hv p

/-- Actual product-law integrability, proved for every input probability,
before invoking any stationary probability or positive-mean assumption. -/
theorem integrable_transferLogCocycle (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    Integrable (fun z : ℝ × ProjectivePoint => transferLogCocycle E z.1 z.2)
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  obtain ⟨C, _, hb⟩ := ae_uniform_logCocycle_bound law E
  apply (integrable_const C).mono' (continuous_transferLogCocycle E).measurable.aestronglyMeasurable
  have hprod : ∀ᵐ z ∂law.measure.prod (ν : Measure ProjectivePoint),
      ∀ p : ProjectivePoint, |transferLogCocycle E z.1 p| ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae hb
  exact hprod.mono fun z hz => by simpa only [Real.norm_eq_abs] using hz z.2

theorem integrable_inverseTransferLogCocycle (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    Integrable (fun z : ℝ × ProjectivePoint => inverseTransferLogCocycle E z.1 z.2)
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  obtain ⟨C, _, hb⟩ := ae_uniform_inverseLogCocycle_bound law E
  apply (integrable_const C).mono'
    (continuous_inverseTransferLogCocycle E).measurable.aestronglyMeasurable
  have hprod : ∀ᵐ z ∂law.measure.prod (ν : Measure ProjectivePoint),
      ∀ p : ProjectivePoint, |inverseTransferLogCocycle E z.1 p| ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae hb
  exact hprod.mono fun z hz => by simpa only [Real.norm_eq_abs] using hz z.2

def forwardDistribution (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) : ProbabilityMeasure ProjectivePoint :=
  (inputDistribution law ν).map (measurable_forwardStep E).aemeasurable

def inverseDistribution (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) : ProbabilityMeasure ProjectivePoint :=
  (inputDistribution law ν).map (measurable_inverseStep E).aemeasurable

def ForwardStationary (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) : Prop := forwardDistribution law E ν = ν

def InverseStationary (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) : Prop := inverseDistribution law E ν = ν

/-- This is an actual Bochner integral under the independent product law. -/
def stationaryMean (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) : ℝ :=
  ∫ z, transferLogCocycle E z.1 z.2 ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint))

def inverseStationaryMean (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) : ℝ :=
  ∫ z, inverseTransferLogCocycle E z.1 z.2
    ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint))

theorem forward_stationary_integral (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (f : ProjectivePoint → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂(ν : Measure ProjectivePoint)) =
      ∫ z, f (forwardStep E z) ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  have hmap := congrArg (fun μ : ProbabilityMeasure ProjectivePoint =>
    (μ : Measure ProjectivePoint)) hν
  change (inputDistribution law ν : Measure (ℝ × ProjectivePoint)).map (forwardStep E) =
    (ν : Measure ProjectivePoint) at hmap
  rw [← hmap]
  exact integral_map (measurable_forwardStep E).aemeasurable hf.aestronglyMeasurable

theorem inverse_stationary_integral (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : InverseStationary law E ν)
    (f : ProjectivePoint → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂(ν : Measure ProjectivePoint)) =
      ∫ z, f (inverseStep E z) ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  have hmap := congrArg (fun μ : ProbabilityMeasure ProjectivePoint =>
    (μ : Measure ProjectivePoint)) hν
  change (inputDistribution law ν : Measure (ℝ × ProjectivePoint)).map (inverseStep E) =
    (ν : Measure ProjectivePoint) at hmap
  rw [← hmap]
  exact integral_map (measurable_inverseStep E).aemeasurable hf.aestronglyMeasurable

/-- Positive actual mean already rules out Bochner's nonintegrable default. -/
theorem integrable_logCocycle_of_mean_pos (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hmean : 0 < stationaryMean law E ν) :
    Integrable (fun z : ℝ × ProjectivePoint => transferLogCocycle E z.1 z.2)
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  by_contra h
  have hz : stationaryMean law E ν = 0 := integral_undef h
  rw [hz] at hmean
  exact lt_irrefl 0 hmean

/-- The ONLY external conclusions: qualitative Furstenberg theory on the
actual transfer law. No inhabitant is supplied in this development. -/
structure QualitativeData (law : PotentialLaw) (E : ℝ) where
  forwardMeasure : ProbabilityMeasure ProjectivePoint
  inverseMeasure : ProbabilityMeasure ProjectivePoint
  forward_stationary : ForwardStationary law E forwardMeasure
  inverse_stationary : InverseStationary law E inverseMeasure
  forward_unique : ∀ ν, ForwardStationary law E ν → ν = forwardMeasure
  inverse_unique : ∀ ν, InverseStationary law E ν → ν = inverseMeasure
  forward_null_singletons : ∀ p, (forwardMeasure : Measure ProjectivePoint) {p} = 0
  inverse_null_singletons : ∀ p, (inverseMeasure : Measure ProjectivePoint) {p} = 0
  stationary_mean_pos : 0 < stationaryMean law E forwardMeasure
  inverse_stationary_mean_pos : 0 < inverseStationaryMean law E inverseMeasure

/-- A family of external qualitative conclusions, passed explicitly as a
parameter wherever used. This declaration asserts no global instance. -/
structure Input (law : PotentialLaw) where
  atEnergy : ∀ E : ℝ, QualitativeData law E

end FixedCouplingPoisson.Furstenberg
