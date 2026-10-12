import FixedCouplingPoisson.ProjectiveTopology
import Mathlib.MeasureTheory.Integral.Prod

/-! Coordinate exchange conjugates the actual forward and inverse transfers.
The exchange preserves the genuine Euclidean norm. No qualitative input is used.
Actual checking records are maintained beside the source. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix
open scoped Topology

def flipVector (u : Vector2) : Vector2 := ![u 1, u 0]

@[simp] theorem flipVector_involutive (u : Vector2) : flipVector (flipVector u) = u := by
  ext i
  fin_cases i <;> simp [flipVector]

theorem flipVector_injective : Function.Injective flipVector :=
  (show Function.Involutive flipVector from flipVector_involutive).injective

@[simp] theorem flipVector_zero : flipVector 0 = 0 := by
  ext i
  fin_cases i <;> simp [flipVector]

theorem flipVector_ne_zero (u : Vector2) (hu : u ≠ 0) : flipVector u ≠ 0 := by
  intro h
  exact hu (flipVector_injective (h.trans flipVector_zero.symm))

def flipVectorLinear : Vector2 →ₗ[ℝ] Vector2 where
  toFun := flipVector
  map_add' u v := by ext i; fin_cases i <;> simp [flipVector]
  map_smul' a u := by ext i; fin_cases i <;> simp [flipVector]

@[simp] theorem euclideanNorm_flipVector (u : Vector2) :
    euclideanNorm (flipVector u) = euclideanNorm u := by
  simp only [euclideanNorm, euclideanNormSq, flipVector, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_comm]

theorem flipVector_transfer (E v : ℝ) (u : Vector2) :
    flipVector (transfer E v *ᵥ u) = transferInv E v *ᵥ flipVector u := by
  ext i
  fin_cases i <;>
    simp [flipVector, transfer, transferInv, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, sub_eq_add_neg, add_comm]

theorem flipVector_transferInv (E v : ℝ) (u : Vector2) :
    flipVector (transferInv E v *ᵥ u) = transfer E v *ᵥ flipVector u := by
  have h := congrArg flipVector (flipVector_transfer E v (flipVector u))
  simpa only [flipVector_involutive] using h.symm

def flipProjective : ProjectivePoint → ProjectivePoint :=
  Projectivization.map flipVectorLinear flipVector_injective

@[simp] theorem flipProjective_mk (u : Vector2) (hu : u ≠ 0) :
    flipProjective (Projectivization.mk ℝ u hu) =
      Projectivization.mk ℝ (flipVector u) (flipVector_ne_zero u hu) := rfl

@[simp] theorem flipProjective_involutive (p : ProjectivePoint) :
    flipProjective (flipProjective p) = p := by
  induction p using Projectivization.ind with
  | h u hu =>
    simp only [flipProjective_mk, flipVector_involutive]

theorem flipProjective_injective : Function.Injective flipProjective :=
  (show Function.Involutive flipProjective from flipProjective_involutive).injective

theorem continuous_flipVector : Continuous flipVector := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa [flipVector] using (continuous_apply (1 : Fin 2) :
      Continuous (fun u : Vector2 => u 1))
  · simpa [flipVector] using (continuous_apply (0 : Fin 2) :
      Continuous (fun u : Vector2 => u 0))

theorem continuous_flipProjective : Continuous flipProjective := by
  apply projectivize_isQuotientMap.continuous_iff.mpr
  have h := continuous_flipVector.comp (continuous_subtype_val :
    Continuous (fun u : NonzeroVector => (u : Vector2)))
  exact continuous_projectivize.comp (h.subtype_mk fun u => flipVector_ne_zero u u.2)

def flipProjectiveHomeomorph : ProjectivePoint ≃ₜ ProjectivePoint where
  toFun := flipProjective
  invFun := flipProjective
  left_inv := flipProjective_involutive
  right_inv := flipProjective_involutive
  continuous_toFun := continuous_flipProjective
  continuous_invFun := continuous_flipProjective

theorem measurable_flipProjective : Measurable flipProjective :=
  continuous_flipProjective.measurable

theorem flip_transferProjective (E v : ℝ) (p : ProjectivePoint) :
    flipProjective (transferProjective E v p) =
      transferInverseProjective E v (flipProjective p) := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [transferProjective_mk, flipProjective_mk, flipProjective_mk,
      transferInverseProjective_mk]
    congr 1
    exact flipVector_transfer E v u

theorem flip_transferInverseProjective (E v : ℝ) (p : ProjectivePoint) :
    flipProjective (transferInverseProjective E v p) =
      transferProjective E v (flipProjective p) := by
  have h := congrArg flipProjective (flip_transferProjective E v (flipProjective p))
  simpa only [flipProjective_involutive] using h.symm

theorem projectiveGrowth_inverse_flip (E v : ℝ) (p : ProjectivePoint) :
    projectiveGrowth (transferInv E v) (flipProjective p) =
      projectiveGrowth (transfer E v) p := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [flipProjective_mk, projectiveGrowth_mk, projectiveGrowth_mk]
    unfold vectorGrowth
    rw [← flipVector_transfer, euclideanNorm_flipVector, euclideanNorm_flipVector]

theorem inverseTransferLogCocycle_flip (E v : ℝ) (p : ProjectivePoint) :
    inverseTransferLogCocycle E v (flipProjective p) = transferLogCocycle E v p := by
  unfold inverseTransferLogCocycle transferLogCocycle projectiveLogGrowth
  rw [projectiveGrowth_inverse_flip]

def flipDistribution (ν : ProbabilityMeasure ProjectivePoint) :
    ProbabilityMeasure ProjectivePoint := ν.map measurable_flipProjective.aemeasurable

@[simp] theorem flipDistribution_involutive (ν : ProbabilityMeasure ProjectivePoint) :
    flipDistribution (flipDistribution ν) = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((ν : Measure ProjectivePoint).map flipProjective).map flipProjective = _
  rw [Measure.map_map measurable_flipProjective measurable_flipProjective]
  simp only [Function.comp_def, flipProjective_involutive, Measure.map_id']

theorem inputDistribution_flip (law : PotentialLaw) (ν : ProbabilityMeasure ProjectivePoint) :
    (inputDistribution law (flipDistribution ν) : Measure (ℝ × ProjectivePoint)) =
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)).map
        (Prod.map id flipProjective) := by
  change law.measure.prod ((ν : Measure ProjectivePoint).map flipProjective) =
    (law.measure.prod (ν : Measure ProjectivePoint)).map (Prod.map id flipProjective)
  simpa only [Measure.map_id] using Measure.map_prod_map law.measure
    (ν : Measure ProjectivePoint) measurable_id measurable_flipProjective

theorem inverseDistribution_flip (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    inverseDistribution law E (flipDistribution ν) =
      flipDistribution (forwardDistribution law E ν) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (inputDistribution law (flipDistribution ν) : Measure (ℝ × ProjectivePoint)).map
    (inverseStep E) =
      ((inputDistribution law ν : Measure (ℝ × ProjectivePoint)).map (forwardStep E)).map
        flipProjective
  rw [inputDistribution_flip,
    Measure.map_map (measurable_inverseStep E) (measurable_id.prodMap measurable_flipProjective),
    Measure.map_map measurable_flipProjective (measurable_forwardStep E)]
  congr 1
  funext z
  exact (flip_transferProjective E z.1 z.2).symm

theorem forwardDistribution_flip (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    forwardDistribution law E (flipDistribution ν) =
      flipDistribution (inverseDistribution law E ν) := by
  have h := congrArg flipDistribution (inverseDistribution_flip law E (flipDistribution ν))
  simpa only [flipDistribution_involutive] using h.symm

theorem inverseStationary_flip (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν) :
    InverseStationary law E (flipDistribution ν) := by
  change inverseDistribution law E (flipDistribution ν) = flipDistribution ν
  rw [inverseDistribution_flip, hν]

theorem forwardStationary_flip (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : InverseStationary law E ν) :
    ForwardStationary law E (flipDistribution ν) := by
  change forwardDistribution law E (flipDistribution ν) = flipDistribution ν
  rw [forwardDistribution_flip, hν]

theorem inverseStationaryMean_flip (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    inverseStationaryMean law E (flipDistribution ν) = stationaryMean law E ν := by
  unfold inverseStationaryMean
  rw [inputDistribution_flip]
  calc
    _ = ∫ z : ℝ × ProjectivePoint,
        inverseTransferLogCocycle E z.1 (flipProjective z.2)
          ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
      exact integral_map (measurable_id.prodMap measurable_flipProjective).aemeasurable
        (continuous_inverseTransferLogCocycle E).measurable.aestronglyMeasurable
    _ = stationaryMean law E ν := by
      unfold stationaryMean
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => inverseTransferLogCocycle_flip E z.1 z.2

theorem flipDistribution_null_singletons (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) :
    ∀ p, (flipDistribution ν : Measure ProjectivePoint) {p} = 0 := by
  intro p
  change (ν : Measure ProjectivePoint).map flipProjective {p} = 0
  rw [Measure.map_apply measurable_flipProjective (measurableSet_singleton p)]
  have hpre : flipProjective ⁻¹' {p} = {flipProjective p} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hh := congrArg flipProjective h
      simpa only [flipProjective_involutive] using hh
    · intro h
      rw [h, flipProjective_involutive]
  rw [hpre]
  exact hν _

theorem inverseStationary_unique_of_forward (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint)
    (hunique : ∀ σ, ForwardStationary law E σ → σ = ν) :
    ∀ σ, InverseStationary law E σ → σ = flipDistribution ν := by
  intro σ hσ
  have h := congrArg flipDistribution (hunique (flipDistribution σ)
    (forwardStationary_flip law E σ hσ))
  simpa only [flipDistribution_involutive] using h

end FixedCouplingPoisson.Furstenberg
