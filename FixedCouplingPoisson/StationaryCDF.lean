import FixedCouplingPoisson.AngleProjective
import FixedCouplingPoisson.Phase
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.LeftRightLim

/-!
Work draft: construct the actual CDF lift of an atomless projective probability.
This does not yet assert stationarity, a harmonic identity, or IDS drift.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Real Set
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The unique representative in [0,π) of the actual projective angle. -/
def projectiveCoordinate (p : ProjectivePoint) : ℝ :=
  AddCircle.equivIco Real.pi 0 (angleProjectiveHomeomorph.symm p)

theorem measurable_projectiveCoordinate : Measurable projectiveCoordinate :=
  measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (T := Real.pi) 0).measurable.comp
      angleProjectiveHomeomorph.symm.measurable)

theorem projectiveCoordinate_injective : Function.Injective projectiveCoordinate :=
  Subtype.val_injective.comp
    ((AddCircle.equivIco Real.pi 0).injective.comp angleProjectiveHomeomorph.symm.injective)

theorem projectiveCoordinate_mem (p : ProjectivePoint) :
    projectiveCoordinate p ∈ Ico 0 Real.pi := by
  simpa only [projectiveCoordinate, zero_add] using
    (AddCircle.equivIco Real.pi 0 (angleProjectiveHomeomorph.symm p)).2

theorem phaseProjective_projectiveCoordinate (p : ProjectivePoint) :
    phaseProjective (projectiveCoordinate p) = p := by
  rw [← angleProjectiveHomeomorph_coe]
  have hcoe : ((projectiveCoordinate p : ℝ) : AddCircle Real.pi) =
      angleProjectiveHomeomorph.symm p := AddCircle.coe_equivIco
  rw [hcoe]
  exact angleProjectiveHomeomorph.apply_symm_apply p

def coordinateDistribution (ν : ProbabilityMeasure ProjectivePoint) : ProbabilityMeasure ℝ :=
  ν.map measurable_projectiveCoordinate.aemeasurable

theorem coordinateDistribution_null_singletons
    (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) (x : ℝ) :
    (coordinateDistribution ν : Measure ℝ) {x} = 0 := by
  rw [coordinateDistribution, ProbabilityMeasure.map_apply' _ _ (measurableSet_singleton x)]
  by_cases hx : ∃ p, projectiveCoordinate p = x
  · obtain ⟨p, hp⟩ := hx
    have heq : projectiveCoordinate ⁻¹' {x} = {p} := by
      ext q
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun hq => projectiveCoordinate_injective (hq.trans hp.symm),
        fun hq => hq ▸ hp⟩
    rw [heq]
    exact hν p
  · have heq : projectiveCoordinate ⁻¹' {x} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hx ⟨p, hp⟩
    rw [heq, measure_empty]

/-- Vanishing actual atoms removes the jump of the ordinary real CDF. -/
theorem continuous_cdf_of_null_singletons (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x, μ {x} = 0) : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  have hzero : ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, hμ]
  have hle := ENNReal.ofReal_eq_zero.mp hzero
  have hge := (monotone_cdf μ).leftLim_le (le_refl x)
  linarith

def projectiveCDF (ν : ProbabilityMeasure ProjectivePoint) : ℝ → ℝ :=
  cdf (coordinateDistribution ν : Measure ℝ)

theorem continuous_projectiveCDF (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) : Continuous (projectiveCDF ν) :=
  continuous_cdf_of_null_singletons _ (coordinateDistribution_null_singletons ν hν)

theorem projectiveCDF_nonneg (ν : ProbabilityMeasure ProjectivePoint) (x : ℝ) :
    0 ≤ projectiveCDF ν x := cdf_nonneg _ x

theorem projectiveCDF_le_one (ν : ProbabilityMeasure ProjectivePoint) (x : ℝ) :
    projectiveCDF ν x ≤ 1 := cdf_le_one _ x

theorem projectiveCDF_monotone (ν : ProbabilityMeasure ProjectivePoint) :
    Monotone (projectiveCDF ν) := monotone_cdf _

theorem projectiveCDF_zero (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) : projectiveCDF ν 0 = 0 := by
  have heq : projectiveCoordinate ⁻¹' Iic 0 = projectiveCoordinate ⁻¹' {0} := by
    ext p
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    exact ⟨fun hp => le_antisymm hp (projectiveCoordinate_mem p).1,
      fun hp => hp.le⟩
  have hmass : (coordinateDistribution ν : Measure ℝ) (Iic 0) = 0 := by
    rw [coordinateDistribution, ProbabilityMeasure.map_apply' _ _ measurableSet_Iic, heq]
    have hzero := coordinateDistribution_null_singletons ν hν 0
    rw [coordinateDistribution, ProbabilityMeasure.map_apply' _ _ (measurableSet_singleton 0)] at hzero
    exact hzero
  rw [projectiveCDF, cdf_eq_real, Measure.real, hmass, ENNReal.toReal_zero]

theorem projectiveCDF_pi (ν : ProbabilityMeasure ProjectivePoint) :
    projectiveCDF ν Real.pi = 1 := by
  have heq : projectiveCoordinate ⁻¹' Iic Real.pi = univ := by
    exact eq_univ_iff_forall.mpr fun p => (projectiveCoordinate_mem p).2.le
  have hmass : (coordinateDistribution ν : Measure ℝ) (Iic Real.pi) = 1 := by
    rw [coordinateDistribution, ProbabilityMeasure.map_apply' _ _ measurableSet_Iic,
      heq, measure_univ]
  rw [projectiveCDF, cdf_eq_real, Measure.real, hmass, ENNReal.toReal_one]

def cdfDisplacement (ν : ProbabilityMeasure ProjectivePoint) : AddCircle Real.pi → ℝ :=
  AddCircle.liftIco Real.pi 0 (fun θ => Real.pi * projectiveCDF ν θ - θ)

/-- A concrete global degree-one lift, constructed from the actual probability. -/
def stationaryCDFLift (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) : ℝ :=
  θ + cdfDisplacement ν (θ : AddCircle Real.pi)

theorem continuous_cdfDisplacement (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) : Continuous (cdfDisplacement ν) := by
  apply AddCircle.liftIco_zero_continuous
  · rw [projectiveCDF_zero ν hν, projectiveCDF_pi]
    ring
  · exact ((continuous_const.mul (continuous_projectiveCDF ν hν)).sub continuous_id).continuousOn

theorem continuous_stationaryCDFLift (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) : Continuous (stationaryCDFLift ν) :=
  continuous_id.add ((continuous_cdfDisplacement ν hν).comp (AddCircle.continuous_mk' Real.pi))

theorem stationaryCDFLift_fundamental (ν : ProbabilityMeasure ProjectivePoint) {θ : ℝ}
    (hθ : θ ∈ Ico 0 Real.pi) : stationaryCDFLift ν θ = Real.pi * projectiveCDF ν θ := by
  unfold stationaryCDFLift cdfDisplacement
  rw [AddCircle.liftIco_coe_apply (by simpa only [zero_add] using hθ)]
  ring

theorem stationaryCDFLift_add_int (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) (k : ℤ) :
    stationaryCDFLift ν (θ + k * Real.pi) = stationaryCDFLift ν θ + k * Real.pi := by
  have hcoe : ((θ + k * Real.pi : ℝ) : AddCircle Real.pi) = (θ : AddCircle Real.pi) := by
    rw [AddCircle.coe_add]
    have hzero : ((k * Real.pi : ℝ) : AddCircle Real.pi) = 0 :=
      (AddCircle.coe_eq_zero_iff Real.pi).mpr ⟨k, by simp [zsmul_eq_mul]⟩
    rw [hzero, add_zero]
  simp only [stationaryCDFLift, hcoe]
  ring

def cdfCell (θ : ℝ) : ℤ := Int.floor (θ / Real.pi)
def cdfReduced (θ : ℝ) : ℝ := θ - cdfCell θ * Real.pi

theorem cdfReduced_mem (θ : ℝ) : cdfReduced θ ∈ Ico 0 Real.pi := by
  exact ⟨Int.sub_floor_div_mul_nonneg θ Real.pi_pos,
    Int.sub_floor_div_mul_lt θ Real.pi_pos⟩

theorem stationaryCDFLift_cell (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) :
    stationaryCDFLift ν θ = Real.pi * projectiveCDF ν (cdfReduced θ) + cdfCell θ * Real.pi := by
  have h := stationaryCDFLift_add_int ν (cdfReduced θ) (cdfCell θ)
  have heq : cdfReduced θ + (cdfCell θ : ℝ) * Real.pi = θ := by
    unfold cdfReduced
    ring
  rw [heq, stationaryCDFLift_fundamental ν (cdfReduced_mem θ)] at h
  exact h

theorem stationaryCDFLift_monotone (ν : ProbabilityMeasure ProjectivePoint) :
    Monotone (stationaryCDFLift ν) := by
  intro θ φ hle
  have hk : cdfCell θ ≤ cdfCell φ :=
    Int.floor_mono (div_le_div_of_nonneg_right hle Real.pi_pos.le)
  rw [stationaryCDFLift_cell, stationaryCDFLift_cell]
  by_cases heq : cdfCell θ = cdfCell φ
  · have hr : cdfReduced θ ≤ cdfReduced φ := by
      unfold cdfReduced
      rw [heq]
      linarith
    have hh := mul_le_mul_of_nonneg_left (projectiveCDF_monotone ν hr) Real.pi_pos.le
    rw [heq]
    linarith
  · have hklt : cdfCell θ < cdfCell φ := lt_of_le_of_ne hk heq
    have hstep' : (((cdfCell θ + 1 : ℤ) : ℝ)) ≤ (cdfCell φ : ℝ) :=
      Int.cast_le.mpr (Int.add_one_le_iff.mpr hklt)
    have hstep : (cdfCell θ : ℝ) + 1 ≤ (cdfCell φ : ℝ) := by simpa using hstep'
    have hm := mul_le_mul_of_nonneg_right hstep Real.pi_pos.le
    have hθ := mul_le_mul_of_nonneg_left (projectiveCDF_le_one ν (cdfReduced θ)) Real.pi_pos.le
    have hφ := mul_nonneg Real.pi_pos.le (projectiveCDF_nonneg ν (cdfReduced φ))
    linarith

theorem stationaryCDFLift_close_identity (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) :
    |stationaryCDFLift ν θ - θ| ≤ Real.pi := by
  rw [stationaryCDFLift_cell]
  have hr := cdfReduced_mem θ
  have hlo := mul_nonneg Real.pi_pos.le (projectiveCDF_nonneg ν (cdfReduced θ))
  have hhi := mul_le_mul_of_nonneg_left
    (projectiveCDF_le_one ν (cdfReduced θ)) Real.pi_pos.le
  unfold cdfReduced at hr
  apply abs_le.mpr
  constructor <;> nlinarith [hr.1, hr.2]

def inverseStationaryCDF (law : PotentialLaw) (E : ℝ) (data : QualitativeData law E) : CDFLift where
  toFun := stationaryCDFLift data.inverseMeasure
  monotone := stationaryCDFLift_monotone data.inverseMeasure
  equivariant := stationaryCDFLift_add_int data.inverseMeasure
  normalized := by
    rw [stationaryCDFLift_fundamental data.inverseMeasure ⟨le_refl _, Real.pi_pos⟩,
      projectiveCDF_zero _ data.inverse_null_singletons, mul_zero]

end FixedCouplingPoisson.Furstenberg
