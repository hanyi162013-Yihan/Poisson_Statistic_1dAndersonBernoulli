import FixedCouplingPoisson.StationaryCDF
import FixedCouplingPoisson.LiftWinding
import Mathlib.MeasureTheory.Function.Floor

/-!
Work draft: an integral formula for the actual global CDF lift. The integer
index records every passage through the angular cut, including wrapped arcs.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Real Set
open scoped Topology

def indexObservable (θ : ℝ) (p : ProjectivePoint) : ℝ :=
  angularIndex θ (projectiveCoordinate p)

theorem measurable_indexObservable (θ : ℝ) : Measurable (indexObservable θ) :=
  (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (Int.measurable_floor.comp ((measurable_const.sub measurable_projectiveCoordinate).div_const Real.pi))

theorem norm_indexObservable_le (θ : ℝ) (p : ProjectivePoint) :
    ‖indexObservable θ p‖ ≤ |(Int.floor (θ / Real.pi) : ℝ)| + 1 := by
  have hb := angularIndex_bounds θ (projectiveCoordinate p) (projectiveCoordinate_mem p)
  have hlo : (Int.floor (θ / Real.pi) : ℝ) - 1 ≤ indexObservable θ p := by
    have h : ((Int.floor (θ / Real.pi) - 1 : ℤ) : ℝ) ≤
        (angularIndex θ (projectiveCoordinate p) : ℝ) := Int.cast_le.mpr hb.1
    simpa only [Int.cast_sub, Int.cast_one, indexObservable] using h
  have hhi : indexObservable θ p ≤ (Int.floor (θ / Real.pi) : ℝ) := by
    exact Int.cast_le.mpr hb.2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hl := neg_abs_le (Int.floor (θ / Real.pi) : ℝ)
  have hu := le_abs_self (Int.floor (θ / Real.pi) : ℝ)
  constructor <;> linarith

theorem integrable_indexObservable (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) :
    Integrable (indexObservable θ) (ν : Measure ProjectivePoint) :=
  (integrable_const (|(Int.floor (θ / Real.pi) : ℝ)| + 1)).mono'
    (measurable_indexObservable θ).aestronglyMeasurable
    (ae_of_all _ (norm_indexObservable_le θ))

theorem indexObservable_fundamental {θ : ℝ} (hθ : θ ∈ Ico 0 Real.pi) :
    indexObservable θ =
      (fun p => {q : ProjectivePoint | projectiveCoordinate q ≤ θ}.indicator (fun _ => (1 : ℝ)) p - 1) := by
  funext p
  by_cases hp : projectiveCoordinate p ≤ θ
  · have hz := angularIndex_fundamental_of_le hθ (projectiveCoordinate_mem p) hp
    have hp' : p ∈ {q : ProjectivePoint | projectiveCoordinate q ≤ θ} := hp
    simp only [indexObservable, hz, Int.cast_zero,
      Set.indicator_of_mem hp', sub_self]
  · have hz := angularIndex_fundamental_of_gt hθ (projectiveCoordinate_mem p) (lt_of_not_ge hp)
    have hp' : p ∉ {q : ProjectivePoint | projectiveCoordinate q ≤ θ} := hp
    simp only [indexObservable, hz, Int.cast_neg, Int.cast_one,
      Set.indicator_of_notMem hp', zero_sub]

theorem projectiveCDF_eq_measureReal (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) :
    projectiveCDF ν θ =
      (ν : Measure ProjectivePoint).real {p | projectiveCoordinate p ≤ θ} := by
  rw [projectiveCDF, cdf_eq_real, Measure.real, coordinateDistribution,
    ProbabilityMeasure.map_apply' _ _ measurableSet_Iic]
  rfl

theorem integral_indexObservable_fundamental (ν : ProbabilityMeasure ProjectivePoint)
    {θ : ℝ} (hθ : θ ∈ Ico 0 Real.pi) :
    (∫ p, indexObservable θ p ∂(ν : Measure ProjectivePoint)) = projectiveCDF ν θ - 1 := by
  have hs : MeasurableSet {p : ProjectivePoint | projectiveCoordinate p ≤ θ} :=
    measurable_projectiveCoordinate measurableSet_Iic
  rw [indexObservable_fundamental hθ,
    integral_sub ((integrable_const (1 : ℝ)).indicator hs) (integrable_const (1 : ℝ)),
    integral_indicator_const _ hs, ← projectiveCDF_eq_measureReal]
  simp

theorem indexObservable_add_int (θ : ℝ) (k : ℤ) :
    indexObservable (θ + k * Real.pi) = fun p => indexObservable θ p + (k : ℝ) := by
  funext p
  simp only [indexObservable, angularIndex_add_int, Int.cast_add]

/-- A global formula, with the same integer correction on both sides. -/
theorem stationaryCDFLift_integral_index (ν : ProbabilityMeasure ProjectivePoint) (θ : ℝ) :
    stationaryCDFLift ν θ =
      Real.pi * ((∫ p, indexObservable θ p ∂(ν : Measure ProjectivePoint)) + 1) := by
  let r := cdfReduced θ
  let k := cdfCell θ
  have heq : r + (k : ℝ) * Real.pi = θ := by
    dsimp [r, k, cdfReduced]
    ring
  have hr : r ∈ Ico 0 Real.pi := cdfReduced_mem θ
  have hobs : indexObservable θ = fun p => indexObservable r p + (k : ℝ) := by
    rw [← heq, indexObservable_add_int]
  have hint : (∫ p, indexObservable θ p ∂(ν : Measure ProjectivePoint)) =
      projectiveCDF ν r - 1 + (k : ℝ) := by
    rw [hobs, integral_add (integrable_indexObservable ν r) (integrable_const _),
      integral_indexObservable_fundamental ν hr]
    simp
  rw [hint, stationaryCDFLift_cell]
  change Real.pi * projectiveCDF ν r + (k : ℝ) * Real.pi = _
  ring

theorem stationaryCDFLift_difference_integral_index (ν : ProbabilityMeasure ProjectivePoint)
    (θ φ : ℝ) :
    stationaryCDFLift ν θ - stationaryCDFLift ν φ =
      Real.pi * (∫ p, indexObservable θ p - indexObservable φ p ∂(ν : Measure ProjectivePoint)) := by
  rw [stationaryCDFLift_integral_index, stationaryCDFLift_integral_index,
    integral_sub (integrable_indexObservable ν θ) (integrable_indexObservable ν φ)]
  ring

end FixedCouplingPoisson.Furstenberg
