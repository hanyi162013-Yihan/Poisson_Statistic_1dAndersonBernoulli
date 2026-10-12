import FixedCouplingPoisson.ProjectiveSL2Growth
import FixedCouplingPoisson.ProjectiveAtomlessUniform
import Mathlib.Topology.Order.Compact

/-! Properness of the actual averaged log norm for an atomless projective
probability. All estimates use the explicit Euclidean norm. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Set
open scoped Topology

theorem projectiveLogGrowth_sl2_lower (A : RealSL2) (p : ProjectivePoint) :
    -Real.log 2 - Real.log (sl2RowRadius A) ≤ projectiveLogGrowth A p := by
  have h := Real.log_le_log (inv_pos.mpr
    (mul_pos (by norm_num) (sl2RowRadius_pos A)))
    (inv_sl2RowRadius_le_projectiveGrowth A p)
  rw [Real.log_inv, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (sl2RowRadius_pos A).ne'] at h
  simpa only [projectiveLogGrowth, sub_eq_add_neg, neg_add_rev, add_comm] using h

/-- The exceptional directions have mass at most one quarter. The matrix
dependent singular direction therefore cannot cancel the expanding row. -/
theorem stationarySL2Mean_lower_of_uniform_radius
    (ν : ProbabilityMeasure ProjectivePoint) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : ∀ β : ProjectivePoint,
      (ν : Measure ProjectivePoint).real {p | projectiveDistance p β ≤ δ} ≤ 1 / 4)
    (A : RealSL2) :
    Real.log (sl2RowRadius A) / 2 + Real.log δ - Real.log 2 ≤ stationarySL2Mean ν A := by
  obtain ⟨β, hβ⟩ := exists_sl2RowKernel_growth_lower A
  let B : Set ProjectivePoint := {p | projectiveDistance p β ≤ δ}
  let L := Real.log (sl2RowRadius A)
  let D := Real.log δ
  let C := Real.log 2
  have hL : 0 ≤ L := Real.log_nonneg (one_le_sl2RowRadius A)
  have hD : D ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hC : 0 ≤ C := Real.log_nonneg (by norm_num)
  have hdist : Continuous (fun p : ProjectivePoint => projectiveDistance p β) := by
    have hpair : Continuous (fun p : ProjectivePoint => (p, β)) :=
      continuous_id.prodMk continuous_const
    exact continuous_projectiveDistance_joint.comp hpair
  have hB : MeasurableSet B := (isClosed_le hdist continuous_const).measurableSet
  have hi : Integrable (fun p => L + D - B.indicator (fun _ => 2 * L + C) p)
      (ν : Measure ProjectivePoint) :=
    (integrable_const _).sub ((integrable_const _).indicator hB)
  have hg : Integrable (fun p => projectiveLogGrowth A p) (ν : Measure ProjectivePoint) :=
    integrable_continuous_test (sl2LogContinuousMap A) ν
  have hpoint (p : ProjectivePoint) :
      L + D - B.indicator (fun _ => 2 * L + C) p ≤ projectiveLogGrowth A p := by
    by_cases hp : p ∈ B
    · rw [indicator_of_mem hp]
      have hbase := projectiveLogGrowth_sl2_lower A p
      dsimp only [L, C, D] at *
      linarith
    · rw [indicator_of_notMem hp, sub_zero]
      have hd : δ ≤ projectiveDistance p β := (lt_of_not_ge hp).le
      have hnorm : sl2RowRadius A * δ ≤ projectiveGrowth (A : Matrix2) p :=
        (mul_le_mul_of_nonneg_left hd (sl2RowRadius_nonneg A)).trans (hβ p)
      have hlog := Real.log_le_log (mul_pos (sl2RowRadius_pos A) hδ) hnorm
      rw [Real.log_mul (sl2RowRadius_pos A).ne' hδ.ne'] at hlog
      exact hlog
  have hint := integral_mono hi hg hpoint
  have heval : (∫ p, L + D - B.indicator (fun _ => 2 * L + C) p
      ∂(ν : Measure ProjectivePoint)) =
      L + D - (ν : Measure ProjectivePoint).real B * (2 * L + C) := by
    rw [integral_sub (integrable_const _) ((integrable_const _).indicator hB),
      integral_const, integral_indicator_const _ hB]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [heval] at hint
  have hb := hsmall β
  change (ν : Measure ProjectivePoint).real B ≤ 1 / 4 at hb
  have hb1 : (ν : Measure ProjectivePoint).real B ≤ 1 := hb.trans (by norm_num)
  have hbL := mul_le_mul_of_nonneg_right hb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
  have hbC := mul_le_mul_of_nonneg_right hb1 hC
  change L / 2 + D - C ≤ stationarySL2Mean ν A
  change L + D - (ν : Measure ProjectivePoint).real B * (2 * L + C) ≤
    stationarySL2Mean ν A at hint
  nlinarith

theorem exists_stationarySL2Mean_proper_bound (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ β, (ν : Measure ProjectivePoint) {β} = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : RealSL2,
      Real.log (sl2RowRadius A) / 2 + Real.log δ - Real.log 2 ≤ stationarySL2Mean ν A := by
  obtain ⟨r, hr, hsmall⟩ := exists_uniform_projective_atomless_radius ν hν (1 / 4) (by norm_num)
  let δ := min r 1
  have hδ : 0 < δ := lt_min hr zero_lt_one
  refine ⟨δ, hδ, min_le_right _ _, fun A =>
    stationarySL2Mean_lower_of_uniform_radius ν δ hδ (min_le_right _ _) ?_ A⟩
  intro β
  have hsub : {p : ProjectivePoint | projectiveDistance p β ≤ δ} ⊆
      {p : ProjectivePoint | projectiveDistance p β ≤ r} := by
    intro p hp
    change projectiveDistance p β ≤ δ at hp
    change projectiveDistance p β ≤ r
    exact hp.trans (min_le_left _ _)
  have hbound : (ν : Measure ProjectivePoint) {p | projectiveDistance p β ≤ δ} ≤
      ENNReal.ofReal (1 / 4) :=
    (measure_mono hsub).trans (hsmall β).le
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by norm_num))

theorem isCompact_sl2_coordinate_box (R : ℝ) :
    IsCompact {A : RealSL2 | ∀ i j, A i j ∈ Icc (-R) R} := by
  have hbox : IsCompact {A : Matrix2 | ∀ i j, A i j ∈ Icc (-R) R} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
  exact SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hbox

/-- Every sublevel is genuinely compact in the actual SL₂ topology. -/
theorem isCompact_stationarySL2Mean_sublevel (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ β, (ν : Measure ProjectivePoint) {β} = 0) (c : ℝ) :
    IsCompact {A : RealSL2 | stationarySL2Mean ν A ≤ c} := by
  obtain ⟨δ, hδ, hδ1, hbound⟩ := exists_stationarySL2Mean_proper_bound ν hν
  let R := Real.exp (2 * (c - Real.log δ + Real.log 2))
  apply (isCompact_sl2_coordinate_box R).of_isClosed_subset
    (isClosed_le (continuous_stationarySL2Mean ν) continuous_const)
  intro A hA i j
  change stationarySL2Mean ν A ≤ c at hA
  have hlog : Real.log (sl2RowRadius A) ≤ 2 * (c - Real.log δ + Real.log 2) := by
    linarith [hbound A]
  have hr : sl2RowRadius A ≤ R := (Real.log_le_iff_le_exp (sl2RowRadius_pos A)).mp hlog
  exact (abs_le.mp ((sl2_entry_abs_le_radius A i j).trans hr))

theorem exists_stationarySL2Mean_minimizer (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ β, (ν : Measure ProjectivePoint) {β} = 0) :
    ∃ A : RealSL2, ∀ B : RealSL2, stationarySL2Mean ν A ≤ stationarySL2Mean ν B := by
  let c := stationarySL2Mean ν 1
  have hne : {A : RealSL2 | stationarySL2Mean ν A ≤ c}.Nonempty := by
    refine ⟨1, ?_⟩
    change stationarySL2Mean ν 1 ≤ stationarySL2Mean ν 1
    exact le_rfl
  obtain ⟨A, hA, hmin⟩ := (isCompact_stationarySL2Mean_sublevel ν hν c).exists_isMinOn
    hne (continuous_stationarySL2Mean ν).continuousOn
  change stationarySL2Mean ν A ≤ c at hA
  refine ⟨A, fun B => ?_⟩
  by_cases hB : stationarySL2Mean ν B ≤ c
  · exact hmin (by change stationarySL2Mean ν B ≤ c; exact hB)
  · exact hA.trans (le_of_lt (lt_of_not_ge hB))

end FixedCouplingPoisson.Furstenberg
