import FixedCouplingPoisson.StationaryCDF
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Metrizable.Urysohn

/-! The angular cut contributes one exceptional
projective point. Every CDF set has frontier contained in that point and
one coordinate fiber; actual nonatomicity removes both boundaries. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem continuousAt_projectiveCoordinate {p : ProjectivePoint}
    (hp : p ≠ phaseProjective 0) : ContinuousAt projectiveCoordinate p := by
  change ContinuousAt (fun q : ProjectivePoint =>
    (AddCircle.equivIco Real.pi 0 (angleProjectiveHomeomorph.symm q) : ℝ)) p
  have hx : angleProjectiveHomeomorph.symm p ≠ (0 : AddCircle Real.pi) := by
    intro hx
    apply hp
    have h := congrArg angleProjectiveHomeomorph hx
    simpa only [angleProjectiveHomeomorph.apply_symm_apply,
      ← AddCircle.coe_zero, angleProjectiveHomeomorph_coe] using h
  have hcoord := (AddCircle.continuousAt_equivIco Real.pi 0 hx).comp
    angleProjectiveHomeomorph.symm.continuous.continuousAt
  have hm := continuous_subtype_val.continuousAt.comp hcoord
  simpa only [Function.comp_def] using hm

theorem frontier_projectiveCDF_set_subset (θ : ℝ) :
    frontier {p : ProjectivePoint | projectiveCoordinate p ≤ θ} ⊆
      {phaseProjective 0} ∪ projectiveCoordinate ⁻¹' {θ} := by
  intro p hp
  by_contra hbad
  have hp0 : p ≠ phaseProjective 0 := fun h => hbad (Or.inl h)
  have hpθ : projectiveCoordinate p ≠ θ := fun h => hbad (Or.inr h)
  have hc := continuousAt_projectiveCoordinate hp0
  change p ∈ closure {q : ProjectivePoint | projectiveCoordinate q ≤ θ} ∧
    p ∉ interior {q : ProjectivePoint | projectiveCoordinate q ≤ θ} at hp
  rcases lt_or_gt_of_ne hpθ with hlt | hgt
  · have hn : {q : ProjectivePoint | projectiveCoordinate q ≤ θ} ∈ 𝓝 p :=
      Filter.mem_of_superset (hc.preimage_mem_nhds (Iio_mem_nhds hlt))
        (fun q hq => by
          change projectiveCoordinate q ≤ θ
          change projectiveCoordinate q < θ at hq
          exact hq.le)
    exact hp.2 (mem_interior_iff_mem_nhds.mpr hn)
  · have hn : {q : ProjectivePoint | projectiveCoordinate q ≤ θ}ᶜ ∈ 𝓝 p :=
      Filter.mem_of_superset (hc.preimage_mem_nhds (Ioi_mem_nhds hgt))
        (fun q hq => by
          change ¬ projectiveCoordinate q ≤ θ
          change θ < projectiveCoordinate q at hq
          exact not_le_of_gt hq)
    have hi := mem_interior_iff_mem_nhds.mpr hn
    rw [interior_compl] at hi
    exact hi hp.1

theorem null_frontier_projectiveCDF_set (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) (θ : ℝ) :
    (ν : Measure ProjectivePoint)
      (frontier {p : ProjectivePoint | projectiveCoordinate p ≤ θ}) = 0 := by
  have hfiber : (ν : Measure ProjectivePoint) (projectiveCoordinate ⁻¹' {θ}) = 0 := by
    have h := coordinateDistribution_null_singletons ν hν θ
    rw [coordinateDistribution, ProbabilityMeasure.map_apply' _ _
      (measurableSet_singleton θ)] at h
    exact h
  exact measure_mono_null (frontier_projectiveCDF_set_subset θ)
    (measure_union_null (hν _) hfiber)

theorem projectiveCDF_tendsto_of_weak {ι : Type*} {L : Filter ι}
    {νs : ι → ProbabilityMeasure ProjectivePoint} {ν : ProbabilityMeasure ProjectivePoint}
    (hweak : Tendsto νs L (𝓝 ν))
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) (θ : ℝ) :
    Tendsto (fun i => projectiveCDF (νs i) θ) L (𝓝 (projectiveCDF ν θ)) := by
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
    (null_frontier_projectiveCDF_set ν hν θ)
  have ht := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ProjectivePoint) _)).comp h
  have hformula : ∀ η : ProbabilityMeasure ProjectivePoint,
      projectiveCDF η θ =
        (η : Measure ProjectivePoint).real {p | projectiveCoordinate p ≤ θ} := by
    intro η
    rw [projectiveCDF, cdf_eq_real, Measure.real, coordinateDistribution,
      ProbabilityMeasure.map_apply' _ _ measurableSet_Iic]
    rfl
  simpa only [hformula, Measure.real, Function.comp_def] using ht

/-- Pointwise convergence of monotone functions to a continuous limit also
allows the evaluation point to move. No monotonicity in the index is used. -/
theorem monotone_tendsto_moving_argument {ι : Type*} {L : Filter ι}
    (fs : ι → ℝ → ℝ) (f : ℝ → ℝ) (xs : ι → ℝ) (x : ℝ)
    (hm : ∀ i, Monotone (fs i)) (hf : ContinuousAt f x)
    (hpoint : ∀ a, Tendsto (fun i => fs i a) L (𝓝 (f a)))
    (hx : Tendsto xs L (𝓝 x)) :
    Tendsto (fun i => fs i (xs i)) L (𝓝 (f x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hn : {y | a < f y} ∈ 𝓝 x := hf.preimage_mem_nhds (Ioi_mem_nhds ha)
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
    let y := (l + x) / 2
    have hyx : y < x := by dsimp [y]; linarith [hxu.1]
    have hay : a < f y := hsub (by dsimp [y]; constructor <;> linarith [hxu.1, hxu.2])
    filter_upwards [(tendsto_order.mp (hpoint y)).1 a hay,
      (tendsto_order.mp hx).1 y hyx] with i hi hxi
    exact hi.trans_le (hm i hxi.le)
  · intro b hb
    have hn : {y | f y < b} ∈ 𝓝 x := hf.preimage_mem_nhds (Iio_mem_nhds hb)
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
    let y := (x + u) / 2
    have hxy : x < y := by dsimp [y]; linarith [hxu.2]
    have hyb : f y < b := hsub (by dsimp [y]; constructor <;> linarith [hxu.1, hxu.2])
    filter_upwards [(tendsto_order.mp (hpoint y)).2 b hyb,
      (tendsto_order.mp hx).2 y hxy] with i hi hxi
    exact (hm i hxi.le).trans_lt hi

theorem continuous_projectiveCDF_family {S : Type*} [TopologicalSpace S]
    (ν : S → ProbabilityMeasure ProjectivePoint) (hweak : Continuous ν)
    (hν : ∀ s p, (ν s : Measure ProjectivePoint) {p} = 0) :
    Continuous (fun z : S × ℝ => projectiveCDF (ν z.1) z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hprob : Tendsto (fun z' : S × ℝ => ν z'.1) (𝓝 z) (𝓝 (ν z.1)) :=
    (hweak.comp continuous_fst).tendsto z
  exact monotone_tendsto_moving_argument
    (fun z' : S × ℝ => projectiveCDF (ν z'.1)) (projectiveCDF (ν z.1))
    Prod.snd z.2 (fun z' => projectiveCDF_monotone (ν z'.1))
    (continuous_projectiveCDF (ν z.1) (hν z.1)).continuousAt
    (fun a => projectiveCDF_tendsto_of_weak hprob (hν z.1) a)
    (continuous_snd.tendsto z)

end FixedCouplingPoisson.Furstenberg
