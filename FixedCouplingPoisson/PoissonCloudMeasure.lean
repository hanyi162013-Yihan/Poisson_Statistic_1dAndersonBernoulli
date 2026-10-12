import FixedCouplingPoisson.PoissonUnitCell
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-! A concrete unit-intensity Poisson cloud candidate on the real line.
This file constructs the probability space and proves pathwise local finiteness.
Its PPP law identification is developed separately. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

abbrev PoissonCloud := ℤ → ℕ × (ℕ → I)

def poissonCloudLaw : ProbabilityMeasure PoissonCloud :=
  ⟨Measure.infinitePi (fun _ : ℤ =>
    (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I)))), inferInstance⟩

def poissonCellMeasure (z : ℤ) (p : ℕ × (ℕ → I)) : Measure ℝ :=
  ∑ j ∈ Finset.range p.1, Measure.dirac ((z : ℝ) + (p.2 j : ℝ))

def poissonCloudMeasure (ω : PoissonCloud) : Measure ℝ :=
  Measure.sum (fun z : ℤ => poissonCellMeasure z (ω z))

theorem poissonCellMeasure_isFiniteMeasure (z : ℤ) (p : ℕ × (ℕ → I)) :
    IsFiniteMeasure (poissonCellMeasure z p) := by
  unfold poissonCellMeasure
  infer_instance

theorem poissonCellMeasure_Ioo_eq_zero_of_not_mem (ω : PoissonCloud) (x : ℝ)
    (z : ℤ) (hz : z ∉ Finset.Icc ⌊x - 2⌋ ⌈x + 1⌉) :
    poissonCellMeasure z (ω z) (Ioo (x - 1) (x + 1)) = 0 := by
  classical
  rw [poissonCellMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hn : (z : ℝ) + ((ω z).2 j : ℝ) ∉ Ioo (x - 1) (x + 1) := by
    intro ha
    apply hz
    apply Finset.mem_Icc.mpr
    constructor
    · have h0 := ((ω z).2 j).property.2
      have hfl := Int.floor_le (x - 2)
      have hr : (⌊x - 2⌋ : ℝ) ≤ (z : ℝ) := by linarith [ha.1]
      exact_mod_cast hr
    · have h0 := ((ω z).2 j).property.1
      have hce := Int.le_ceil (x + 1)
      have hr : (z : ℝ) ≤ (⌈x + 1⌉ : ℝ) := by linarith [ha.2]
      exact_mod_cast hr
  simp [hn]

theorem poissonCloudMeasure_Ioo_lt_top (ω : PoissonCloud) (x : ℝ) :
    poissonCloudMeasure ω (Ioo (x - 1) (x + 1)) < ∞ := by
  classical
  unfold poissonCloudMeasure
  rw [Measure.sum_apply _ measurableSet_Ioo,
    tsum_eq_sum (s := Finset.Icc ⌊x - 2⌋ ⌈x + 1⌉)
      (fun z hz => poissonCellMeasure_Ioo_eq_zero_of_not_mem ω x z hz)]
  apply ENNReal.sum_lt_top.mpr
  intro z hz
  letI := poissonCellMeasure_isFiniteMeasure z (ω z)
  exact measure_lt_top _ _

theorem poissonCloudMeasure_isLocallyFiniteMeasure (ω : PoissonCloud) :
    IsLocallyFiniteMeasure (poissonCloudMeasure ω) := by
  constructor
  intro x
  exact ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    poissonCloudMeasure_Ioo_lt_top ω x⟩

theorem poissonCloudMeasure_regular (ω : PoissonCloud) :
    (poissonCloudMeasure ω).Regular := by
  haveI := poissonCloudMeasure_isLocallyFiniteMeasure ω
  infer_instance

end FixedCouplingPoisson
