import FixedCouplingPoisson.PoissonCloudMeasure

/-! At every deterministic point, the actual uniform-mark cloud has zero mass
almost surely. This supplies boundary-nullness for bounded interval counts. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal unitInterval Topology

theorem measurePreserving_poissonCloud_mark (z : ℤ) (j : ℕ) :
    MeasurePreserving (fun ω : PoissonCloud => (ω z).2 j)
      (poissonCloudLaw : Measure PoissonCloud) (volume : Measure I) := by
  have hcell : MeasurePreserving (fun ω : PoissonCloud => ω z)
      (poissonCloudLaw : Measure PoissonCloud)
      (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))) :=
    measurePreserving_eval_infinitePi _ z
  have hmarks : MeasurePreserving (fun p : ℕ × (ℕ → I) => p.2)
      (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I)))
      (uniformMarksLaw : Measure (ℕ → I)) := measurePreserving_snd
  have hmark : MeasurePreserving (fun u : ℕ → I => u j)
      (uniformMarksLaw : Measure (ℕ → I)) (volume : Measure I) :=
    measurePreserving_eval_infinitePi _ j
  exact hmark.comp (hmarks.comp hcell)

theorem poissonCloud_mark_ae_ne (z : ℤ) (j : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂(poissonCloudLaw : Measure PoissonCloud),
      (z : ℝ) + ((ω z).2 j : ℝ) ≠ x := by
  have h := unitInterval.measurePreserving_coe.comp (measurePreserving_poissonCloud_mark z j)
  have he : ∀ᵐ u : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), u ≠ x - (z : ℝ) :=
    Measure.ae_ne _ _
  filter_upwards [h.quasiMeasurePreserving.tendsto_ae he] with ω hω
  dsimp only [Function.comp_def] at hω
  intro hEq
  apply hω
  linarith

theorem poissonCloudMeasure_ae_singleton (x : ℝ) :
    ∀ᵐ ω ∂(poissonCloudLaw : Measure PoissonCloud), poissonCloudMeasure ω {x} = 0 := by
  have hall : ∀ᵐ ω ∂(poissonCloudLaw : Measure PoissonCloud),
      ∀ z : ℤ, ∀ j : ℕ, (z : ℝ) + ((ω z).2 j : ℝ) ≠ x := by
    rw [ae_all_iff]
    intro z
    rw [ae_all_iff]
    exact fun j => poissonCloud_mark_ae_ne z j x
  filter_upwards [hall] with ω hω
  rw [poissonCloudMeasure, Measure.sum_apply _ (measurableSet_singleton x)]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  rw [poissonCellMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp [Measure.dirac_apply, hω z j]

end FixedCouplingPoisson
