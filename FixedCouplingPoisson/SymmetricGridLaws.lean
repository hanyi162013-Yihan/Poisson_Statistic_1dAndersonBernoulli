import FixedCouplingPoisson.RealVagueLaplaceApprox
import FixedCouplingPoisson.RealVagueEvaluation
import FixedCouplingPoisson.PoissonVectorLaplaceWeak
import FixedCouplingPoisson.WeakSequenceTight
import FixedCouplingPoisson.RealVagueLaplace

/-! Actual symmetric interval projections and compact-test step laws. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter
open scoped Topology CompactlySupported BigOperators

def symmetricGridMassVector (R : ℝ) (m : ℕ) (μ : RealVagueMeasure) : Fin (2 * m) → ℝ :=
  fun i => (μ : Measure ℝ).real
    (Ioc (symmetricGrid R m i.val) (symmetricGrid R m (i.val + 1)))

theorem measurable_symmetricGridMassVector (R : ℝ) (m : ℕ) :
    Measurable (symmetricGridMassVector R m) :=
  measurable_pi_lambda _ fun _ => RealVagueMeasure.measurable_measureReal_Ioc _ _

def symmetricEnclosingMass (R : ℝ) (μ : RealVagueMeasure) : ℝ :=
  (μ : Measure ℝ).real (Ioc (-R) R)

theorem measurable_symmetricEnclosingMass (R : ℝ) :
    Measurable (symmetricEnclosingMass R) :=
  RealVagueMeasure.measurable_measureReal_Ioc _ _

theorem symmetricGridMassVector_one_sum {R : ℝ} (hR : 0 < R)
    (μ : RealVagueMeasure) :
    (∑ i : Fin (2 * 1), symmetricGridMassVector R 1 μ i) = symmetricEnclosingMass R μ := by
  have hd : Disjoint (Ioc (-R) 0) (Ioc 0 R) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    exact (not_lt_of_ge hy.2) hz.1
  have h := measureReal_union (μ := (μ : Measure ℝ)) hd measurableSet_Ioc
    (realVagueMeasure_Ioc_ne_top μ _ _) (realVagueMeasure_Ioc_ne_top μ _ _)
  rw [Ioc_union_Ioc_eq_Ioc (neg_nonpos.mpr hR.le) hR.le] at h
  rw [Fin.sum_univ_two]
  change (μ : Measure ℝ).real (Ioc (symmetricGrid R 1 0) (symmetricGrid R 1 1)) +
    (μ : Measure ℝ).real (Ioc (symmetricGrid R 1 1) (symmetricGrid R 1 2)) =
      (μ : Measure ℝ).real (Ioc (-R) R)
  have hend := symmetricGrid_endpoints R (m := 1) (by decide)
  rw [hend.1, hend.2.1, hend.2.2]
  exact h.symm

theorem map_symmetricGridMassVector_one_sum {R : ℝ} (hR : 0 < R)
    (ν : ProbabilityMeasure RealVagueMeasure) :
    (ν.map (measurable_symmetricGridMassVector R 1).aemeasurable).map
      (show Measurable (fun x : Fin (2 * 1) → ℝ => ∑ i, x i) from by fun_prop).aemeasurable =
      ν.map (measurable_symmetricEnclosingMass R).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((ν : Measure RealVagueMeasure).map (symmetricGridMassVector R 1)).map
    (fun x : Fin (2 * 1) → ℝ => ∑ i, x i) =
      (ν : Measure RealVagueMeasure).map (symmetricEnclosingMass R)
  rw [Measure.map_map (show Measurable (fun x : Fin (2 * 1) → ℝ => ∑ i, x i) from by fun_prop)
    (measurable_symmetricGridMassVector R 1)]
  congr 1
  funext μ
  exact symmetricGridMassVector_one_sum hR μ

theorem symmetricEnclosingMass_law_tendsto_of_grid_law_tendsto
    (νs : ℕ → ProbabilityMeasure RealVagueMeasure) (ν : ProbabilityMeasure RealVagueMeasure)
    {R : ℝ} (hR : 0 < R)
    (hgrid : Tendsto (fun n => (νs n).map (measurable_symmetricGridMassVector R 1).aemeasurable)
      atTop (𝓝 (ν.map (measurable_symmetricGridMassVector R 1).aemeasurable))) :
    Tendsto (fun n => (νs n).map (measurable_symmetricEnclosingMass R).aemeasurable)
      atTop (𝓝 (ν.map (measurable_symmetricEnclosingMass R).aemeasurable)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hgrid
    (show Continuous (fun x : Fin (2 * 1) → ℝ => ∑ i, x i) from by fun_prop)
  simpa only [map_symmetricGridMassVector_one_sum hR] using h

def symmetricStepLaplace (f : C_c(ℝ, ℝ)) (R : ℝ) (m : ℕ)
    (μ : RealVagueMeasure) : ℝ :=
  Real.exp (-(∫ y, symmetricStep f R m y ∂(μ : Measure ℝ)))

theorem symmetricStepLaplace_eq_clipped (f : C_c(ℝ, ℝ)) (R : ℝ) (m : ℕ)
    (μ : RealVagueMeasure) :
    symmetricStepLaplace f R m μ =
      clippedVectorLaplace (fun i : Fin (2 * m) => f (symmetricGrid R m i.val))
        (symmetricGridMassVector R m μ) := by
  rw [symmetricStepLaplace, symmetricStep, integral_poissonStepDensity _ _
    (fun _ => measurableSet_Ioc) _ (fun _ => realVagueMeasure_Ioc_ne_top μ _ _)]
  unfold clippedVectorLaplace symmetricGridMassVector
  simp only [max_eq_right measureReal_nonneg, mul_comm]

theorem measurable_symmetricStepLaplace (f : C_c(ℝ, ℝ)) (R : ℝ) (m : ℕ) :
    Measurable (symmetricStepLaplace f R m) := by
  have heq : symmetricStepLaplace f R m =
      (fun μ => clippedVectorLaplace (fun i : Fin (2 * m) => f (symmetricGrid R m i.val))
        (symmetricGridMassVector R m μ)) :=
    funext (symmetricStepLaplace_eq_clipped f R m)
  rw [heq]
  have hc : Continuous (clippedVectorLaplace
      (fun i : Fin (2 * m) => f (symmetricGrid R m i.val))) := by
    unfold clippedVectorLaplace
    fun_prop
  exact hc.measurable.comp (measurable_symmetricGridMassVector R m)

theorem symmetricStepLaplace_bounds (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f)
    (R : ℝ) (m : ℕ) (μ : RealVagueMeasure) :
    0 ≤ symmetricStepLaplace f R m μ ∧ symmetricStepLaplace f R m μ ≤ 1 := by
  rw [symmetricStepLaplace_eq_clipped]
  exact clippedVectorLaplace_bounds _ (fun i => hf _) _

theorem symmetricStepLaplace_integral_tendsto_of_grid_law_tendsto
    (νs : ℕ → ProbabilityMeasure RealVagueMeasure) (ν : ProbabilityMeasure RealVagueMeasure)
    (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) (R : ℝ) (m : ℕ)
    (hgrid : Tendsto (fun n => (νs n).map (measurable_symmetricGridMassVector R m).aemeasurable)
      atTop (𝓝 (ν.map (measurable_symmetricGridMassVector R m).aemeasurable))) :
    Tendsto (fun n => ∫ μ, symmetricStepLaplace f R m μ ∂(νs n : Measure RealVagueMeasure))
      atTop (𝓝 (∫ μ, symmetricStepLaplace f R m μ ∂(ν : Measure RealVagueMeasure))) := by
  let t : Fin (2 * m) → ℝ := fun i => f (symmetricGrid R m i.val)
  have ht : ∀ i, 0 ≤ t i := fun i => hf _
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hgrid
    (clippedVectorLaplaceBounded t ht)
  have heq (Q : ProbabilityMeasure RealVagueMeasure) :
      (∫ v, clippedVectorLaplaceBounded t ht v
        ∂(Q.map (measurable_symmetricGridMassVector R m).aemeasurable :
          Measure (Fin (2 * m) → ℝ))) =
        ∫ μ, symmetricStepLaplace f R m μ ∂(Q : Measure RealVagueMeasure) := by
    rw [integral_probabilityMeasure_map Q (measurable_symmetricGridMassVector R m)]
    apply integral_congr_ae
    filter_upwards with μ
    change clippedVectorLaplace t (symmetricGridMassVector R m μ) = _
    exact (symmetricStepLaplace_eq_clipped f R m μ).symm
  simpa only [heq] using h

end FixedCouplingPoisson
