import FixedCouplingPoisson.JointLaplaceWeak

noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Integer Laplace transforms determine an actual nonnegative real probability law. -/
theorem probabilityMeasure_eq_of_nonnegative_integer_laplace
    (μ ν : ProbabilityMeasure ℝ)
    (hμ0 : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x)
    (hν0 : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x)
    (hLap : ∀ m : ℕ,
      (∫ x, Real.exp (-(m : ℝ) * x) ∂(μ : Measure ℝ)) =
        ∫ x, Real.exp (-(m : ℝ) * x) ∂(ν : Measure ℝ)) : μ = ν := by
  let X : ℝ → Unit → ℝ := fun x _ => max x 0
  let Y : ℝ → Unit → ℝ := fun x _ => x
  have hX : Measurable X := by unfold X; fun_prop
  have hY : Measurable Y := by unfold Y; fun_prop
  let νv : ProbabilityMeasure (Unit → ℝ) := ν.map hY.aemeasurable
  have hνv : ∀ᵐ x ∂(νv : Measure (Unit → ℝ)), ∀ j, 0 ≤ x j := by
    change ∀ᵐ x ∂(ν : Measure ℝ).map Y, ∀ j, 0 ≤ x j
    apply (ae_map_iff hY.aemeasurable (by measurability)).mpr
    filter_upwards [hν0] with x hx
    exact fun _ => hx
  have hlap (m : Unit → ℕ) :
      (∫ x, realMixedLaplaceTest m (X x) ∂(μ : Measure ℝ)) =
        ∫ x, realMixedLaplaceTest m x ∂(νv : Measure (Unit → ℝ)) := by
    change _ = ∫ x, realMixedLaplaceTest m x ∂(ν : Measure ℝ).map Y
    rw [integral_map hY.aemeasurable
      (show Continuous (realMixedLaplaceTest m) from by
        unfold realMixedLaplaceTest; fun_prop).aestronglyMeasurable]
    have hs : (∫ x, realMixedLaplaceTest m (X x) ∂(μ : Measure ℝ)) =
        ∫ x, Real.exp (-(m () : ℝ) * x) ∂(μ : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [hμ0] with x hx
      simp [realMixedLaplaceTest, X, max_eq_left hx]
    rw [hs, hLap (m ())]
    simp [realMixedLaplaceTest, Y]
  have hweak := laws_tendsto_of_mixed_integer_laplace
    (F := (atTop : Filter ℕ)) μ (fun _ => X) (fun _ => hX)
    (fun _ x _ => le_max_right x 0) νv hνv
    (fun m => by simpa only [hlap m] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ∫ x, realMixedLaplaceTest m x ∂(νv : Measure (Unit → ℝ))) atTop
        (𝓝 (∫ x, realMixedLaplaceTest m x ∂(νv : Measure (Unit → ℝ))))))
  have heq : μ.map hX.aemeasurable = νv :=
    tendsto_nhds_unique tendsto_const_nhds hweak
  have hm := congrArg (fun P : ProbabilityMeasure (Unit → ℝ) =>
    (P : Measure (Unit → ℝ)).map (fun x => x ())) heq
  change ((μ : Measure ℝ).map X).map (fun x => x ()) =
    ((ν : Measure ℝ).map Y).map (fun x => x ()) at hm
  rw [Measure.map_map (by fun_prop) hX, Measure.map_map (by fun_prop) hY] at hm
  have he : (fun x : ℝ => max x 0) =ᵐ[(μ : Measure ℝ)] id := by
    filter_upwards [hμ0] with x hx
    exact max_eq_left hx
  change (μ : Measure ℝ).map (fun x => max x 0) = (ν : Measure ℝ).map id at hm
  rw [Measure.map_congr he, Measure.map_id, Measure.map_id] at hm
  exact ProbabilityMeasure.toMeasure_injective hm

end FixedCouplingPoisson
