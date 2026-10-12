import FixedCouplingPoisson.SymmetricGridLaws

/-! The actual finite interval laws imply every genuine nonnegative C_c
Laplace limit. Uniform tails come from an actually convergent scalar count
law; no bound on expected counts is assumed. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter
open scoped Topology CompactlySupported

theorem real_upper_tail_bound_of_enclosingMass_law_bound
    (Q : ProbabilityMeasure RealVagueMeasure) (R M δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : (Q.map (measurable_symmetricEnclosingMass R).aemeasurable : Measure ℝ)
      (Ioi M) ≤ ENNReal.ofReal δ) :
    (Q : Measure RealVagueMeasure).real {μ | M < symmetricEnclosingMass R μ} ≤ δ := by
  have heq : (Q : Measure RealVagueMeasure) {μ | M < symmetricEnclosingMass R μ} =
      (Q.map (measurable_symmetricEnclosingMass R).aemeasurable : Measure ℝ) (Ioi M) := by
    exact (ProbabilityMeasure.map_apply' Q
      (measurable_symmetricEnclosingMass R).aemeasurable measurableSet_Ioi).symm
  rw [measureReal_def, heq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hδ)

theorem symmetricStep_laplace_expectation_error
    (Q : ProbabilityMeasure RealVagueMeasure) (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f)
    {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m)
    (hsupp : tsupport f ⊆ Ioo (-R) R) {η M : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M)
    (happrox : ∀ y, |f y - symmetricStep f R m y| ≤ η) :
    |(∫ μ, RealVagueMeasure.laplaceTest f μ ∂(Q : Measure RealVagueMeasure)) -
      (∫ μ, symmetricStepLaplace f R m μ ∂(Q : Measure RealVagueMeasure))| ≤
      η * M + (Q : Measure RealVagueMeasure).real {μ | M < symmetricEnclosingMass R μ} := by
  apply integral_difference_le_truncated_count Q
    (RealVagueMeasure.laplaceTest f) (symmetricStepLaplace f R m) (symmetricEnclosingMass R)
    (RealVagueMeasure.continuous_laplaceTest f).measurable
    (measurable_symmetricStepLaplace f R m) (measurable_symmetricEnclosingMass R)
    (RealVagueMeasure.laplaceTest_mem_Icc f hf) (symmetricStepLaplace_bounds f hf R m) hη hM
  intro μ
  exact symmetricStep_laplace_error μ f hf hR hm hsupp hη happrox

/-- Only a symmetric grid with zero as an endpoint is needed. The scalar
enclosing count supplies uniform truncation for the sequence and its target. -/
theorem compactTestLaplace_integral_tendsto_of_symmetricGrid_laws
    (νs : ℕ → ProbabilityMeasure RealVagueMeasure) (ν : ProbabilityMeasure RealVagueMeasure)
    (hgrid : ∀ R : ℝ, 0 < R → ∀ m : ℕ, 0 < m →
      Tendsto (fun n => (νs n).map (measurable_symmetricGridMassVector R m).aemeasurable)
        atTop (𝓝 (ν.map (measurable_symmetricGridMassVector R m).aemeasurable)))
    (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) :
    Tendsto (fun n => ∫ μ, RealVagueMeasure.laplaceTest f μ ∂(νs n : Measure RealVagueMeasure))
      atTop (𝓝 (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(ν : Measure RealVagueMeasure))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR, hsupp⟩ := exists_symmetric_support_window f
  have hcount := symmetricEnclosingMass_law_tendsto_of_grid_law_tendsto νs ν hR
    (hgrid R hR 1 (by decide))
  obtain ⟨M, hM, htail, htailTarget⟩ := exists_uniform_upper_tail_of_weak_tendsto
    (fun n => (νs n).map (measurable_symmetricEnclosingMass R).aemeasurable)
    (ν.map (measurable_symmetricEnclosingMass R).aemeasurable) hcount
    (ENNReal.ofReal (ε / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  let η : ℝ := ε / (8 * M)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hM)
  have hηM : η * M = ε / 8 := by
    dsimp [η]
    field_simp [ne_of_gt hM] <;> ring
  obtain ⟨m, hm, happrox⟩ := symmetricStep_uniform_approx f hR hsupp hη
  have hsource (n : ℕ) :
      |(∫ μ, RealVagueMeasure.laplaceTest f μ ∂(νs n : Measure RealVagueMeasure)) -
        (∫ μ, symmetricStepLaplace f R m μ ∂(νs n : Measure RealVagueMeasure))| ≤ ε / 4 := by
    have h := symmetricStep_laplace_expectation_error (νs n) f hf hR hm hsupp
      hη.le hM.le happrox
    have ht := real_upper_tail_bound_of_enclosingMass_law_bound (νs n) R M (ε / 8)
      (by positivity) (htail n)
    rw [hηM] at h
    linarith
  have htarget :
      |(∫ μ, symmetricStepLaplace f R m μ ∂(ν : Measure RealVagueMeasure)) -
        (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(ν : Measure RealVagueMeasure))| ≤ ε / 4 := by
    rw [abs_sub_comm]
    have h := symmetricStep_laplace_expectation_error ν f hf hR hm hsupp hη.le hM.le happrox
    have ht := real_upper_tail_bound_of_enclosingMass_law_bound ν R M (ε / 8)
      (by positivity) htailTarget
    rw [hηM] at h
    linarith
  have hstep := symmetricStepLaplace_integral_tendsto_of_grid_law_tendsto
    νs ν f hf R m (hgrid R hR m hm)
  filter_upwards [Metric.tendsto_nhds.mp hstep (ε / 2) (by positivity)] with n hn
  rw [Real.dist_eq] at hn ⊢
  have htri := abs_sub_le
    (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(νs n : Measure RealVagueMeasure))
    (∫ μ, symmetricStepLaplace f R m μ ∂(νs n : Measure RealVagueMeasure))
    (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(ν : Measure RealVagueMeasure))
  have htri' := abs_sub_le
    (∫ μ, symmetricStepLaplace f R m μ ∂(νs n : Measure RealVagueMeasure))
    (∫ μ, symmetricStepLaplace f R m μ ∂(ν : Measure RealVagueMeasure))
    (∫ μ, RealVagueMeasure.laplaceTest f μ ∂(ν : Measure RealVagueMeasure))
  linarith [hsource n]

end FixedCouplingPoisson
