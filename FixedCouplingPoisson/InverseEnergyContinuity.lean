import FixedCouplingPoisson.EnergyContinuity

/-!
# Weak energy continuity of the actual inverse stationary probability

The inverse transfer action and probability pushforward are the
ones defined in the frozen qualitative interface. Ordinary Feller and compact
closed-graph arguments supply continuity; inverse uniqueness is the only
qualitative conclusion used for continuity of the selected inverse law.
The actual inverse stationary log mean is also continuous in energy.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Matrix
open scoped Topology

theorem continuous_transferInv_energy_fixed_potential (v : ℝ) :
    Continuous (fun E : ℝ => transferInv E v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_id.sub continuous_const | exact continuous_const

theorem continuous_inverse_energy_fixed_potential (v : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => transferInverseProjective z.1 v z.2) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : ℝ × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hmul := ((continuous_transferInv_energy_fixed_potential v).comp continuous_fst).matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun z =>
    transferInv_mulVec_ne_zero z.1 v z.2 z.2.2)

theorem continuous_inverseTransferLogCocycle_energy_fixed_potential (v : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => inverseTransferLogCocycle z.1 v z.2) := by
  change Continuous (fun z : ℝ × ProjectivePoint =>
    Real.log (projectiveGrowth (transferInv z.1 v) z.2))
  exact (continuous_projectiveGrowth (fun E : ℝ => transferInv E v)
    (continuous_transferInv_energy_fixed_potential v)).log
      (fun z => (projectiveGrowth_transferInv_pos z.1 v z.2).ne')

theorem continuous_inverse_fixed_direction (E : ℝ) (p : ProjectivePoint) :
    Continuous (fun v : ℝ => transferInverseProjective E v p) := by
  have hp : (fun v : ℝ => transferInverseProjective E v p) =
      (fun v : ℝ => projectivize ⟨transferInv E v *ᵥ p.rep,
        transferInv_mulVec_ne_zero E v p.rep p.rep_nonzero⟩) := by
    funext v
    conv_lhs => rw [← Projectivization.mk_rep p]
    rfl
  rw [hp]
  have hmul : Continuous (fun v : ℝ => transferInv E v *ᵥ p.rep) :=
    (continuous_transferInv_fixed E).matrix_mulVec continuous_const
  exact continuous_projectivize.comp (hmul.subtype_mk fun v =>
    transferInv_mulVec_ne_zero E v p.rep p.rep_nonzero)

theorem continuous_of_unique_compact_fixedPoints {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (Φ : X × Y → Y) (hΦ : Continuous Φ) (σ : X → Y)
    (hfix : ∀ x, Φ (x, σ x) = σ x)
    (hunique : ∀ x y, Φ (x, y) = y → y = σ x) : Continuous σ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_of_unique_mapClusterPt
  intro y hy
  have hc := mapClusterPt_prodMk_of_tendsto (tendsto_id : Tendsto (fun a : X => a)
    (𝓝 x) (𝓝 x)) hy
  have hclosed : IsClosed {z : X × Y | Φ z = z.2} := isClosed_eq hΦ continuous_snd
  exact hunique x y (hclosed.mem_of_mapClusterPt hc (Eventually.of_forall hfix))

def inverseAverage (law : PotentialLaw) (E : ℝ) (f : C(ProjectivePoint, ℝ))
    (p : ProjectivePoint) : ℝ := ∫ v, f (transferInverseProjective E v p) ∂law.measure

theorem continuous_inverseAverage_energy (law : PotentialLaw) (f : C(ProjectivePoint, ℝ)) :
    Continuous (fun z : ℝ × ProjectivePoint => inverseAverage law z.1 f z.2) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro z
    exact (f.continuous.comp (continuous_inverse_fixed_direction z.1 z.2)).measurable.aestronglyMeasurable
  · intro z
    exact Filter.Eventually.of_forall fun v => f.norm_coe_le_norm _
  · exact integrable_const ‖f‖
  · exact Filter.Eventually.of_forall fun v =>
      f.continuous.comp (continuous_inverse_energy_fixed_potential v)

theorem continuous_inverseAverage (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) : Continuous (inverseAverage law E f) := by
  have harg : Continuous (fun p : ProjectivePoint => (E, p)) :=
    continuous_const.prodMk continuous_id
  have hcomp := (continuous_inverseAverage_energy law f).comp harg
  have hfun : (fun z : ℝ × ProjectivePoint => inverseAverage law z.1 f z.2) ∘
      (fun p : ProjectivePoint => (E, p)) = inverseAverage law E f := rfl
  rw [hfun] at hcomp
  exact hcomp

def inverseContinuousAverage (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) : C(ProjectivePoint, ℝ) :=
  ⟨inverseAverage law E f, continuous_inverseAverage law E f⟩

theorem continuous_inverseContinuousAverage_energy (law : PotentialLaw)
    (f : C(ProjectivePoint, ℝ)) : Continuous (fun E => inverseContinuousAverage law E f) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_inverseAverage_energy law f)

theorem integrable_inverse_product_test (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (ν : ProbabilityMeasure ProjectivePoint) :
    Integrable (fun z : ℝ × ProjectivePoint => f (inverseStep E z))
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_inverseStep E)).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _

theorem inverseDistribution_average_integral (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (ν : ProbabilityMeasure ProjectivePoint) :
    (∫ p, f p ∂(inverseDistribution law E ν : Measure ProjectivePoint)) =
      ∫ p, inverseAverage law E f p ∂(ν : Measure ProjectivePoint) := by
  change (∫ p, f p ∂((inputDistribution law ν : Measure (ℝ × ProjectivePoint)).map
    (inverseStep E))) = _
  rw [integral_map (measurable_inverseStep E).aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact integral_prod_symm _ (integrable_inverse_product_test law E f ν)

theorem continuous_inverseDistribution_energy (law : PotentialLaw) :
    Continuous (fun z : ℝ × ProbabilityMeasure ProjectivePoint => inverseDistribution law z.1 z.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  have h := continuous_testIntegral.comp
    (((continuous_inverseContinuousAverage_energy law f).comp continuous_fst).prodMk continuous_snd)
  convert h using 1
  funext z
  exact inverseDistribution_average_integral law z.1 f z.2

/-- Derived weak continuity of the inverse stationary law, for use in the
energy-uniform stationary CDF. No regularity field is assumed externally. -/
theorem continuous_selected_inverseMeasure (law : PotentialLaw) (input : Input law) :
    Continuous (fun E => (input.atEnergy E).inverseMeasure) := by
  exact continuous_of_unique_compact_fixedPoints
    (fun z : ℝ × ProbabilityMeasure ProjectivePoint => inverseDistribution law z.1 z.2)
    (continuous_inverseDistribution_energy law) (fun E => (input.atEnergy E).inverseMeasure)
    (fun E => (input.atEnergy E).inverse_stationary)
    (fun E ν hν => (input.atEnergy E).inverse_unique ν hν)

theorem continuous_oneStepInverseLogMean_energy (law : PotentialLaw) :
    Continuous (fun z : ℝ × ProjectivePoint => oneStepInverseLogMean law z.1 z.2) := by
  obtain ⟨M, hM, hb⟩ := law.bounded
  change Continuous (fun z : ℝ × ProjectivePoint =>
    ∫ v, inverseTransferLogCocycle z.1 v z.2 ∂law.measure)
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hnear : ∀ᶠ z : ℝ × ProjectivePoint in 𝓝 z₀, |z.1 - z₀.1| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (continuous_fst.tendsto z₀).eventually (Metric.ball_mem_nhds z₀.1 zero_lt_one)
  apply continuousAt_of_dominated (bound := fun _ : ℝ => Real.log (|z₀.1| + M + 3))
  · exact Filter.Eventually.of_forall fun z =>
      ((continuous_inverseTransferLogCocycle z.1).comp
        (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  · apply hnear.mono
    intro z hz
    have hE : |z.1| ≤ |z₀.1| + 1 := by
      have ha := abs_add_le (z.1 - z₀.1) z₀.1
      have heq : z.1 - z₀.1 + z₀.1 = z.1 := by ring
      rw [heq] at ha
      linarith
    exact hb.mono fun v hv => by
      rw [Real.norm_eq_abs]
      exact (abs_inverseTransferLogCocycle_le z.1 v M hM hv z.2).trans
        (Real.log_le_log (by positivity) (by linarith))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun v =>
      (continuous_inverseTransferLogCocycle_energy_fixed_potential v).continuousAt

def oneStepContinuousInverseLogMean (law : PotentialLaw) (E : ℝ) : C(ProjectivePoint, ℝ) :=
  ⟨oneStepInverseLogMean law E, continuous_oneStepInverseLogMean law E⟩

theorem continuous_oneStepContinuousInverseLogMean_energy (law : PotentialLaw) :
    Continuous (oneStepContinuousInverseLogMean law) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_oneStepInverseLogMean_energy law)

theorem continuous_selected_inverseStationaryMean (law : PotentialLaw) (input : Input law) :
    Continuous (fun E => inverseStationaryMean law E (input.atEnergy E).inverseMeasure) := by
  have h := continuous_testIntegral.comp
    ((continuous_oneStepContinuousInverseLogMean_energy law).prodMk
      (continuous_selected_inverseMeasure law input))
  convert h using 1
  funext E
  exact inverseStationaryMean_eq_integral_oneStep law E _

end FixedCouplingPoisson.Furstenberg
