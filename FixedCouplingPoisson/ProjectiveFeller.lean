import FixedCouplingPoisson.ProjectiveTopology
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Feller averages and stationary cluster points for the actual transfer law

The Markov step is the actual projective transfer action integrated against
`PotentialLaw.measure`. Dominated convergence proves its Feller property;
Fubini identifies test integrals with the genuine pushforward distribution.
Vanishing test defects identify cluster points as actual stationary measures.
The empirical Cesàro telescope is proved in the subsequent module.

No qualitative Furstenberg input is used in this module.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix
open scoped Topology

theorem continuous_forward_fixed_potential (E v : ℝ) :
    Continuous (transferProjective E v) := by
  apply projectivize_isQuotientMap.continuous_iff.mpr
  have hv : Continuous (fun u : NonzeroVector => (u : Vector2)) := continuous_subtype_val
  have hmul : Continuous (fun u : NonzeroVector => transfer E v *ᵥ (u : Vector2)) :=
    continuous_const.matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun u =>
    sl2_mulVec_ne_zero (transfer E v) (transfer_det _ _) u u.2)

theorem continuous_forward_fixed_direction (E : ℝ) (p : ProjectivePoint) :
    Continuous (fun v : ℝ => transferProjective E v p) := by
  have hp : (fun v : ℝ => transferProjective E v p) =
      (fun v : ℝ => projectivize ⟨transfer E v *ᵥ p.rep,
        sl2_mulVec_ne_zero (transfer E v) (transfer_det _ _) p.rep p.rep_nonzero⟩) := by
    funext v
    conv_lhs => rw [← Projectivization.mk_rep p]
    rfl
  rw [hp]
  have hmul : Continuous (fun v : ℝ => transfer E v *ᵥ p.rep) :=
    (continuous_transfer_fixed E).matrix_mulVec continuous_const
  exact continuous_projectivize.comp (hmul.subtype_mk fun v =>
    sl2_mulVec_ne_zero (transfer E v) (transfer_det _ _) p.rep p.rep_nonzero)

def forwardAverage (law : PotentialLaw) (E : ℝ) (f : C(ProjectivePoint, ℝ))
    (p : ProjectivePoint) : ℝ := ∫ v, f (transferProjective E v p) ∂law.measure

theorem integrable_forward_test (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (p : ProjectivePoint) :
    Integrable (fun v => f (transferProjective E v p)) law.measure := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_forward_fixed_direction E p)).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun v => f.norm_coe_le_norm _

theorem continuous_forwardAverage (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) : Continuous (forwardAverage law E f) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro p
    exact (f.continuous.comp (continuous_forward_fixed_direction E p)).measurable.aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun v => f.norm_coe_le_norm _
  · exact integrable_const ‖f‖
  · exact Filter.Eventually.of_forall fun v =>
      f.continuous.comp (continuous_forward_fixed_potential E v)

def forwardContinuousAverage (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) : C(ProjectivePoint, ℝ) :=
  ⟨forwardAverage law E f, continuous_forwardAverage law E f⟩


theorem integrable_forward_product_test (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (ν : ProbabilityMeasure ProjectivePoint) :
    Integrable (fun z : ℝ × ProjectivePoint => f (forwardStep E z))
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_forwardStep E)).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _

theorem forwardDistribution_average_integral (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (ν : ProbabilityMeasure ProjectivePoint) :
    (∫ p, f p ∂(forwardDistribution law E ν : Measure ProjectivePoint)) =
      ∫ p, forwardAverage law E f p ∂(ν : Measure ProjectivePoint) := by
  change (∫ p, f p ∂((inputDistribution law ν : Measure (ℝ × ProjectivePoint)).map
    (forwardStep E))) = _
  rw [integral_map (measurable_forwardStep E).aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact integral_prod_symm _ (integrable_forward_product_test law E f ν)

theorem forward_stationary_of_average_test (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint)
    (h : ∀ f : C(ProjectivePoint, ℝ),
      (∫ p, forwardAverage law E f p ∂(ν : Measure ProjectivePoint)) =
        ∫ p, f p ∂(ν : Measure ProjectivePoint)) : ForwardStationary law E ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact (forwardDistribution_average_integral law E f.toContinuousMap ν).trans
    (h f.toContinuousMap)

def forwardTestDefect (law : PotentialLaw) (E : ℝ) (f : C(ProjectivePoint, ℝ))
    (ν : ProbabilityMeasure ProjectivePoint) : ℝ :=
  (∫ p, forwardAverage law E f p ∂(ν : Measure ProjectivePoint)) -
    ∫ p, f p ∂(ν : Measure ProjectivePoint)

theorem continuous_forwardTestDefect (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) : Continuous (forwardTestDefect law E f) :=
  (ProbabilityMeasure.continuous_integral_continuousMap (forwardContinuousAverage law E f)).sub
    (ProbabilityMeasure.continuous_integral_continuousMap f)

/-- Ordinary cluster argument for actual measures. The vanishing-defect
hypothesis must still be derived for the actual empirical Cesàro measures. -/
theorem forward_stationary_of_cluster_vanishing_defect (law : PotentialLaw) (E : ℝ)
    (μ : ℕ → ProbabilityMeasure ProjectivePoint) (ν : ProbabilityMeasure ProjectivePoint)
    (hν : MapClusterPt ν Filter.atTop μ)
    (hd : ∀ f : C(ProjectivePoint, ℝ), Filter.Tendsto
      (fun n => forwardTestDefect law E f (μ n)) Filter.atTop (𝓝 0)) :
    ForwardStationary law E ν := by
  apply forward_stationary_of_average_test law E ν
  intro f
  apply sub_eq_zero.mp
  have hc := hν.continuousAt_comp (continuous_forwardTestDefect law E f).continuousAt
  exact eq_of_nhds_neBot (hc.clusterPt.mono (hd f))

end FixedCouplingPoisson.Furstenberg
