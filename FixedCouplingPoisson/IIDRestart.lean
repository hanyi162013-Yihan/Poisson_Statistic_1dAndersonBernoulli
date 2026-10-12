import FixedCouplingPoisson.IIDModel
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Prod

/-!
Conditional restart formulas derived from the actual infinite iid law.
Measurability of a state with respect to the stopped past is the usual
adaptedness requirement; freshness is proved here, rather than assumed.
-/
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory

noncomputable def futureKernel {S : Type*} (law : PotentialLaw)
    (f : S × PotentialSpace → ℝ) (x : S) : ℝ :=
  ∫ ξ, f (x, ξ) ∂iidMeasure law

theorem measurable_futureKernel {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {f : S × PotentialSpace → ℝ} (hf : Measurable f) :
    Measurable (futureKernel law f) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

theorem iidMeasure_stopped_state_future_independent {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) {X : PotentialSpace → S}
    (hX : Measurable[hτ.measurableSpace] X) :
    IndepFun X (stoppedPotentialFuture τ) (iidMeasure law) := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left
    (iidMeasure_ae_finite_stopped_future_independent law hτ hfinite) hX.comap_le

theorem iidMeasure_stopped_state_future_map {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) {X : PotentialSpace → S}
    (hX : Measurable[hτ.measurableSpace] X) :
    (iidMeasure law).map (fun ω => (X ω, stoppedPotentialFuture τ ω)) =
      ((iidMeasure law).map X).prod (iidMeasure law) := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hprod := (iidMeasure_stopped_state_future_independent law hτ hfinite hX).map_prod_eq_prod_map_map
    hXm.aemeasurable (measurable_stoppedPotentialFuture hτ).aemeasurable
  rw [hprod,
    iidMeasure_ae_finite_stopped_future_map law hτ hfinite]

/-- The actual joint restart integral, with the past state integrated against
its actual law and the future against a fresh iid copy. -/
theorem iidMeasure_integral_stopped_state_future {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) {X : PotentialSpace → S}
    (hX : Measurable[hτ.measurableSpace] X) {f : S × PotentialSpace → ℝ}
    (hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law))) :
    (∫ ω, f (X ω, stoppedPotentialFuture τ ω) ∂iidMeasure law) =
      ∫ x, futureKernel law f x ∂(iidMeasure law).map X := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hpair : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
    hXm.prodMk (measurable_stoppedPotentialFuture hτ)
  have hmap := iidMeasure_stopped_state_future_map law hτ hfinite hX
  have hfm : AEStronglyMeasurable f
      ((iidMeasure law).map (fun ω => (X ω, stoppedPotentialFuture τ ω))) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  rw [← integral_map hpair.aemeasurable hfm, hmap, integral_prod _ hf]
  rfl

/-- A future-only observable has its original expectation conditionally on
the stopped past. For integrable observables this is the usual restart law. -/
theorem iidMeasure_condExp_stopped_future (law : PotentialLaw)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {g : PotentialSpace → ℝ} (hg : Measurable g) :
    (iidMeasure law)[(fun ω => g (stoppedPotentialFuture τ ω)) | hτ.measurableSpace] =ᵐ[
      iidMeasure law] (fun _ => ∫ ξ, g ξ ∂iidMeasure law) := by
  have hgm : @Measurable PotentialSpace ℝ
      (MeasurableSpace.comap (stoppedPotentialFuture τ) inferInstance) inferInstance
      (fun ω => g (stoppedPotentialFuture τ ω)) := by
    intro A hA
    exact ⟨g ⁻¹' A, hg hA, rfl⟩
  have hc := condExp_indep_eq
    (measurable_stoppedPotentialFuture hτ).comap_le hτ.measurableSpace_le
    hgm.stronglyMeasurable
    (iidMeasure_ae_finite_stopped_future_independent law hτ hfinite).symm
  have hi : (∫ ω, g (stoppedPotentialFuture τ ω) ∂iidMeasure law) =
      ∫ ξ, g ξ ∂iidMeasure law := by
    rw [← integral_map (measurable_stoppedPotentialFuture hτ).aemeasurable
      hg.aestronglyMeasurable, iidMeasure_ae_finite_stopped_future_map law hτ hfinite]
  exact hc.trans (Eventually.of_forall fun _ => hi)

end FixedCouplingPoisson
