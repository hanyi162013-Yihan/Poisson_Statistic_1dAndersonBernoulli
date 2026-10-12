import FixedCouplingPoisson.IIDRestart

/-!
State-dependent conditional restart kernels on the actual iid sample space.
The dependence on the stopped state is retained. No Markov or restart property
is supplied as an extra hypothesis.
-/
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory

/-- Restricting to a stopped-past event changes only the state marginal of
the joint state/future law. -/
theorem iidMeasure_restrict_stopped_state_future_map {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) {X : PotentialSpace → S}
    (hX : Measurable[hτ.measurableSpace] X)
    {s : Set PotentialSpace} (hs : MeasurableSet[hτ.measurableSpace] s) :
    ((iidMeasure law).restrict s).map (fun ω => (X ω, stoppedPotentialFuture τ ω)) =
      (((iidMeasure law).restrict s).map X).prod (iidMeasure law) := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hsm : MeasurableSet s := hτ.measurableSpace_le _ hs
  have hpair : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
    hXm.prodMk (measurable_stoppedPotentialFuture hτ)
  refine (Measure.prod_eq fun B A hB hA => ?_).symm
  rw [Measure.map_apply hpair (hB.prod hA), Measure.map_apply hXm hB,
    Measure.restrict_apply' hsm, Measure.restrict_apply' hsm]
  change iidMeasure law ((X ⁻¹' B ∩ stoppedPotentialFuture τ ⁻¹' A) ∩ s) =
    iidMeasure law (X ⁻¹' B ∩ s) * iidMeasure law A
  have hi := iidMeasure_ae_finite_stopped_inter_future law hτ hfinite
    ((hX hB).inter hs) hA
  simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hi

theorem iidMeasure_setIntegral_stopped_futureKernel {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) {X : PotentialSpace → S}
    (hX : Measurable[hτ.measurableSpace] X) {f : S × PotentialSpace → ℝ}
    (hfm : Measurable f)
    (hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)))
    {s : Set PotentialSpace} (hs : MeasurableSet[hτ.measurableSpace] s) :
    (∫ ω in s, futureKernel law f (X ω) ∂iidMeasure law) =
      ∫ ω in s, f (X ω, stoppedPotentialFuture τ ω) ∂iidMeasure law := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hpair : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
    hXm.prodMk (measurable_stoppedPotentialFuture hτ)
  have hmap := iidMeasure_restrict_stopped_state_future_map law hτ hfinite hX hs
  have hfres : Integrable f
      ((((iidMeasure law).restrict s).map X).prod (iidMeasure law)) :=
    hf.mono_measure (Measure.prod_mono
      (Measure.map_mono Measure.restrict_le_self hXm) le_rfl)
  calc
    (∫ ω in s, futureKernel law f (X ω) ∂iidMeasure law) =
        ∫ x, futureKernel law f x ∂((iidMeasure law).restrict s).map X :=
      (integral_map hXm.aemeasurable
        (measurable_futureKernel law hfm).aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(((iidMeasure law).restrict s).map X).prod (iidMeasure law) :=
      (integral_prod f hfres).symm
    _ = ∫ ω in s, f (X ω, stoppedPotentialFuture τ ω) ∂iidMeasure law := by
      rw [← hmap, integral_map hpair.aemeasurable hfm.aestronglyMeasurable]

/-- The conditional Markov kernel at every almost surely finite discrete
stopping time, derived from the full stopped-future independence theorem. -/
theorem iidMeasure_condExp_stopped_futureKernel {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) {X : PotentialSpace → S}
    (hX : Measurable[hτ.measurableSpace] X) {f : S × PotentialSpace → ℝ}
    (hfm : Measurable f)
    (hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law))) :
    (iidMeasure law)[(fun ω => f (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace] =ᵐ[
      iidMeasure law] (fun ω => futureKernel law f (X ω)) := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hpair : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
    hXm.prodMk (measurable_stoppedPotentialFuture hτ)
  have hmap := iidMeasure_stopped_state_future_map law hτ hfinite hX
  have hfmap : Integrable f
      ((iidMeasure law).map (fun ω => (X ω, stoppedPotentialFuture τ ω))) := by
    rw [hmap]
    exact hf
  have hfi : Integrable (fun ω => f (X ω, stoppedPotentialFuture τ ω)) (iidMeasure law) :=
    hfmap.comp_measurable hpair
  have hki : Integrable (fun ω => futureKernel law f (X ω)) (iidMeasure law) :=
    hf.integral_prod_left.comp_measurable hXm
  have hkm : Measurable[hτ.measurableSpace] (fun ω => futureKernel law f (X ω)) :=
    (measurable_futureKernel law hfm).comp hX
  exact (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hfi
    (fun _ _ _ => hki.integrableOn)
    (fun _ hs _ => iidMeasure_setIntegral_stopped_futureKernel law hτ hfinite hX hfm hf hs)
    hkm.stronglyMeasurable.aestronglyMeasurable).symm

end FixedCouplingPoisson
