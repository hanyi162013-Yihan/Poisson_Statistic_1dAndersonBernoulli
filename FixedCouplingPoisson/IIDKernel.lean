import FixedCouplingPoisson.IIDMarkov

/-! Deterministic-time versions of the actual stopped state/future kernel,
with the natural past sigma algebra retained explicitly. -/
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem iidMeasure_condExp_past_futureKernel {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) (n : ℕ) {X : PotentialSpace → S}
    (hX : Measurable[pastMeasurableSpace n] X) {f : S × PotentialSpace → ℝ}
    (hfm : Measurable f)
    (hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law))) :
    (iidMeasure law)[(fun ω => f (X ω, potentialShift n ω)) | pastMeasurableSpace n] =ᵐ[
      iidMeasure law] (fun ω => futureKernel law f (X ω)) := by
  have hτ := isStoppingTime_const potentialFiltration n
  have hfinite : ∀ᵐ ω ∂iidMeasure law,
      (fun _ : PotentialSpace => (n : WithTop ℕ)) ω ≠ ⊤ :=
    ae_of_all _ fun _ => WithTop.coe_ne_top
  have hspace : hτ.measurableSpace = pastMeasurableSpace n := by
    calc
      hτ.measurableSpace = potentialFiltration n :=
        IsStoppingTime.measurableSpace_const potentialFiltration n
      _ = pastMeasurableSpace n := rfl
  have hX' : Measurable[hτ.measurableSpace] X := by
    rw [hspace]
    exact hX
  simpa only [hspace, stoppedPotentialFuture,
    WithTop.untopD_coe] using
    iidMeasure_condExp_stopped_futureKernel law hτ hfinite hX' hfm hf

theorem iidMeasure_integral_past_futureKernel {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) (n : ℕ) {X : PotentialSpace → S}
    (hX : Measurable[pastMeasurableSpace n] X) {f : S × PotentialSpace → ℝ}
    (hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law))) :
    (∫ ω, f (X ω, potentialShift n ω) ∂iidMeasure law) =
      ∫ x, futureKernel law f x ∂(iidMeasure law).map X := by
  have hτ := isStoppingTime_const potentialFiltration n
  have hfinite : ∀ᵐ ω ∂iidMeasure law,
      (fun _ : PotentialSpace => (n : WithTop ℕ)) ω ≠ ⊤ :=
    ae_of_all _ fun _ => WithTop.coe_ne_top
  have hspace : hτ.measurableSpace = pastMeasurableSpace n := by
    calc
      hτ.measurableSpace = potentialFiltration n :=
        IsStoppingTime.measurableSpace_const potentialFiltration n
      _ = pastMeasurableSpace n := rfl
  have hX' : Measurable[hτ.measurableSpace] X := by
    rw [hspace]
    exact hX
  simpa only [hspace, stoppedPotentialFuture,
    WithTop.untopD_coe] using
    iidMeasure_integral_stopped_state_future law hτ hfinite hX' hf

end FixedCouplingPoisson
