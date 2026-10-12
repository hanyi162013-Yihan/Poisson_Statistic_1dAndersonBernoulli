import FixedCouplingPoisson.UpperLayer
import FixedCouplingPoisson.IIDMarkov

/-!
# Actual remaining waiting time after upper-layer entrance

The integrability of the stopped-state future observable is derived from
its pathwise equality to the remaining part of the original crossing time.
The full iid future law then gives its exact iterated-integral formula.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter
open scoped ProbabilityTheory

/-- The entire number of remaining steps; the natural subtraction is also
well defined on the exceptional paths assigned the default value zero. -/
def canonicalUpperLayerRemaining (E δ θ φ h : ℝ) (ω : PotentialSpace) : ℝ :=
  (((canonicalCrossingTime E δ θ φ ω).untopD 0 -
    (canonicalUpperLayerTime E δ θ φ h ω).untopD 0 : ℕ) : ℝ)

theorem canonicalUpperLayerRemaining_measurable (E δ θ φ h : ℝ) :
    Measurable (canonicalUpperLayerRemaining E δ θ φ h) := by
  exact (measurable_of_countable (fun z : ℕ × ℕ => ((z.1 - z.2 : ℕ) : ℝ))).comp
    (((WithTop.measurable_untopD 0).comp (canonicalCrossingTime_measurable E δ θ φ)).prodMk
      ((WithTop.measurable_untopD 0).comp (canonicalUpperLayerTime_measurable E δ θ φ h)))

theorem canonicalUpperLayerRemaining_nonneg (E δ θ φ h : ℝ) (ω : PotentialSpace) :
    0 ≤ canonicalUpperLayerRemaining E δ θ φ h ω :=
  Nat.cast_nonneg _

theorem canonicalUpperLayerRemaining_le_crossing (E δ θ φ h : ℝ) (ω : PotentialSpace) :
    canonicalUpperLayerRemaining E δ θ φ h ω ≤
      (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) := by
  dsimp only [canonicalUpperLayerRemaining]
  exact_mod_cast Nat.sub_le ((canonicalCrossingTime E δ θ φ ω).untopD 0)
    ((canonicalUpperLayerTime E δ θ φ h ω).untopD 0)

theorem canonicalUpperLayerRemaining_integrable (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hT : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    Integrable (canonicalUpperLayerRemaining E δ θ φ h) (iidMeasure law) := by
  apply hT.mono' (canonicalUpperLayerRemaining_measurable E δ θ φ h).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (canonicalUpperLayerRemaining_nonneg E δ θ φ h ω)]
    exact canonicalUpperLayerRemaining_le_crossing E δ θ φ h ω

/-- The measurable real-valued first crossing includes both initial angles
and the entire future path. -/
theorem canonicalCrossingReal_measurable_initial_path (E δ : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × PotentialSpace =>
      (((canonicalCrossingTime E δ z.1.1 z.1.2 z.2).untopD 0 : ℕ) : ℝ)) :=
  (measurable_of_countable (fun t : WithTop ℕ => ((t.untopD 0 : ℕ) : ℝ))).comp
    (canonicalCrossingTime_measurable_initial_path E δ)

theorem canonicalUpperLayerRemaining_ae_restart (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    (fun ω => (((canonicalCrossingTime E δ (canonicalUpperLayerState E δ θ φ h ω).1
      (canonicalUpperLayerState E δ θ φ h ω).2
      (stoppedPotentialFuture (canonicalUpperLayerTime E δ θ φ h) ω)).untopD 0 : ℕ) : ℝ))
        =ᵐ[iidMeasure law] canonicalUpperLayerRemaining E δ θ φ h := by
  filter_upwards [hfinite] with ω hω
  rw [canonicalUpperLayerTime_crossing_restart E δ θ φ h hh ω hω]
  simp only [canonicalUpperLayerRemaining, Nat.cast_withTop, WithTop.untopD_coe]

/-- Almost-sure finiteness is retained by the actual joint stopped-state
and fresh-future law; the default real value at infinity is not used to infer it. -/
theorem canonicalUpperLayer_future_crossing_ae_finite (law : PotentialLaw)
    (E δ θ φ h : ℝ) (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    ∀ᵐ z : (ℝ × ℝ) × PotentialSpace
      ∂(((iidMeasure law).map (canonicalUpperLayerState E δ θ φ h)).prod (iidMeasure law)),
        canonicalCrossingTime E δ z.1.1 z.1.2 z.2 ≠ ⊤ := by
  have hX := canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hXm : Measurable (canonicalUpperLayerState E δ θ φ h) :=
    hX.mono (canonicalUpperLayerTime_isStoppingTime E δ θ φ h).measurableSpace_le le_rfl
  have hpair : Measurable (fun ω => (canonicalUpperLayerState E δ θ φ h ω,
      stoppedPotentialFuture (canonicalUpperLayerTime E δ θ φ h) ω)) :=
    hXm.prodMk (measurable_stoppedPotentialFuture
      (canonicalUpperLayerTime_isStoppingTime E δ θ φ h))
  have hpred : MeasurableSet {z : (ℝ × ℝ) × PotentialSpace |
      canonicalCrossingTime E δ z.1.1 z.1.2 z.2 ≠ ⊤} :=
    (measurableSet_eq_fun (canonicalCrossingTime_measurable_initial_path E δ)
      measurable_const).compl
  rw [← iidMeasure_upperLayer_state_future_map law E δ θ φ h hh hfinite]
  apply (ae_map_iff hpair.aemeasurable hpred).mpr
  filter_upwards [hfinite] with ω hω
  rw [canonicalUpperLayerTime_crossing_restart E δ θ φ h hh ω hω]
  exact WithTop.coe_ne_top

/-- For almost every stopped pair occurring in the original model, the
fresh iid future really crosses in finite time almost surely. -/
theorem canonicalUpperLayer_stopped_future_ae_finite (law : PotentialLaw)
    (E δ θ φ h : ℝ) (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    ∀ᵐ ω ∂iidMeasure law, ∀ᵐ ξ ∂iidMeasure law,
      canonicalCrossingTime E δ (canonicalUpperLayerState E δ θ φ h ω).1
        (canonicalUpperLayerState E δ θ φ h ω).2 ξ ≠ ⊤ := by
  have hX := canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hXm : Measurable (canonicalUpperLayerState E δ θ φ h) :=
    hX.mono (canonicalUpperLayerTime_isStoppingTime E δ θ φ h).measurableSpace_le le_rfl
  exact ae_of_ae_map hXm.aemeasurable (Measure.ae_ae_of_ae_prod
    (canonicalUpperLayer_future_crossing_ae_finite law E δ θ φ h hh hfinite))

/-- The actual future crossing observable is product-integrable because it
is the remaining part of an integrable original waiting time. -/
theorem canonicalUpperLayer_future_crossing_integrable (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤)
    (hT : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    Integrable (fun z : (ℝ × ℝ) × PotentialSpace =>
      (((canonicalCrossingTime E δ z.1.1 z.1.2 z.2).untopD 0 : ℕ) : ℝ))
      (((iidMeasure law).map (canonicalUpperLayerState E δ θ φ h)).prod (iidMeasure law)) := by
  let τ := canonicalUpperLayerTime E δ θ φ h
  let X := canonicalUpperLayerState E δ θ φ h
  let f : (ℝ × ℝ) × PotentialSpace → ℝ := fun z =>
    (((canonicalCrossingTime E δ z.1.1 z.1.2 z.2).untopD 0 : ℕ) : ℝ)
  have hτ : IsStoppingTime potentialFiltration τ := canonicalUpperLayerTime_isStoppingTime E δ θ φ h
  have hσ : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤ :=
    canonicalUpperLayerTime_ae_finite law E δ θ φ h hh hfinite
  have hX : Measurable[hτ.measurableSpace] X :=
    canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hpair : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
    hXm.prodMk (measurable_stoppedPotentialFuture hτ)
  have hfm : Measurable f := canonicalCrossingReal_measurable_initial_path E δ
  have heq : (fun ω => f (X ω, stoppedPotentialFuture τ ω)) =ᵐ[iidMeasure law]
      canonicalUpperLayerRemaining E δ θ φ h :=
    canonicalUpperLayerRemaining_ae_restart law E δ θ φ h hh hfinite
  have hcomp : Integrable (fun ω => f (X ω, stoppedPotentialFuture τ ω)) (iidMeasure law) :=
    (canonicalUpperLayerRemaining_integrable law E δ θ φ h hT).congr heq.symm
  have hfmap : Integrable f ((iidMeasure law).map
      (fun ω => (X ω, stoppedPotentialFuture τ ω))) :=
    (integrable_map_measure hfm.aestronglyMeasurable hpair.aemeasurable).mpr hcomp
  rwa [iidMeasure_stopped_state_future_map law hτ hσ hX] at hfmap

/-- Fresh-future waiting time is integrable at almost every actual stopped state. -/
theorem canonicalUpperLayer_stopped_future_integrable (law : PotentialLaw)
    (E δ θ φ h : ℝ) (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤)
    (hT : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    ∀ᵐ ω ∂iidMeasure law, Integrable (fun ξ => (((canonicalCrossingTime E δ
      (canonicalUpperLayerState E δ θ φ h ω).1
      (canonicalUpperLayerState E δ θ φ h ω).2 ξ).untopD 0 : ℕ) : ℝ)) (iidMeasure law) := by
  have hX := canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hXm : Measurable (canonicalUpperLayerState E δ θ φ h) :=
    hX.mono (canonicalUpperLayerTime_isStoppingTime E δ θ φ h).measurableSpace_le le_rfl
  exact ae_of_ae_map hXm.aemeasurable
    (canonicalUpperLayer_future_crossing_integrable law E δ θ φ h hh hfinite hT).prod_right_ae

/-- The stopped-state future mean is also integrable under the original iid law. -/
theorem canonicalUpperLayer_future_mean_integrable (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤)
    (hT : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    Integrable (fun ω => ∫ ξ, (((canonicalCrossingTime E δ
      (canonicalUpperLayerState E δ θ φ h ω).1
      (canonicalUpperLayerState E δ θ φ h ω).2 ξ).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)
        (iidMeasure law) := by
  have hX := canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hXm : Measurable (canonicalUpperLayerState E δ θ φ h) :=
    hX.mono (canonicalUpperLayerTime_isStoppingTime E δ θ φ h).measurableSpace_le le_rfl
  have hi : Integrable (fun x : ℝ × ℝ =>
      ∫ ξ, (((canonicalCrossingTime E δ x.1 x.2 ξ).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)
        ((iidMeasure law).map (canonicalUpperLayerState E δ θ φ h)) :=
    (canonicalUpperLayer_future_crossing_integrable law E δ θ φ h hh hfinite hT).integral_prod_left
  exact hi.comp_measurable hXm

/-- The exact conditional mean of all remaining steps is the actual fresh-iid
crossing mean evaluated at the stopped phase pair. -/
theorem canonicalUpperLayerRemaining_condExp_restart (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤)
    (hT : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    (iidMeasure law)[canonicalUpperLayerRemaining E δ θ φ h |
      (canonicalUpperLayerTime_isStoppingTime E δ θ φ h).measurableSpace] =ᵐ[iidMeasure law]
        (fun ω => ∫ ξ, (((canonicalCrossingTime E δ
          (canonicalUpperLayerState E δ θ φ h ω).1
          (canonicalUpperLayerState E δ θ φ h ω).2 ξ).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) := by
  let τ := canonicalUpperLayerTime E δ θ φ h
  let X := canonicalUpperLayerState E δ θ φ h
  let f : (ℝ × ℝ) × PotentialSpace → ℝ := fun z =>
    (((canonicalCrossingTime E δ z.1.1 z.1.2 z.2).untopD 0 : ℕ) : ℝ)
  have hτ : IsStoppingTime potentialFiltration τ := canonicalUpperLayerTime_isStoppingTime E δ θ φ h
  have hσ : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤ :=
    canonicalUpperLayerTime_ae_finite law E δ θ φ h hh hfinite
  have hX : Measurable[hτ.measurableSpace] X :=
    canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hfm : Measurable f := canonicalCrossingReal_measurable_initial_path E δ
  have hfprod : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)) :=
    canonicalUpperLayer_future_crossing_integrable law E δ θ φ h hh hfinite hT
  have heq : (fun ω => f (X ω, stoppedPotentialFuture τ ω)) =ᵐ[iidMeasure law]
      canonicalUpperLayerRemaining E δ θ φ h :=
    canonicalUpperLayerRemaining_ae_restart law E δ θ φ h hh hfinite
  have hc := iidMeasure_condExp_stopped_futureKernel law hτ hσ hX hfm hfprod
  exact (condExp_congr_ae (m := hτ.measurableSpace) heq.symm).trans hc

/-- Exact stopped-state mean formula for the whole remaining waiting time.
The original crossing's integrability supplies every integrability hypothesis. -/
theorem canonicalUpperLayerRemaining_integral_restart (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤)
    (hT : Integrable (fun ω => (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))
      (iidMeasure law)) :
    (∫ ω, canonicalUpperLayerRemaining E δ θ φ h ω ∂iidMeasure law) =
      ∫ ω, (∫ ξ, (((canonicalCrossingTime E δ
        (canonicalUpperLayerState E δ θ φ h ω).1
        (canonicalUpperLayerState E δ θ φ h ω).2 ξ).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)
          ∂iidMeasure law := by
  let τ := canonicalUpperLayerTime E δ θ φ h
  let X := canonicalUpperLayerState E δ θ φ h
  let f : (ℝ × ℝ) × PotentialSpace → ℝ := fun z =>
    (((canonicalCrossingTime E δ z.1.1 z.1.2 z.2).untopD 0 : ℕ) : ℝ)
  have hτ : IsStoppingTime potentialFiltration τ := canonicalUpperLayerTime_isStoppingTime E δ θ φ h
  have hσ : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤ :=
    canonicalUpperLayerTime_ae_finite law E δ θ φ h hh hfinite
  have hX : Measurable[hτ.measurableSpace] X :=
    canonicalUpperLayerState_stopped_measurable E δ θ φ h
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hfm : Measurable f := canonicalCrossingReal_measurable_initial_path E δ
  have heq : (fun ω => f (X ω, stoppedPotentialFuture τ ω)) =ᵐ[iidMeasure law]
      canonicalUpperLayerRemaining E δ θ φ h :=
    canonicalUpperLayerRemaining_ae_restart law E δ θ φ h hh hfinite
  have hfprod : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)) :=
    canonicalUpperLayer_future_crossing_integrable law E δ θ φ h hh hfinite hT
  calc
    _ = ∫ ω, f (X ω, stoppedPotentialFuture τ ω) ∂iidMeasure law :=
      integral_congr_ae heq.symm
    _ = ∫ x, futureKernel law f x ∂(iidMeasure law).map X :=
      iidMeasure_integral_stopped_state_future law hτ hσ hX hfprod
    _ = ∫ ω, futureKernel law f (X ω) ∂iidMeasure law :=
      integral_map hXm.aemeasurable (measurable_futureKernel law hfm).aestronglyMeasurable
    _ = _ := rfl

end FixedCouplingPoisson
