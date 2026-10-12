import FixedCouplingPoisson.ProjectiveFeller
import FixedCouplingPoisson.IIDKernel
import FixedCouplingPoisson.Occupation

/-! The actual same-potential two-energy kernel acts
on continuous functions on the compact pair space, so every integral used
in its linearity proof is integrable. The conditional kernel is derived
from the already proved iid future law. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

abbrev ProjectivePair := ProjectivePoint × ProjectivePoint

def pairStep (E E' v : ℝ) (z : ProjectivePair) : ProjectivePair :=
  (transferProjective E v z.1, transferProjective E' v z.2)

theorem continuous_pairStep_fixed_potential (E E' v : ℝ) : Continuous (pairStep E E' v) :=
  ((continuous_forward_fixed_potential E v).comp continuous_fst).prodMk
    ((continuous_forward_fixed_potential E' v).comp continuous_snd)

theorem continuous_pairStep_fixed_pair (E E' : ℝ) (z : ProjectivePair) :
    Continuous (fun v => pairStep E E' v z) :=
  (continuous_forward_fixed_direction E z.1).prodMk
    (continuous_forward_fixed_direction E' z.2)

theorem continuous_pairStep_joint (E E' : ℝ) :
    Continuous (fun z : ℝ × ProjectivePair => pairStep E E' z.1 z.2) := by
  have ha : Continuous (fun z : ℝ × ProjectivePair => (z.1, z.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun z : ℝ × ProjectivePair => (z.1, z.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hfirst := (continuous_forwardStep E).comp ha
  have hsecond := (continuous_forwardStep E').comp hb
  have hm := hfirst.prodMk hsecond
  simpa only [Function.comp_def, forwardStep, pairStep] using hm

def pairAverage (law : PotentialLaw) (E E' : ℝ) (f : C(ProjectivePair, ℝ))
    (z : ProjectivePair) : ℝ := ∫ v, f (pairStep E E' v z) ∂law.measure

theorem integrable_pair_test (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (z : ProjectivePair) :
    Integrable (fun v => f (pairStep E E' v z)) law.measure :=
  (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_pairStep_fixed_pair E E' z)).measurable.aestronglyMeasurable
    (ae_of_all _ fun v => f.norm_coe_le_norm (pairStep E E' v z))

theorem continuous_pairAverage (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) : Continuous (pairAverage law E E' f) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro z
    exact (f.continuous.comp (continuous_pairStep_fixed_pair E E' z)).measurable.aestronglyMeasurable
  · intro z
    exact ae_of_all _ fun v => f.norm_coe_le_norm (pairStep E E' v z)
  · exact integrable_const ‖f‖
  · exact ae_of_all _ fun v => f.continuous.comp (continuous_pairStep_fixed_potential E E' v)

/-- Linearity is asserted on the compact continuous-function space. -/
def pairKernel (law : PotentialLaw) (E E' : ℝ) : Module.End ℝ C(ProjectivePair, ℝ) where
  toFun f := ⟨pairAverage law E E' f, continuous_pairAverage law E E' f⟩
  map_add' f g := by
    ext z
    change (∫ v, f (pairStep E E' v z) + g (pairStep E E' v z) ∂law.measure) = _
    exact integral_add (integrable_pair_test law E E' f z) (integrable_pair_test law E E' g z)
  map_smul' c f := by
    ext z
    change (∫ v, c * f (pairStep E E' v z) ∂law.measure) =
      c * (∫ v, f (pairStep E E' v z) ∂law.measure)
    exact integral_const_mul c _

@[simp] theorem pairKernel_apply (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (z : ProjectivePair) :
    pairKernel law E E' f z = pairAverage law E E' f z := rfl

theorem pairKernel_monotone (law : PotentialLaw) (E E' : ℝ) :
    Monotone (pairKernel law E E') := by
  intro f g hfg z
  exact integral_mono (integrable_pair_test law E E' f z)
    (integrable_pair_test law E E' g z) (fun v => hfg (pairStep E E' v z))

@[simp] theorem pairKernel_one (law : PotentialLaw) (E E' : ℝ) :
    pairKernel law E E' (1 : C(ProjectivePair, ℝ)) = 1 := by
  ext z
  change (∫ _v : ℝ, (1 : ℝ) ∂law.measure) = 1
  simp

theorem pairKernel_norm_le (law : PotentialLaw) (E E' : ℝ) (f : C(ProjectivePair, ℝ)) :
    ‖pairKernel law E E' f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le (pairKernel law E E' f) (norm_nonneg f)).mpr
  intro z
  change ‖∫ v, f (pairStep E E' v z) ∂law.measure‖ ≤ ‖f‖
  have h := norm_integral_le_of_norm_le_const (μ := law.measure)
    (f := fun v => f (pairStep E E' v z))
    (ae_of_all _ fun v => f.norm_coe_le_norm (pairStep E E' v z))
  simpa only [probReal_univ, mul_one] using h

def pairFutureTest (E E' : ℝ) (f : C(ProjectivePair, ℝ))
    (z : ProjectivePair × PotentialSpace) : ℝ := f (pairStep E E' (z.2 0) z.1)

theorem measurable_pairFutureTest (E E' : ℝ) (f : C(ProjectivePair, ℝ)) :
    Measurable (pairFutureTest E E' f) := by
  change Measurable (fun z : ProjectivePair × PotentialSpace =>
    f (pairStep E E' (z.2 0) z.1))
  have ha : Measurable (fun z : ProjectivePair × PotentialSpace => (z.2 0, z.1)) :=
    ((measurable_pi_apply 0).comp measurable_snd).prodMk measurable_fst
  have hs := (continuous_pairStep_joint E E').measurable.comp ha
  have hm := f.continuous.measurable.comp hs
  simpa only [Function.comp_def] using hm

theorem integrable_pairFutureTest (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (η : ProbabilityMeasure ProjectivePair) :
    Integrable (pairFutureTest E E' f) ((η : Measure ProjectivePair).prod (iidMeasure law)) :=
  (integrable_const ‖f‖).mono' (measurable_pairFutureTest E E' f).aestronglyMeasurable
    (ae_of_all _ fun z => f.norm_coe_le_norm (pairStep E E' (z.2 0) z.1))

theorem futureKernel_pairFutureTest (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (z : ProjectivePair) :
    futureKernel law (pairFutureTest E E' f) z = pairKernel law E E' f z := by
  have hm : Measurable (fun v => f (pairStep E E' v z)) := by
    have h := (f.continuous.comp (continuous_pairStep_fixed_pair E E' z)).measurable
    simpa only [Function.comp_def] using h
  have hmap := integral_map (μ := iidMeasure law) (φ := fun ω : PotentialSpace => ω 0)
    (f := fun v : ℝ => f (pairStep E E' v z)) (measurable_site 0).aemeasurable
    hm.aestronglyMeasurable
  change (∫ ω, f (pairStep E E' (ω 0) z) ∂iidMeasure law) = _
  calc
    _ = ∫ v, f (pairStep E E' v z) ∂(iidMeasure law).map (fun ω => ω 0) := hmap.symm
    _ = ∫ v, f (pairStep E E' v z) ∂law.measure := by rw [iidMeasure_site_map]
    _ = _ := rfl

/-- The actual one-step kernel at any natural-past measurable pair state. -/
theorem iidMeasure_condExp_pairKernel (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (n : ℕ) (X : PotentialSpace → ProjectivePair)
    (hX : Measurable[pastMeasurableSpace n] X) :
    (iidMeasure law)[(fun ω => f (pairStep E E' (ω n) (X ω))) | pastMeasurableSpace n] =ᵐ[
      iidMeasure law] (fun ω => pairKernel law E E' f (X ω)) := by
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le n) le_rfl
  let η : ProbabilityMeasure ProjectivePair :=
    ⟨(iidMeasure law).map X, (iidMeasure law).isProbabilityMeasure_map hXm.aemeasurable⟩
  have hk := iidMeasure_condExp_past_futureKernel law n hX
    (measurable_pairFutureTest E E' f) (integrable_pairFutureTest law E E' f η)
  exact hk.trans (ae_of_all _ fun ω => futureKernel_pairFutureTest law E E' f (X ω))

def pairCorrector (law : PotentialLaw) (E E' : ℝ) (L : ℕ)
    (f : C(ProjectivePair, ℝ)) : C(ProjectivePair, ℝ) :=
  ∑ j ∈ Finset.range L, (pairKernel law E E' ^ j) f

theorem pairCorrector_drift_identity (law : PotentialLaw) (E E' : ℝ) (L : ℕ)
    (f : C(ProjectivePair, ℝ)) :
    pairKernel law E E' (pairCorrector law E E' L f) - pairCorrector law E E' L f =
      (pairKernel law E E' ^ L) f - f :=
  Occupation.linear_corrector_drift_identity _ L f

theorem pairCorrector_drift_le (law : PotentialLaw) (E E' : ℝ) (L : ℕ)
    (f : C(ProjectivePair, ℝ)) (q ε : ℝ)
    (hblock : ∀ z, (pairKernel law E E' ^ L) f z ≤ q * f z + ε) (z : ProjectivePair) :
    pairKernel law E E' (pairCorrector law E E' L f) z - pairCorrector law E E' L f z ≤
      -(1 - q) * f z + ε := by
  have h := congrArg (fun g : C(ProjectivePair, ℝ) => g z)
    (pairCorrector_drift_identity law E E' L f)
  change pairKernel law E E' (pairCorrector law E E' L f) z -
    pairCorrector law E E' L f z = (pairKernel law E E' ^ L) f z - f z at h
  rw [h]
  linarith [hblock z]

end FixedCouplingPoisson.Furstenberg
