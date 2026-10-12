import FixedCouplingPoisson.PairKernel
import FixedCouplingPoisson.ProjectiveMetric
import FixedCouplingPoisson.PhaseProcess
import FixedCouplingPoisson.PhaseWeakTools
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The genuine pair kernel is connected to the
common-potential two-energy phase process. Its finite corrector is then
inserted into the proved conditional stopped occupation budget. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators

def phasePairProcess (E E' θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ProjectivePair :=
  (phaseProjective (canonicalPhaseProcess E θ n ω),
    phaseProjective (canonicalPhaseProcess E' φ n ω))

@[simp] theorem phasePairProcess_zero (E E' θ φ : ℝ) (ω : PotentialSpace) :
    phasePairProcess E E' θ φ 0 ω = (phaseProjective θ, phaseProjective φ) := rfl

theorem phasePairProcess_succ (E E' θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    phasePairProcess E E' θ φ (n + 1) ω =
      pairStep E E' (ω n) (phasePairProcess E E' θ φ n ω) := by
  simp only [phasePairProcess, canonicalPhaseProcess_succ,
    phaseProjective_canonicalPhase, pairStep]

theorem phasePairProcess_past_measurable (E E' θ φ : ℝ) (n : ℕ) :
    Measurable[pastMeasurableSpace n] (phasePairProcess E E' θ φ n) := by
  change Measurable[pastMeasurableSpace n] (fun ω : PotentialSpace =>
    (phaseProjective (canonicalPhaseProcess E θ n ω),
      phaseProjective (canonicalPhaseProcess E' φ n ω)))
  have hfirst := continuous_phaseProjective.measurable.comp
    (canonicalPhaseProcess_past_measurable E θ n)
  have hsecond := continuous_phaseProjective.measurable.comp
    (canonicalPhaseProcess_past_measurable E' φ n)
  have hm := hfirst.prodMk hsecond
  simpa only [Function.comp_def] using hm

theorem phasePairProcess_measurable (E E' θ φ : ℝ) (n : ℕ) :
    Measurable (phasePairProcess E E' θ φ n) :=
  (phasePairProcess_past_measurable E E' θ φ n).mono (pastMeasurableSpace_le n) le_rfl

theorem integrable_phasePairProcess_test (law : PotentialLaw) (E E' θ φ : ℝ)
    (f : C(ProjectivePair, ℝ)) (n : ℕ) :
    Integrable (fun ω => f (phasePairProcess E E' θ φ n ω)) (iidMeasure law) := by
  have hm := f.continuous.measurable.comp (phasePairProcess_measurable E E' θ φ n)
  apply (integrable_const ‖f‖).mono'
  · simpa only [Function.comp_def] using hm.aestronglyMeasurable
  · exact ae_of_all _ fun ω => f.norm_coe_le_norm (phasePairProcess E E' θ φ n ω)

theorem condExp_phasePairProcess_test (law : PotentialLaw) (E E' θ φ : ℝ)
    (f : C(ProjectivePair, ℝ)) (n : ℕ) :
    (iidMeasure law)[(fun ω => f (phasePairProcess E E' θ φ (n + 1) ω)) |
      pastMeasurableSpace n] =ᵐ[iidMeasure law]
        (fun ω => pairKernel law E E' f (phasePairProcess E E' θ φ n ω)) := by
  simpa only [phasePairProcess_succ] using
    iidMeasure_condExp_pairKernel law E E' f n (phasePairProcess E E' θ φ n)
      (phasePairProcess_past_measurable E E' θ φ n)

/-- The iterated operator is the expectation under the actual shared iid
path; no independent-pair model is substituted. -/
theorem integral_phasePairProcess_test (law : PotentialLaw) (E E' θ φ : ℝ)
    (f : C(ProjectivePair, ℝ)) (n : ℕ) :
    (∫ ω, f (phasePairProcess E E' θ φ n ω) ∂iidMeasure law) =
      (pairKernel law E E' ^ n) f (phaseProjective θ, phaseProjective φ) := by
  induction n generalizing f with
  | zero => simp only [phasePairProcess_zero, integral_const, probReal_univ,
      one_smul, pow_zero, Module.End.one_apply]
  | succ n ih =>
    have h := integral_congr_ae (condExp_phasePairProcess_test law E E' θ φ f n)
    rw [integral_condExp (pastMeasurableSpace_le n)] at h
    rw [h, ih, pow_succ]
    rfl

theorem pairKernel_pow_nonneg (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (hf : 0 ≤ f) (n : ℕ) :
    0 ≤ (pairKernel law E E' ^ n) f := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hf
  | succ n ih =>
    rw [pow_succ']
    change 0 ≤ pairKernel law E E' ((pairKernel law E E' ^ n) f)
    simpa only [map_zero] using pairKernel_monotone law E E' ih

theorem pairKernel_pow_le_one (law : PotentialLaw) (E E' : ℝ)
    (f : C(ProjectivePair, ℝ)) (hf : f ≤ 1) (n : ℕ) :
    (pairKernel law E E' ^ n) f ≤ 1 := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hf
  | succ n ih =>
    rw [pow_succ']
    change pairKernel law E E' ((pairKernel law E E' ^ n) f) ≤ 1
    simpa only [pairKernel_one] using pairKernel_monotone law E E' ih

theorem pairCorrector_nonneg (law : PotentialLaw) (E E' : ℝ) (L : ℕ)
    (f : C(ProjectivePair, ℝ)) (hf : 0 ≤ f) : 0 ≤ pairCorrector law E E' L f :=
  Finset.sum_nonneg fun j _ => pairKernel_pow_nonneg law E E' f hf j

theorem pairCorrector_le_length (law : PotentialLaw) (E E' : ℝ) (L : ℕ)
    (f : C(ProjectivePair, ℝ)) (hf : f ≤ 1) (z : ProjectivePair) :
    pairCorrector law E E' L f z ≤ (L : ℝ) := by
  calc
    _ = ∑ j ∈ Finset.range L, (pairKernel law E E' ^ j) f z := by simp [pairCorrector]
    _ ≤ ∑ _j ∈ Finset.range L, (1 : ℝ) :=
      Finset.sum_le_sum fun j _ => pairKernel_pow_le_one law E E' f hf j z
    _ = _ := by simp

theorem integrable_phasePairProcess_stopped_test (law : PotentialLaw) (E E' θ φ : ℝ)
    (f : C(ProjectivePair, ℝ)) (τ : PotentialSpace → ℕ) (hτ : Measurable τ) :
    Integrable (fun ω => f (phasePairProcess E E' θ φ (τ ω) ω)) (iidMeasure law) := by
  have hprocess : Measurable (fun p : ℕ × PotentialSpace =>
      phasePairProcess E E' θ φ p.1 p.2) :=
    measurable_from_prod_countable_right (fun n => phasePairProcess_measurable E E' θ φ n)
  have hstate := hprocess.comp (hτ.prodMk measurable_id)
  have hm := f.continuous.measurable.comp hstate
  apply (integrable_const ‖f‖).mono'
  · simpa only [Function.comp_def, id_eq] using hm.aestronglyMeasurable
  · exact ae_of_all _ fun ω =>
      f.norm_coe_le_norm (phasePairProcess E E' θ φ (τ ω) ω)

/-- Actual pair-process occupation, conditional only on a displayed block
inequality which will be instantiated by the proved matrix contraction. -/
theorem phasePairProcess_bounded_occupation (law : PotentialLaw) (E E' θ φ : ℝ)
    (f : C(ProjectivePair, ℝ)) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (L : ℕ) (q ε : ℝ)
    (hblock : ∀ z, (pairKernel law E E' ^ L) f z ≤ q * f z + ε)
    (τ : PotentialSpace → ℕ) (hτm : Measurable τ) (N : ℕ)
    (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet[pastMeasurableSpace j] {ω | j < τ ω}) :
    (1 - q) * (∫ ω, ∑ j ∈ Finset.range (τ ω), f (phasePairProcess E E' θ φ j ω)
        ∂iidMeasure law) ≤ (L : ℝ) + ε * (∫ ω, (τ ω : ℝ) ∂iidMeasure law) := by
  let V := pairCorrector law E E' L f
  have hbudget := Occupation.bounded_stopped_occupation_of_conditional_drift_nonneg
    pastMeasurableSpace pastMeasurableSpace_le τ N hτ hA
    (fun j ω => V (phasePairProcess E E' θ φ j ω))
    (fun j ω => f (phasePairProcess E E' θ φ j ω))
    (integrable_phasePairProcess_test law E E' θ φ V)
    (integrable_phasePairProcess_test law E E' θ φ f)
    (integrable_phasePairProcess_stopped_test law E E' θ φ V τ hτm)
    (ae_of_all _ fun ω => pairCorrector_nonneg law E E' L f hf0
      (phasePairProcess E E' θ φ (τ ω) ω))
    (1 - q) ε (fun j _ => ?_)
  · have hinit : (∫ ω, V (phasePairProcess E E' θ φ 0 ω) ∂iidMeasure law) ≤ (L : ℝ) := by
      simpa only [phasePairProcess_zero, integral_const, probReal_univ, one_smul] using
        pairCorrector_le_length law E E' L f hf1 (phaseProjective θ, phaseProjective φ)
    linarith
  · filter_upwards [condExp_phasePairProcess_test law E E' θ φ V j] with ω hω
    rw [hω]
    exact pairCorrector_drift_le law E E' L f q ε hblock _

def pairDistancePower (s : ℝ) (hs : 0 ≤ s) : C(ProjectivePair, ℝ) where
  toFun z := projectiveDistance z.1 z.2 ^ s
  continuous_toFun := by
    have hm := (Real.continuous_rpow_const hs).comp continuous_projectiveDistance_joint
    simpa only [Function.comp_def] using hm

theorem pairDistancePower_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ pairDistancePower s hs := by
  intro z
  apply Real.rpow_nonneg
  unfold projectiveDistance determinantDistance
  exact div_nonneg (abs_nonneg _)
    (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))

theorem pairDistancePower_le_one (s : ℝ) (hs : 0 ≤ s) : pairDistancePower s hs ≤ 1 := by
  intro z
  apply Real.rpow_le_one _ (projectiveDistance_le_one z.1 z.2) hs
  unfold projectiveDistance determinantDistance
  exact div_nonneg (abs_nonneg _)
    (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))

end FixedCouplingPoisson.Furstenberg
