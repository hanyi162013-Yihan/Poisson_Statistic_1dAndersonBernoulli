import FixedCouplingPoisson.AngleProjective
import FixedCouplingPoisson.ProductCocycle
import FixedCouplingPoisson.PhaseProcess
import FixedCouplingPoisson.PhaseWeakTools
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Actual canonical phase distributions modulo π

The wrapped phase is the actual canonical process. Its law is the pullback
of the actual projective-product law under the angle/projective homeomorphism.
Weak limits and the absence of atoms therefore transfer without adding a
stationarity or convergence field to the qualitative external interface.

-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Filter
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The actual real canonical phase, reduced only by the quotient modulo π. -/
def canonicalPhaseCircleProcess (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) : AddCircle Real.pi :=
  (canonicalPhaseProcess E θ n ω : AddCircle Real.pi)

theorem measurable_canonicalPhaseCircleProcess (E θ : ℝ) (n : ℕ) :
    Measurable (canonicalPhaseCircleProcess E θ n) :=
  (AddCircle.continuous_mk' Real.pi).measurable.comp (canonicalPhaseProcess_measurable E θ n)

/-- The actual iid probability distribution of the wrapped canonical phase. -/
def phaseProcessDistribution (law : PotentialLaw) (E θ : ℝ) (n : ℕ) :
    ProbabilityMeasure (AddCircle Real.pi) :=
  ⟨(iidMeasure law).map (canonicalPhaseCircleProcess E θ n),
    Measure.isProbabilityMeasure_map (measurable_canonicalPhaseCircleProcess E θ n).aemeasurable⟩

theorem phaseProjective_canonicalPhase_map (E v θ : ℝ) :
    phaseProjective (canonicalPhase E v θ) = transferProjective E v (phaseProjective θ) :=
  canonicalPhase_projective E v θ

/-- The actual canonical angle and actual product-induced projective process coincide. -/
theorem phaseProjective_canonicalPhaseProcess (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    phaseProjective (canonicalPhaseProcess E θ n ω) =
      projectiveProcess E (phaseProjective θ) n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [canonicalPhaseProcess_succ, projectiveProcess_succ,
      phaseProjective_canonicalPhase_map, ih]

/-- A genuine projective probability measure transported to angles modulo π. -/
def pullbackPhaseDistribution (ν : ProbabilityMeasure ProjectivePoint) :
    ProbabilityMeasure (AddCircle Real.pi) :=
  ν.map angleProjectiveHomeomorph.symm.continuous.measurable.aemeasurable

/-- No alternate random phase is substituted: this is the law of the actual lift. -/
theorem phaseProcessDistribution_eq_pullback (law : PotentialLaw) (E θ : ℝ) (n : ℕ) :
    phaseProcessDistribution law E θ n =
      pullbackPhaseDistribution (projectiveProcessDistribution law E (phaseProjective θ) n) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidMeasure law).map (canonicalPhaseCircleProcess E θ n) =
    ((iidMeasure law).map (projectiveProcess E (phaseProjective θ) n)).map
      angleProjectiveHomeomorph.symm
  rw [Measure.map_map angleProjectiveHomeomorph.symm.continuous.measurable
    (projectiveProcess_measurable E (phaseProjective θ) n)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun ω => by
    apply angleProjectiveHomeomorph.injective
    simpa only [Function.comp_apply, canonicalPhaseCircleProcess,
      angleProjectiveHomeomorph_coe, Homeomorph.apply_symm_apply] using
      phaseProjective_canonicalPhaseProcess E θ n ω

/-- The absence of projective atoms is preserved by the actual angle homeomorphism. -/
theorem pullbackPhaseDistribution_null_singletons (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ p, (ν : Measure ProjectivePoint) {p} = 0) (x : AddCircle Real.pi) :
    (pullbackPhaseDistribution ν : Measure (AddCircle Real.pi)) {x} = 0 := by
  change ((ν : Measure ProjectivePoint).map angleProjectiveHomeomorph.symm) {x} = 0
  rw [Measure.map_apply angleProjectiveHomeomorph.symm.continuous.measurable
    (measurableSet_singleton x)]
  have hpre : angleProjectiveHomeomorph.symm ⁻¹' {x} = {angleProjectiveHomeomorph x} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact angleProjectiveHomeomorph.symm_apply_eq
  rw [hpre]
  exact hν _

/-- Weak convergence of the actual projective laws transfers to the actual wrapped phases. -/
theorem phaseProcessDistribution_tendsto_of_projective (law : PotentialLaw) (E θ : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint)
    (h : Tendsto (projectiveProcessDistribution law E (phaseProjective θ)) atTop (𝓝 ν)) :
    Tendsto (phaseProcessDistribution law E θ) atTop (𝓝 (pullbackPhaseDistribution ν)) := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (projectiveProcessDistribution law E (phaseProjective θ)) ν h
    angleProjectiveHomeomorph.symm.continuous
  have heq : phaseProcessDistribution law E θ =
      (fun n => pullbackPhaseDistribution
        (projectiveProcessDistribution law E (phaseProjective θ) n)) := by
    funext n
    exact phaseProcessDistribution_eq_pullback law E θ n
  rw [heq]
  exact hm

end FixedCouplingPoisson.Furstenberg
