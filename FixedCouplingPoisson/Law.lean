import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith

/-! The actual bounded, nonconstant single-site laws and iid-model hypotheses.
No spectral or probabilistic conclusion is placed in these hypotheses. -/
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set

structure PotentialLaw where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ v ∂measure, |v| ≤ M
  nonconstant : ∀ a : ℝ, measure ≠ Measure.dirac a

attribute [instance] PotentialLaw.probability

/-- The iid assumption uses actual joint independence and identical pushforward laws. -/
structure IIDPotential {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (law : PotentialLaw) where
  potential : ℕ → Ω → ℝ
  measurable : ∀ j, Measurable (potential j)
  independent : iIndepFun potential P
  identical : ∀ j, P.map (potential j) = law.measure

/-- A nondegenerate fixed-coupling Bernoulli law on the actual values `a,b`. -/
noncomputable def bernoulliLaw (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : PotentialLaw where
  measure := bernoulliMeasure a b p
  probability := inferInstance
  bounded := by
    refine ⟨max |a| |b|, le_trans (abs_nonneg a) (le_max_left _ _), ?_⟩
    have hs : ∀ᵐ v ∂bernoulliMeasure a b p, v ∈ ({a, b} : Set ℝ) := by
      rw [ae_iff]
      apply bernoulliMeasure_apply_of_notMem_of_notMem p
      · exact ((measurableSet_singleton b).insert a).compl
      · simp
      · simp
    filter_upwards [hs] with v hv
    simp only [mem_insert_iff, mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  nonconstant := by
    intro c h
    by_cases hc : c = a
    · subst c
      have heq := congrArg (fun μ : Measure ℝ => μ.real {b}) h
      have hm : (bernoulliMeasure a b p).real {b} = 1 - p :=
        bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton b)
          (by simpa using hab.ne) (by simp)
      rw [hm] at heq
      have hd : (Measure.dirac a).real {b} = 0 := by simp [measureReal_def, hab.ne]
      rw [hd] at heq
      linarith
    · have heq := congrArg (fun μ : Measure ℝ => μ.real {a}) h
      have hm : (bernoulliMeasure a b p).real {a} = p :=
        bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton a)
          (by simp) (by simpa using hab.ne.symm)
      rw [hm] at heq
      have hd : (Measure.dirac c).real {a} = 0 := by simp [measureReal_def, hc]
      rw [hd] at heq
      linarith

@[simp] theorem bernoulliLaw_measure (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (bernoulliLaw a b hab p hp0 hp1).measure = bernoulliMeasure a b p := rfl

/-- Atom masses are retained; no density assumption is hidden in the model. -/
theorem bernoulliLaw_mass_left (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (bernoulliLaw a b hab p hp0 hp1).measure.real {a} = p := by
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton a)
    (by simp) (by simpa using hab.ne.symm)

end FixedCouplingPoisson
