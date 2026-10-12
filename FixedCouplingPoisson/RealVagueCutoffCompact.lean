import FixedCouplingPoisson.RealVagueCompact

/-! Actual cutoff-integral bounds yield compact vague sets. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Topology Set
open scoped Topology CompactlySupported

/-- Pointwise domination bounds the actual compact-test integral. -/
theorem abs_testIntegral_le_mul_testIntegral (μ : RealVagueMeasure)
    (f χ : C_c(ℝ, ℝ)) (C : ℝ) (hdom : ∀ x, |f x| ≤ C * χ x) :
    |testIntegral μ f| ≤ C * testIntegral μ χ := by
  change |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * ∫ x, χ x ∂(μ : Measure ℝ)
  calc
    _ ≤ ∫ x, |f x| ∂(μ : Measure ℝ) := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * χ x ∂(μ : Measure ℝ) :=
      integral_mono f.integrable.abs (χ.integrable.const_mul C) hdom
    _ = _ := integral_const_mul C _

/-- The closed constraints use continuous cutoff integrals. -/
def cutoffBox (χ : ℕ → C_c(ℝ, ℝ)) (M : ℕ → ℝ) : Set RealVagueMeasure :=
  {μ | ∀ r, testIntegral μ (χ r) ≤ M r}

theorem isClosed_cutoffBox (χ : ℕ → C_c(ℝ, ℝ)) (M : ℕ → ℝ) :
    IsClosed (cutoffBox χ M) := by
  simp only [cutoffBox, Set.ofPred_forall]
  exact isClosed_iInter fun r => isClosed_le (continuous_testIntegral (χ r)) continuous_const

/-- Every compact test may use its own cutoff and a nonnegative finite constant.
The concrete cutoff construction is supplied by the application; compactness
follows from the proved RMK coordinate boxes. -/
theorem isCompact_cutoffBox_of_domination (χ : ℕ → C_c(ℝ, ℝ))
    (hdom : ∀ f : C_c(ℝ, ℝ), ∃ r : ℕ, ∃ C : ℝ,
      0 ≤ C ∧ ∀ x, |f x| ≤ C * χ r x) (M : ℕ → ℝ) :
    IsCompact (cutoffBox χ M) := by
  classical
  choose r C hC hbound using hdom
  let B : C_c(ℝ, ℝ) → ℝ := fun f => C f * M (r f)
  apply (isCompact_abs_coordinateBox B).of_isClosed_subset (isClosed_cutoffBox χ M)
  intro μ hμ f
  exact (abs_testIntegral_le_mul_testIntegral μ f (χ (r f)) (C f) (hbound f)).trans
    (mul_le_mul_of_nonneg_left (hμ (r f)) (hC f))

end FixedCouplingPoisson.RealVagueMeasure
