import FixedCouplingPoisson.RealVagueSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

/-! Genuine nonnegative compact-test Laplace coordinates on the real vague space. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Topology
open scoped Topology CompactlySupported BoundedContinuousFunction

theorem testIntegral_add (μ : RealVagueMeasure) (f g : C_c(ℝ, ℝ)) :
    testIntegral μ (f + g) = testIntegral μ f + testIntegral μ g :=
  integral_add' f.integrable g.integrable

theorem testIntegral_sub (μ : RealVagueMeasure) (f g : C_c(ℝ, ℝ)) :
    testIntegral μ (f - g) = testIntegral μ f - testIntegral μ g :=
  integral_sub' f.integrable g.integrable

/-- Nonnegative compactly supported tests already separate actual measures. -/
theorem ext_of_nonneg_testIntegral {μ ν : RealVagueMeasure}
    (h : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → testIntegral μ f = testIntegral ν f) : μ = ν := by
  apply ext_of_testIntegral
  intro f
  have hdecomp : f = (f ⊔ 0) - ((-f) ⊔ 0) := by
    ext x
    simp only [CompactlySupportedContinuousMap.sub_apply,
      CompactlySupportedContinuousMap.sup_apply,
      CompactlySupportedContinuousMap.zero_apply,
      CompactlySupportedContinuousMap.neg_apply]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      simp
    · have hx' : f x ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
      simp
  calc
    testIntegral μ f = testIntegral μ ((f ⊔ 0) - ((-f) ⊔ 0)) :=
      congrArg (testIntegral μ) hdecomp
    _ = testIntegral μ (f ⊔ 0) - testIntegral μ ((-f) ⊔ 0) :=
      testIntegral_sub μ _ _
    _ = testIntegral ν (f ⊔ 0) - testIntegral ν ((-f) ⊔ 0) := by
      rw [h (f ⊔ 0) le_sup_right, h ((-f) ⊔ 0) le_sup_right]
    _ = testIntegral ν ((f ⊔ 0) - ((-f) ⊔ 0)) := (testIntegral_sub ν _ _).symm
    _ = testIntegral ν f := (congrArg (testIntegral ν) hdecomp).symm

/-- A genuine Laplace coordinate, before imposing nonnegativity on the test. -/
def laplaceTest (f : C_c(ℝ, ℝ)) (μ : RealVagueMeasure) : ℝ :=
  Real.exp (-testIntegral μ f)

theorem continuous_laplaceTest (f : C_c(ℝ, ℝ)) : Continuous (laplaceTest f) :=
  Real.continuous_exp.comp (continuous_testIntegral f).neg

theorem laplaceTest_mem_Icc (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) (μ : RealVagueMeasure) :
    laplaceTest f μ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (testIntegral_nonneg μ f (fun x => hf x)))⟩

/-- The real bounded continuous test needed for laws of random measures. -/
def laplaceBoundedTest (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) : RealVagueMeasure →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨laplaceTest f, continuous_laplaceTest f⟩ 1 (by
    intro μ ν
    have hμ := laplaceTest_mem_Icc f hf μ
    have hν := laplaceTest_mem_Icc f hf ν
    change dist (laplaceTest f μ) (laplaceTest f ν) ≤ 1
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hμ.1, hμ.2, hν.1, hν.2])

@[simp] theorem laplaceBoundedTest_apply (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f)
    (μ : RealVagueMeasure) : laplaceBoundedTest f hf μ = laplaceTest f μ := rfl

theorem norm_laplaceBoundedTest_le (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) :
    ‖laplaceBoundedTest f hf‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro μ
  rw [laplaceBoundedTest_apply, Real.norm_eq_abs,
    abs_of_nonneg (laplaceTest_mem_Icc f hf μ).1]
  exact (laplaceTest_mem_Icc f hf μ).2

@[simp] theorem laplaceTest_zero (μ : RealVagueMeasure) : laplaceTest 0 μ = 1 := by
  simp [laplaceTest, testIntegral]

theorem laplaceTest_add (f g : C_c(ℝ, ℝ)) (μ : RealVagueMeasure) :
    laplaceTest (f + g) μ = laplaceTest f μ * laplaceTest g μ := by
  simp only [laplaceTest, testIntegral_add, neg_add, Real.exp_add]

/-- Equal nonnegative Laplace coordinates force equality of actual locally finite measures. -/
theorem ext_of_nonneg_laplaceTest {μ ν : RealVagueMeasure}
    (h : ∀ f : C_c(ℝ, ℝ), 0 ≤ f → laplaceTest f μ = laplaceTest f ν) : μ = ν := by
  apply ext_of_nonneg_testIntegral
  intro f hf
  exact neg_injective (Real.exp_injective (h f hf))

/-- Explicit point separation for compact-set approximation and law identification. -/
theorem exists_nonneg_laplaceTest_ne {μ ν : RealVagueMeasure} (hμν : μ ≠ ν) :
    ∃ f : C_c(ℝ, ℝ), 0 ≤ f ∧ laplaceTest f μ ≠ laplaceTest f ν := by
  classical
  by_contra h
  apply hμν
  apply ext_of_nonneg_laplaceTest
  intro f hf
  by_contra hne
  exact h ⟨f, hf, hne⟩

end FixedCouplingPoisson.RealVagueMeasure
