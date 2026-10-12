import FixedCouplingPoisson.JointKernel
import FixedCouplingPoisson.RealVagueSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Truncation controls compact-test Laplace errors without expected counts. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter
open scoped Topology CompactlySupported

private theorem laplace_neg_difference_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  calc
    Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (a - b)) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-a) * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a - b)]) (Real.exp_pos _).le
    _ ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)) (sub_nonneg.mpr hab)
    _ = b - a := one_mul _

theorem abs_laplace_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact laplace_neg_difference_le_of_le ha hab
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hba))),
      abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact laplace_neg_difference_le_of_le hb hba

/-- A [0,1] observable error bounded by η times a count costs at most
ηR plus the actual upper-tail probability. -/
theorem integral_difference_le_truncated_count {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (F G X : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hX : Measurable X)
    (hFb : ∀ ω, 0 ≤ F ω ∧ F ω ≤ 1) (hGb : ∀ ω, 0 ≤ G ω ∧ G ω ≤ 1)
    {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (herror : ∀ ω, |F ω - G ω| ≤ η * X ω) :
    |(∫ ω, F ω ∂(P : Measure Ω)) - (∫ ω, G ω ∂(P : Measure Ω))| ≤
      η * R + (P : Measure Ω).real {ω | R < X ω} := by
  let B : Set Ω := {ω | R < X ω}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hX
  have hFi : Integrable F (P : Measure Ω) := bounded_block_integrable hF.stronglyMeasurable hFb
  have hGi : Integrable G (P : Measure Ω) := bounded_block_integrable hG.stronglyMeasurable hGb
  have hbi : Integrable (B.indicator (fun _ => (1 : ℝ))) (P : Measure Ω) :=
    (integrable_const _).indicator hB
  have hbound (ω : Ω) : |F ω - G ω| ≤ η * R + B.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      have herr : |F ω - G ω| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hFb ω).1, (hFb ω).2, (hGb ω).1, (hGb ω).2]
      exact herr.trans (by nlinarith)
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact (herror ω).trans (mul_le_mul_of_nonneg_left (le_of_not_gt hω) hη)
  rw [← integral_sub hFi hGi]
  calc
    _ ≤ ∫ ω, |F ω - G ω| ∂(P : Measure Ω) := abs_integral_le_integral_abs
    _ ≤ ∫ ω, η * R + B.indicator (fun _ => (1 : ℝ)) ω ∂(P : Measure Ω) :=
      integral_mono (hFi.sub hGi).abs ((integrable_const _).add hbi) hbound
    _ = _ := by
      rw [integral_add (integrable_const _) hbi, integral_const, integral_indicator_const _ hB]
      simp only [probReal_univ, smul_eq_mul, one_mul, mul_one, B]

end FixedCouplingPoisson
