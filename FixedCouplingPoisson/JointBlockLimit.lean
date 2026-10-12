import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# Two-stage block error limits

The block number is chosen after an accuracy tolerance and is then held
fixed while the model size tends to infinity. No uniform remainder bound
in the block number, and no interchange of these two limits, is assumed.
These are analytic lemmas; actual model error estimates must be proved
separately before applying them.
-/
noncomputable section
namespace FixedCouplingPoisson
open Filter
open scoped Topology

/-- The standard exponential approximation, including arbitrary initial
values of the sequence where the denominator may vanish. -/
theorem tendsto_one_sub_div_pow_exp_neg (Λ : ℝ) :
    Tendsto (fun m : ℕ => (1 - Λ / (m : ℝ)) ^ m) atTop (𝓝 (Real.exp (-Λ))) := by
  simpa only [neg_div, sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-Λ)

/-- An eventual family of vanishing remainders suffices for a two-stage
approximation. Each remainder is used at one fixed outer index only. -/
theorem tendsto_of_twoStage_error_budget
    (f a e : ℕ → ℝ) (A : ℝ)
    (ha : Tendsto a atTop (𝓝 A)) (he : Tendsto e atTop (𝓝 0))
    (hbudget : ∀ᶠ m : ℕ in atTop, ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, |f n - a m| ≤ e m + r n) :
    Tendsto f atTop (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  have haε : ∀ᶠ m in atTop, |a m - A| < ε / 3 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp ha (ε / 3) hthird
  have heε : ∀ᶠ m in atTop, e m < ε / 3 :=
    (tendsto_order.mp he).2 (ε / 3) hthird
  obtain ⟨m, hm, hma, hme⟩ := (hbudget.and (haε.and heε)).exists
  obtain ⟨r, hr, hbound⟩ := hm
  have hrε : ∀ᶠ n in atTop, r n < ε / 3 :=
    (tendsto_order.mp hr).2 (ε / 3) hthird
  filter_upwards [hbound, hrε] with n hn hrn
  rw [Real.dist_eq]
  calc
    |f n - A| ≤ |f n - a m| + |a m - A| := abs_sub_le _ _ _
    _ ≤ e m + r n + |a m - A| := add_le_add hn le_rfl
    _ < ε := by linarith

theorem tendsto_of_twoStage_reciprocal_error_budget
    (f a : ℕ → ℝ) (A C : ℝ) (ha : Tendsto a atTop (𝓝 A))
    (hbudget : ∀ᶠ m : ℕ in atTop, ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, |f n - a m| ≤ C / (m : ℝ) + r n) :
    Tendsto f atTop (𝓝 A) :=
  tendsto_of_twoStage_error_budget f a (fun m => C / (m : ℝ)) A ha
    (tendsto_const_div_atTop_nhds_zero_nat C) hbudget

/-- The analytic last step for a block Laplace proof. This statement does
not assert that any phase process satisfies its explicit error hypothesis. -/
theorem jointBlockLimit_of_twoStage_bound (f : ℕ → ℝ) (Λ C : ℝ)
    (hbudget : ∀ᶠ m : ℕ in atTop, ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 0) ∧
        ∀ᶠ n in atTop,
          |f n - (1 - Λ / (m : ℝ)) ^ m| ≤ C / (m : ℝ) + r n) :
    Tendsto f atTop (𝓝 (Real.exp (-Λ))) :=
  tendsto_of_twoStage_reciprocal_error_budget f
    (fun m => (1 - Λ / (m : ℝ)) ^ m) (Real.exp (-Λ)) C
    (tendsto_one_sub_div_pow_exp_neg Λ) hbudget

end FixedCouplingPoisson
