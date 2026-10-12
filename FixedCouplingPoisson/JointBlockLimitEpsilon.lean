import FixedCouplingPoisson.JointBlockLimit

/-! The two-stage limit in the direct epsilon form used by actual blocks. -/
noncomputable section
namespace FixedCouplingPoisson
open Filter
open scoped Topology

theorem tendsto_of_twoStage_eventual_error
    (f a e : ℕ → ℝ) (A : ℝ)
    (ha : Tendsto a atTop (𝓝 A)) (he : Tendsto e atTop (𝓝 0))
    (hbudget : ∀ᶠ m : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, |f n - a m| ≤ e m + ε) :
    Tendsto f atTop (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  have haε : ∀ᶠ m in atTop, |a m - A| < ε / 3 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp ha (ε / 3) hthird
  have heε : ∀ᶠ m in atTop, e m < ε / 3 :=
    (tendsto_order.mp he).2 (ε / 3) hthird
  obtain ⟨m, hm, hma, hme⟩ := (hbudget.and (haε.and heε)).exists
  filter_upwards [hm (ε / 3) hthird] with n hn
  rw [Real.dist_eq]
  calc
    |f n - A| ≤ |f n - a m| + |a m - A| := abs_sub_le _ _ _
    _ ≤ e m + ε / 3 + |a m - A| := add_le_add hn le_rfl
    _ < ε := by linarith

theorem jointBlockLimit_of_twoStage_eventual_bound (f : ℕ → ℝ) (Λ C : ℝ)
    (hbudget : ∀ᶠ m : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        |f n - (1 - Λ / (m : ℝ)) ^ m| ≤ C / (m : ℝ) + ε) :
    Tendsto f atTop (𝓝 (Real.exp (-Λ))) :=
  tendsto_of_twoStage_eventual_error f
    (fun m => (1 - Λ / (m : ℝ)) ^ m) (fun m => C / (m : ℝ)) (Real.exp (-Λ))
    (tendsto_one_sub_div_pow_exp_neg Λ) (tendsto_const_div_atTop_nhds_zero_nat C) hbudget

end FixedCouplingPoisson
