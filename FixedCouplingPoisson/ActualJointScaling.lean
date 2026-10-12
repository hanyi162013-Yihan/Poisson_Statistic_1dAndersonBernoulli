import FixedCouplingPoisson.ActualColoredKernelUniform
import FixedCouplingPoisson.EqualBlockTimeScales

/-! Arithmetic and deterministic scale facts for actual colored blocks. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal

theorem coloredQuadraticBudget_nonneg (s : ℕ) (w : Fin s → ℝ) (W : ℝ) :
    0 ≤ coloredQuadraticBudget s w W := by
  unfold coloredQuadraticBudget
  positivity

theorem coloredQuadraticBudget_div (s : ℕ) (w : Fin s → ℝ) (W : ℝ)
    {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * coloredQuadraticBudget s (fun i => w i / (m : ℝ)) (W / (m : ℝ)) =
      coloredQuadraticBudget s w W / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  unfold coloredQuadraticBudget
  simp_rw [div_pow]
  rw [mul_add, Finset.mul_sum, add_div, Finset.sum_div]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro i hi
    field_simp

theorem coloredArrivalWeight_div (s : ℕ) (t w : Fin s → ℝ) (m : ℕ) :
    (∑ i, firstArrivalWeight (t i) * (w i / (m : ℝ))) =
      (∑ i, firstArrivalWeight (t i) * w i) / (m : ℝ) := by
  simp only [mul_div_assoc, Finset.sum_div]

theorem idsCluster_mass_tendsto_zero (law : PotentialLaw) (e : ℕ → ℕ → ℝ)
    (a b : ℕ) (E₀ : ℝ)
    (ha : Tendsto (fun n => e n a) atTop (𝓝 E₀))
    (hb : Tendsto (fun n => e n b) atTop (𝓝 E₀)) :
    Tendsto (fun n => idsCandidate law (e n b) - idsCandidate law (e n a))
      atTop (𝓝 0) := by
  simpa only [Function.comp_apply, sub_self] using
    ((continuous_idsCandidate law).tendsto E₀ |>.comp hb).sub
      ((continuous_idsCandidate law).tendsto E₀ |>.comp ha)

theorem finite_good_complement_budget_tendsto_zero {Ω β : Type*}
    [MeasurableSpace Ω] [Fintype β] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℕ → β → Set Ω) (hG : ∀ n b, MeasurableSet (G n b))
    (hprob : ∀ b, Tendsto (fun n => μ (G n b)) atTop (𝓝 1)) :
    Tendsto (fun n => 2 * ∑ b, μ.real (G n b)ᶜ) atTop (𝓝 0) := by
  have hbad (b : β) : Tendsto (fun n => μ.real (G n b)ᶜ) atTop (𝓝 0) := by
    have hr : Tendsto (fun n => μ.real (G n b)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_one] using
        (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (hprob b)
    simpa only [measureReal_compl (hG _ b), probReal_univ, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  simpa using (tendsto_finsetSum Finset.univ (fun b _ => hbad b)).const_mul 2

theorem coloredLinearFactor_bounds_eventually (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 0 ≤ 1 - Λ / (m : ℝ) ∧
      1 - Λ / (m : ℝ) ≤ 1 := by
  have htop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ m : ℕ in atTop, Λ < (m : ℝ) := htop.eventually (eventually_gt_atTop Λ)
  filter_upwards [hlarge, eventually_gt_atTop 0] with m hm hm0
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm0
  exact ⟨hm0, sub_nonneg.mpr ((div_le_one hmR).mpr hm.le),
    sub_le_self _ (div_nonneg hΛ hmR.le)⟩

end FixedCouplingPoisson.Furstenberg
