import FixedCouplingPoisson.CanonicalResidual
import FixedCouplingPoisson.Rounding

/-! Exact enclosing-window domination for actual phase-count increments.
The only small-start condition is the sum of the actual oriented residuals.
No independence or probabilistic count estimate occurs in this module. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open scoped BigOperators

theorem terminalWindow_enclosing_carry (θ : ℕ → ℝ) (s : ℕ) :
    ⌊(θ 0 - θ s) / Real.pi⌋ -
      ∑ i ∈ Finset.range s, terminalWindowWinding θ i =
        ⌊(∑ i ∈ Finset.range s, terminalWindowResidual θ i) / Real.pi⌋ := by
  have hsum : (∑ i ∈ Finset.range s,
      (Real.pi * (terminalWindowWinding θ i : ℝ) + terminalWindowResidual θ i)) =
        θ 0 - θ s := by
    calc
      _ = ∑ i ∈ Finset.range s, (θ i - θ (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := terminalWindow_decomposition θ i
        linarith
      _ = _ := Finset.sum_range_sub' θ s
  simpa only [hsum] using floor_scaled_sum_winding_residual (Finset.range s)
    (terminalWindowWinding θ) (terminalWindowResidual θ) Real.pi_ne_zero

theorem terminalWindow_enclosing_carry_nonneg (θ : ℕ → ℝ) (s : ℕ) :
    0 ≤ ⌊(θ 0 - θ s) / Real.pi⌋ -
      ∑ i ∈ Finset.range s, terminalWindowWinding θ i := by
  rw [terminalWindow_enclosing_carry]
  exact floor_scaled_sum_residual_nonneg (Finset.range s) (terminalWindowResidual θ)
    Real.pi_pos (fun i _ => (terminalWindowResidual_mem θ i).1)

theorem terminalWindow_enclosing_eq_sum_of_small_residual (θ : ℕ → ℝ) (s : ℕ)
    (hsmall : (∑ i ∈ Finset.range s, terminalWindowResidual θ i) < Real.pi) :
    ⌊(θ 0 - θ s) / Real.pi⌋ =
      ∑ i ∈ Finset.range s, terminalWindowWinding θ i := by
  have hzero : ⌊(∑ i ∈ Finset.range s, terminalWindowResidual θ i) / Real.pi⌋ = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    exact ⟨div_nonneg (Finset.sum_nonneg fun i _ =>
      (terminalWindowResidual_mem θ i).1) Real.pi_pos.le,
      (div_lt_one Real.pi_pos).mpr hsmall⟩
  have h := terminalWindow_enclosing_carry θ s
  rw [hzero] at h
  omega

theorem terminalWindow_increment_domination (θ θ' : ℕ → ℝ) (s : ℕ)
    (hsmall : (∑ i ∈ Finset.range s, terminalWindowResidual θ i) < Real.pi) :
    (∑ i ∈ Finset.range s,
      (terminalWindowWinding θ' i - terminalWindowWinding θ i)) ≤
        ⌊(θ' 0 - θ' s) / Real.pi⌋ - ⌊(θ 0 - θ s) / Real.pi⌋ := by
  rw [Finset.sum_sub_distrib, terminalWindow_enclosing_eq_sum_of_small_residual θ s hsmall]
  have h := terminalWindow_enclosing_carry_nonneg θ' s
  omega

theorem canonicalCrossingCount_adjacent_increment_domination
    (e : ℕ → ℝ) (j L s : ℕ) (ω : PotentialSpace)
    (hsmall : (∑ i ∈ Finset.range s,
      canonicalCrossingResidual (e i) (e (i + 1) - e i) 0 0 j ω) < Real.pi) :
    (∑ i ∈ Finset.range s,
      (canonicalCrossingCount (e i) (e (i + 1) - e i) 0 0 (j + L) ω -
        canonicalCrossingCount (e i) (e (i + 1) - e i) 0 0 j ω)) ≤
      canonicalCrossingCount (e 0) (e s - e 0) 0 0 (j + L) ω -
        canonicalCrossingCount (e 0) (e s - e 0) 0 0 j ω := by
  let θ := fun k i => canonicalPhaseProcess (e i) 0 k ω
  have hwind (k i : ℕ) : terminalWindowWinding (θ k) i =
      canonicalCrossingCount (e i) (e (i + 1) - e i) 0 0 k ω := by
    simp only [terminalWindowWinding, canonicalCrossingCount, canonicalGapProcess,
      θ, add_sub_cancel]
  have hres (k i : ℕ) : terminalWindowResidual (θ k) i =
      canonicalCrossingResidual (e i) (e (i + 1) - e i) 0 0 k ω := by
    simp only [terminalWindowResidual, canonicalCrossingResidual, canonicalGapProcess,
      hwind, θ, add_sub_cancel]
  have h := terminalWindow_increment_domination (θ j) (θ (j + L)) s
    (by simpa only [hres] using hsmall)
  simpa only [hwind, canonicalCrossingCount, canonicalGapProcess, θ, add_sub_cancel] using h

end FixedCouplingPoisson.Furstenberg
