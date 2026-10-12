import FixedCouplingPoisson.PhaseWindow
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Deterministic vanishing cutoffs for residual tails

A diagonal choice is made from proved fixed-threshold convergence. The
resulting cutoff is positive and decreasing, tends to zero, and its bad
probability tends to zero along the full sequence, rather than a subsequence.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Full-sequence deterministic diagonalization of fixed-threshold tail
estimates. The conclusion includes a decreasing positive cutoff. -/
theorem exists_antitone_cutoff_of_fixed_tails
    (p : ℕ → ℝ → ℝ≥0∞)
    (hp : ∀ h : ℝ, 0 < h → Tendsto (fun n => p n h) atTop (𝓝 0)) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Antitone h ∧
      Tendsto h atTop (𝓝 0) ∧ Tendsto (fun n => p n (h n)) atTop (𝓝 0) := by
  classical
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hu : ∀ k, 0 < u k := by intro k; dsimp only [u]; positivity
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, p n (u k) ≤ ENNReal.ofReal (u k) := by
    intro k
    exact eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp (hp (u k) (hu k)))
      (ENNReal.ofReal (u k)) (ENNReal.ofReal_pos.mpr (hu k)))
  choose N hN using hN
  let k : ℕ → ℕ := fun n => Nat.findGreatest (fun m => N m ≤ n) n
  have hkmono : Monotone k := by
    intro a b hab
    exact Nat.findGreatest_mono (fun m hm => hm.trans hab) hab
  have hktop : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro m
    filter_upwards [eventually_ge_atTop (max m (N m))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn)
      ((le_max_right _ _).trans hn)
  let h : ℕ → ℝ := fun n => u (k n)
  have hhpos : ∀ n, 0 < h n := fun n => hu (k n)
  have hhmono : Antitone h := by
    intro a b hab
    apply one_div_le_one_div_of_le (by positivity : 0 < (k a : ℝ) + 1)
    exact add_le_add (Nat.cast_le.mpr (hkmono hab)) le_rfl
  have hhtop : Tendsto h atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hktop
  have htail : ∀ᶠ n in atTop, p n (h n) ≤ ENNReal.ofReal (h n) := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have hk : N (k n) ≤ n :=
      Nat.findGreatest_spec (P := fun m => N m ≤ n) (Nat.zero_le n) hn
    exact hN (k n) n hk
  refine ⟨h, hhpos, hhmono, hhtop, ?_⟩
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hupper : Tendsto (fun n => ENNReal.ofReal (h n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hhtop
  filter_upwards [htail, (ENNReal.tendsto_nhds_zero.mp hupper) ε hε] with n hn huε
  exact hn.trans huε

/-- A finite family of fixed-threshold residual tails has a vanishing union
probability. The index can combine window and deterministic block-start indices. -/
theorem finite_residual_tail_union_tendsto_zero {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (R : ℕ → ι → Ω → ℝ)
    (hR : ∀ i, ∀ h : ℝ, 0 < h →
      Tendsto (fun n => μ {ω | h < R n i ω}) atTop (𝓝 0))
    (h : ℝ) (hh : 0 < h) :
    Tendsto (fun n => μ {ω | ∃ i, h < R n i ω}) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ i : ι, μ {ω | h < R n i ω})
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset ι) (fun (i : ι) _ => hR i h hh)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro n
  have heq : {ω | ∃ i, h < R n i ω} = ⋃ i : ι, {ω | h < R n i ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  change μ {ω | ∃ i, h < R n i ω} ≤ ∑ i : ι, μ {ω | h < R n i ω}
  rw [heq]
  exact measure_iUnion_fintype_le _ _

/-- One decreasing deterministic cutoff works for every member of a finite
residual family. No uniform fixed-threshold estimate was assumed. -/
theorem finite_residual_exists_antitone_cutoff {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (R : ℕ → ι → Ω → ℝ)
    (hR : ∀ i, ∀ h : ℝ, 0 < h →
      Tendsto (fun n => μ {ω | h < R n i ω}) atTop (𝓝 0)) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Antitone h ∧
      Tendsto h atTop (𝓝 0) ∧ Tendsto
        (fun n => μ {ω | ∃ i, h n < R n i ω}) atTop (𝓝 0) :=
  exists_antitone_cutoff_of_fixed_tails _
    (finite_residual_tail_union_tendsto_zero μ R hR)

/-- The actual residual tails yield the deterministic cutoff required at
all finitely many window indices of a fixed observation array. -/
theorem actualWindow_exists_antitone_residual_cutoff (law : PotentialLaw)
    (e : ℕ → ℕ → ℝ) (s : ℕ)
    (hres : ∀ h : ℝ, 0 < h → Tendsto
      (fun n => iidMeasure law {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω})
      atTop (𝓝 0)) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Antitone h ∧
      Tendsto h atTop (𝓝 0) ∧ Tendsto
        (fun n => iidMeasure law {ω | ∃ i, i < s ∧ h n < actualWindowResidual e n i ω})
          atTop (𝓝 0) :=
  exists_antitone_cutoff_of_fixed_tails _ hres

/-- Individual actual residual tails suffice: the proved finite union
estimate is applied before choosing the single deterministic cutoff. -/
theorem actualWindow_exists_antitone_residual_cutoff_of_individual
    (law : PotentialLaw) (e : ℕ → ℕ → ℝ) (s : ℕ)
    (hres : ∀ i < s, ∀ h : ℝ, 0 < h → Tendsto
      (fun n => iidMeasure law {ω | h < actualWindowResidual e n i ω}) atTop (𝓝 0)) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Antitone h ∧
      Tendsto h atTop (𝓝 0) ∧ Tendsto
        (fun n => iidMeasure law {ω | ∃ i, i < s ∧ h n < actualWindowResidual e n i ω})
          atTop (𝓝 0) :=
  actualWindow_exists_antitone_residual_cutoff law e s
    (actualWindow_residual_union_tendsto_zero law e s hres)

end FixedCouplingPoisson.Furstenberg
