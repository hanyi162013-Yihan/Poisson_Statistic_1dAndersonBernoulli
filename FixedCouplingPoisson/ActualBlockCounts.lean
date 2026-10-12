import FixedCouplingPoisson.FreshCountKernel
import FixedCouplingPoisson.ResidualCountRestart
import FixedCouplingPoisson.ActualCountCarry

/-! Actual deterministic-block increments and their genuine conditional tails. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

def canonicalBlockCount (E δ θ φ : ℝ) (j L : ℕ) (ω : PotentialSpace) : ℕ :=
  (canonicalCrossingCount E δ θ φ (j + L) ω -
    canonicalCrossingCount E δ θ φ j ω).toNat

theorem canonicalBlockCount_measurable (E δ θ φ : ℝ) (j L : ℕ) :
    Measurable (canonicalBlockCount E δ θ φ j L) :=
  (measurable_of_countable Int.toNat).comp
    ((canonicalCrossingCount_measurable E δ θ φ (j + L)).sub
      (canonicalCrossingCount_measurable E δ θ φ j))

theorem canonicalBlockCount_eq_fresh (E δ θ φ : ℝ) (j L : ℕ) (ω : PotentialSpace) :
    canonicalBlockCount E δ θ φ j L ω =
      canonicalNaturalCrossingCount E δ (canonicalResidualState E δ θ φ j ω).1
        (canonicalResidualState E δ θ φ j ω).2 L (potentialShift j ω) :=
  (canonicalResidualState_natural_count_restart E δ θ φ j L ω).symm

theorem canonicalBlockCount_cast (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (j L : ℕ) (ω : PotentialSpace) :
    (canonicalBlockCount E δ θ φ j L ω : ℤ) =
      canonicalCrossingCount E δ θ φ (j + L) ω -
        canonicalCrossingCount E δ θ φ j ω := by
  apply Int.toNat_of_nonneg
  exact sub_nonneg.mpr ((canonicalCrossingCount_mono E δ θ φ hδ ω)
    (show j ≤ j + L by omega))

theorem canonicalBlockCount_zero_start (E δ θ : ℝ) (L : ℕ) (ω : PotentialSpace) :
    canonicalBlockCount E δ θ θ 0 L ω =
      canonicalNaturalCrossingCount E δ θ θ L ω := by
  simp only [canonicalBlockCount, canonicalNaturalCrossingCount, zero_add,
    canonicalCrossingCount, canonicalGapProcess, canonicalPhaseProcess_zero,
    sub_self, zero_div, Int.floor_zero, sub_zero]

theorem canonicalBlockCount_sum_partition (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (u : ℕ → ℕ) (hu : Monotone u) (m : ℕ) (ω : PotentialSpace) :
    (∑ b ∈ Finset.range m,
      canonicalBlockCount E δ θ φ (u b) (u (b + 1) - u b) ω) =
        canonicalBlockCount E δ θ φ (u 0) (u m - u 0) ω := by
  have hcast (b : ℕ) :
      (canonicalBlockCount E δ θ φ (u b) (u (b + 1) - u b) ω : ℤ) =
        canonicalCrossingCount E δ θ φ (u (b + 1)) ω -
          canonicalCrossingCount E δ θ φ (u b) ω := by
    rw [canonicalBlockCount_cast _ _ _ _ hδ,
      Nat.add_sub_of_le (hu (Nat.le_succ b))]
  have houter : (canonicalBlockCount E δ θ φ (u 0) (u m - u 0) ω : ℤ) =
      canonicalCrossingCount E δ θ φ (u m) ω -
        canonicalCrossingCount E δ θ φ (u 0) ω := by
    rw [canonicalBlockCount_cast _ _ _ _ hδ,
      Nat.add_sub_of_le (hu (Nat.zero_le m))]
  have heq : ((∑ b ∈ Finset.range m,
      canonicalBlockCount E δ θ φ (u b) (u (b + 1) - u b) ω : ℕ) : ℤ) =
        (canonicalBlockCount E δ θ φ (u 0) (u m - u 0) ω : ℤ) := by
    push_cast
    simp only [hcast, houter]
    exact Finset.sum_range_sub (fun b => canonicalCrossingCount E δ θ φ (u b) ω) m
  exact_mod_cast heq

theorem canonicalBlockCount_tail_condExp (law : PotentialLaw) (E δ θ φ : ℝ)
    (k j L : ℕ) :
    (iidMeasure law)[({ω | k ≤ canonicalBlockCount E δ θ φ j L ω}.indicator
      (fun _ => (1 : ℝ))) | pastMeasurableSpace j] =ᵐ[iidMeasure law]
        (fun ω => freshCountTailKernel law E δ k L (canonicalResidualState E δ θ φ j ω)) := by
  have heq : {ω | k ≤ canonicalBlockCount E δ θ φ j L ω}.indicator
      (fun _ => (1 : ℝ)) =
        (fun ω => freshCountTailObservable E δ k L
          (canonicalResidualState E δ θ φ j ω, potentialShift j ω)) := by
    funext ω
    simp only [freshCountTailObservable, canonicalBlockCount_eq_fresh,
      Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  exact freshCountTail_condExp law E δ k j L
    (canonicalResidualState_past_measurable E δ θ φ j)

theorem canonicalBlockCount_tailKernel_uniform_on_small_residual
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ r : ℕ → ℝ)
    (hE : ∀ n, E n ∈ K) (hE' : ∀ n, E n + δ n ∈ K)
    (hδ : ∀ n, 0 ≤ δ n) (hr : ∀ n, 0 ≤ r n)
    (hp : ∀ n, 0 < idsCandidate law (E n + δ n) - idsCandidate law (E n))
    (hδlim : Tendsto δ atTop (𝓝 0)) (hrlim : Tendsto r atTop (𝓝 0))
    (ℓ : ℕ → ℕ) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (E n + δ n) - idsCandidate law (E n)) * (ℓ n : ℝ)) atTop (𝓝 t))
    (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ θ φ : ℝ, ∀ j : ℕ, ∀ ω : PotentialSpace,
      canonicalCrossingResidual (E n) (δ n) θ φ j ω ≤ r n →
      |freshCountTailKernel law (E n) (δ n) k (ℓ n)
          (canonicalResidualState (E n) (δ n) θ φ j ω) -
        cdf (exponentialSumLaw k : Measure ℝ) t| < ε := by
  have h := freshCountTailKernel_uniform_small_gap law input hK E δ r
    hE hE' hδ hr hp hδlim hrlim ℓ htime k hk ε hε
  filter_upwards [h] with n hn
  intro θ φ j ω hsmall
  have h0 := (canonicalResidualState_gap_mem (E n) (δ n) θ φ j ω).1
  have h1 : (canonicalResidualState (E n) (δ n) θ φ j ω).1 -
      (canonicalResidualState (E n) (δ n) θ φ j ω).2 ≤ r n := by
    rw [canonicalResidualState_gap]
    exact hsmall
  exact hn (canonicalResidualState (E n) (δ n) θ φ j ω).1
    (canonicalResidualState (E n) (δ n) θ φ j ω).2 h0 h1

theorem canonicalBlockCount_adjacent_domination (e : ℕ → ℝ) (j L s : ℕ)
    (horder : ∀ i < s, e i ≤ e (i + 1)) (houter : e 0 ≤ e s)
    (ω : PotentialSpace)
    (hsmall : (∑ i ∈ Finset.range s,
      canonicalCrossingResidual (e i) (e (i + 1) - e i) 0 0 j ω) < Real.pi) :
    (∑ i ∈ Finset.range s,
      canonicalBlockCount (e i) (e (i + 1) - e i) 0 0 j L ω) ≤
        canonicalBlockCount (e 0) (e s - e 0) 0 0 j L ω := by
  have h := canonicalCrossingCount_adjacent_increment_domination e j L s ω hsmall
  have hsum : ((∑ i ∈ Finset.range s,
      canonicalBlockCount (e i) (e (i + 1) - e i) 0 0 j L ω : ℕ) : ℤ) =
        ∑ i ∈ Finset.range s,
          (canonicalCrossingCount (e i) (e (i + 1) - e i) 0 0 (j + L) ω -
            canonicalCrossingCount (e i) (e (i + 1) - e i) 0 0 j ω) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    exact canonicalBlockCount_cast _ _ _ _
      (sub_nonneg.mpr (horder i (Finset.mem_range.mp hi))) _ _ _
  have houterCast := canonicalBlockCount_cast (e 0) (e s - e 0) 0 0
    (sub_nonneg.mpr houter) j L ω
  rw [← hsum, ← houterCast] at h
  exact_mod_cast h

end FixedCouplingPoisson.Furstenberg
