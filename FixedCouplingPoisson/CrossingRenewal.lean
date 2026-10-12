import FixedCouplingPoisson.CrossingLevels
import FixedCouplingPoisson.UpperLayer
import FixedCouplingPoisson.CDFDynamics
import FixedCouplingPoisson.CDFExitUniform
import FixedCouplingPoisson.UpperLayerRemaining
import FixedCouplingPoisson.IIDMarkov
import FixedCouplingPoisson.JointKernel


/-! Factored proof group: CrossingRestart. -/

/-! Unchecked work draft. The actual stopped pair is recentered by its
completed number of pi crossings. Whole-future iid freshness proves the
finiteness of every fixed level, rather than assuming it as restart data. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def canonicalLevelState (E δ θ φ : ℝ) (k : ℕ) (ω : PotentialSpace) : ℝ × ℝ :=
  (stoppedValue (canonicalPhaseProcess E θ) (canonicalLevelCrossingTime E δ θ φ k) ω,
    stoppedValue (canonicalPhaseProcess (E + δ) φ)
      (canonicalLevelCrossingTime E δ θ φ k) ω + (k : ℝ) * Real.pi)

theorem canonicalLevelState_stopped_measurable (E δ θ φ : ℝ) (k : ℕ) :
    Measurable[(canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSpace]
      (canonicalLevelState E δ θ φ k) :=
  (canonicalPhaseProcess_stopped_measurable E θ
    (canonicalLevelCrossingTime_isStoppingTime E δ θ φ k)).prodMk
      ((canonicalPhaseProcess_stopped_measurable (E + δ) φ
        (canonicalLevelCrossingTime_isStoppingTime E δ θ φ k)).add measurable_const)

theorem canonicalLevelState_eq_of_time (E δ θ φ : ℝ) (k n : ℕ)
    (ω : PotentialSpace) (hn : canonicalLevelCrossingTime E δ θ φ k ω = n) :
    canonicalLevelState E δ θ φ k ω =
      (canonicalPhaseProcess E θ n ω,
        canonicalPhaseProcess (E + δ) φ n ω + (k : ℝ) * Real.pi) := by
  simp only [canonicalLevelState, stoppedValue, hn, WithTop.untopA]
  rfl

theorem canonicalLevelState_positive_gap_bounds (E δ θ φ : ℝ) (k : ℕ)
    (hδ : 0 ≤ δ) (hsmall : θ - φ < Real.pi) (hk : 0 < k)
    (ω : PotentialSpace) (hfinite : canonicalLevelCrossingTime E δ θ φ k ω ≠ ⊤) :
    0 ≤ (canonicalLevelState E δ θ φ k ω).1 -
        (canonicalLevelState E δ θ φ k ω).2 ∧
      (canonicalLevelState E δ θ φ k ω).1 -
        (canonicalLevelState E δ θ φ k ω).2 ≤ δ := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hb := canonicalLevelCrossingTime_hits_gap_bounds E δ θ φ hδ hsmall
    k n hk ω hn.symm
  rw [canonicalLevelState_eq_of_time E δ θ φ k n ω hn.symm]
  change 0 ≤ canonicalPhaseProcess E θ n ω -
    (canonicalPhaseProcess (E + δ) φ n ω + (k : ℝ) * Real.pi) ∧
    canonicalPhaseProcess E θ n ω -
      (canonicalPhaseProcess (E + δ) φ n ω + (k : ℝ) * Real.pi) ≤ δ
  dsimp only [canonicalGapProcess] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Each actual recentered pair lies below the next crossing. The zeroth
pair uses the initial gap; every positive level uses the true overshoot. -/
theorem canonicalLevelState_gap_bounds (E δ θ φ : ℝ) (k : ℕ)
    (hδ : 0 ≤ δ) (hδπ : δ < Real.pi) (hinit : φ ≤ θ)
    (hsmall : θ - φ < Real.pi) (ω : PotentialSpace)
    (hfinite : canonicalLevelCrossingTime E δ θ φ k ω ≠ ⊤) :
    0 ≤ (canonicalLevelState E δ θ φ k ω).1 -
        (canonicalLevelState E δ θ φ k ω).2 ∧
      (canonicalLevelState E δ θ φ k ω).1 -
        (canonicalLevelState E δ θ φ k ω).2 < Real.pi := by
  by_cases hk : k = 0
  · subst k
    rw [canonicalLevelState_eq_of_time E δ θ φ 0 0 ω
      (canonicalLevelCrossingTime_zero E δ θ φ hinit ω)]
    simpa only [Nat.cast_zero, zero_mul, add_zero, canonicalPhaseProcess_zero] using
      And.intro (sub_nonneg.mpr hinit) hsmall
  · have hb := canonicalLevelState_positive_gap_bounds E δ θ φ k hδ hsmall
      (Nat.pos_of_ne_zero hk) ω hfinite
    exact ⟨hb.1, hb.2.trans_lt hδπ⟩

def canonicalLevelWaitingTime (E δ θ φ : ℝ) (k : ℕ) (ω : PotentialSpace) : ℝ :=
  (((canonicalLevelCrossingTime E δ θ φ (k + 1) ω).untopD 0 -
    (canonicalLevelCrossingTime E δ θ φ k ω).untopD 0 : ℕ) : ℝ)

theorem canonicalLevelWaitingTime_measurable (E δ θ φ : ℝ) (k : ℕ) :
    Measurable (canonicalLevelWaitingTime E δ θ φ k) :=
  (measurable_of_countable (fun z : ℕ × ℕ => ((z.1 - z.2 : ℕ) : ℝ))).comp
    (((WithTop.measurable_untopD 0).comp
      (canonicalLevelCrossingTime_measurable E δ θ φ (k + 1))).prodMk
        ((WithTop.measurable_untopD 0).comp
          (canonicalLevelCrossingTime_measurable E δ θ φ k)))

theorem iidMeasure_level_state_future_map (law : PotentialLaw)
    (E δ θ φ : ℝ) (k : ℕ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalLevelCrossingTime E δ θ φ k ω ≠ ⊤) :
    (iidMeasure law).map (fun ω => (canonicalLevelState E δ θ φ k ω,
      stoppedPotentialFuture (canonicalLevelCrossingTime E δ θ φ k) ω)) =
        ((iidMeasure law).map (canonicalLevelState E δ θ φ k)).prod (iidMeasure law) :=
  iidMeasure_stopped_state_future_map law
    (canonicalLevelCrossingTime_isStoppingTime E δ θ φ k) hfinite
    (canonicalLevelState_stopped_measurable E δ θ φ k)

end FixedCouplingPoisson

namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter

/-- Positive actual IDS increment and whole-future iid freshness imply
that every fixed crossing level is reached almost surely. -/
theorem canonicalLevelCrossingTime_ae_finite (law : PotentialLaw) (input : Input law)
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (k : ℕ) :
    ∀ᵐ ω ∂iidMeasure law, canonicalLevelCrossingTime E δ θ φ k ω ≠ ⊤ := by
  induction k with
  | zero =>
    exact ae_of_all _ fun ω => by
      rw [canonicalLevelCrossingTime_zero E δ θ φ hinit ω]
      simp
  | succ k ih =>
    let τ := canonicalLevelCrossingTime E δ θ φ k
    let X := canonicalLevelState E δ θ φ k
    have hτ : IsStoppingTime potentialFiltration τ :=
      canonicalLevelCrossingTime_isStoppingTime E δ θ φ k
    have hX : Measurable[hτ.measurableSpace] X :=
      canonicalLevelState_stopped_measurable E δ θ φ k
    have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
    have hpair : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
      hXm.prodMk (measurable_stoppedPotentialFuture hτ)
    have hvalid : MeasurableSet {x : ℝ × ℝ | x.2 ≤ x.1 ∧ x.1 - x.2 ≤ Real.pi} :=
      (measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le (measurable_fst.sub measurable_snd) measurable_const)
    have hstate : ∀ᵐ x : ℝ × ℝ ∂(iidMeasure law).map X,
        x.2 ≤ x.1 ∧ x.1 - x.2 ≤ Real.pi := by
      apply (ae_map_iff hXm.aemeasurable hvalid).mpr
      filter_upwards [ih] with ω hω
      have hb := canonicalLevelState_gap_bounds E δ θ φ k hδ hδπ hinit hsmall ω hω
      exact ⟨sub_nonneg.mp hb.1, hb.2.le⟩
    have hpred : MeasurableSet {z : (ℝ × ℝ) × PotentialSpace |
        canonicalCrossingTime E δ z.1.1 z.1.2 z.2 ≠ ⊤} :=
      (measurableSet_eq_fun (canonicalCrossingTime_measurable_initial_path E δ)
        measurable_const).compl
    have hprod : ∀ᵐ z : (ℝ × ℝ) × PotentialSpace
        ∂((iidMeasure law).map X).prod (iidMeasure law),
        canonicalCrossingTime E δ z.1.1 z.1.2 z.2 ≠ ⊤ := by
      apply (Measure.ae_prod_iff_ae_ae hpred).mpr
      filter_upwards [hstate] with x hx
      exact (canonicalCrossingTime_finite_mean_IDS law
        (input.atEnergy E).inverseMeasure (input.atEnergy (E + δ)).inverseMeasure
        E δ x.1 x.2 (input.atEnergy E).inverse_stationary
        (input.atEnergy (E + δ)).inverse_stationary hδ hx.1 hx.2 hp).1
    have hfuture : ∀ᵐ ω ∂iidMeasure law,
        canonicalCrossingTime E δ (X ω).1 (X ω).2 (stoppedPotentialFuture τ ω) ≠ ⊤ := by
      rw [← iidMeasure_stopped_state_future_map law hτ ih hX] at hprod
      exact (ae_map_iff hpair.aemeasurable hpred).mp hprod
    filter_upwards [ih, hfuture] with ω hω hfω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    have hstateEq := canonicalLevelState_eq_of_time E δ θ φ k n ω hn.symm
    have hshift : stoppedPotentialFuture τ ω = potentialShift n ω := by
      simp only [stoppedPotentialFuture, τ, ← hn, WithTop.untopD_coe]
    change canonicalCrossingTime E δ (canonicalLevelState E δ θ φ k ω).1
      (canonicalLevelState E δ θ φ k ω).2 (stoppedPotentialFuture τ ω) ≠ ⊤ at hfω
    rw [hstateEq, hshift] at hfω
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hfω
    have hfresh : canonicalCrossingTime E δ (canonicalPhaseProcess E θ n ω)
        (canonicalPhaseProcess (E + δ) φ n ω + (k : ℤ) * Real.pi)
        (potentialShift n ω) ≤ j := by
      simpa only [Int.cast_natCast, Nat.cast_withTop] using hj.symm.le
    have hnext := (canonicalLevelCrossingTime_restart_le_iff E δ θ φ hδ k n j ω).mp hfresh
    intro htop
    rw [htop] at hnext
    have hne : (((n + j : ℕ) : WithTop ℕ)) ≠ ⊤ := by simp
    exact hne (top_le_iff.mp hnext)

/-- The real next waiting time equals the actual first crossing on the
whole stopped future, outside the already proved finite-time null sets. -/
theorem canonicalLevelWaitingTime_ae_restart (law : PotentialLaw) (input : Input law)
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (k : ℕ) :
    (fun ω => (((canonicalCrossingTime E δ (canonicalLevelState E δ θ φ k ω).1
      (canonicalLevelState E δ θ φ k ω).2
      (stoppedPotentialFuture (canonicalLevelCrossingTime E δ θ φ k) ω)).untopD 0 : ℕ) : ℝ))
        =ᵐ[iidMeasure law] canonicalLevelWaitingTime E δ θ φ k := by
  filter_upwards [canonicalLevelCrossingTime_ae_finite law input E δ θ φ
    hδ hδπ hinit hsmall hp k, canonicalLevelCrossingTime_ae_finite law input E δ θ φ
    hδ hδπ hinit hsmall hp (k + 1)] with ω hω hω'
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hω'
  have hle := canonicalLevelCrossingTime_mono E δ θ φ ω (Nat.le_succ k)
  change canonicalLevelCrossingTime E δ θ φ k ω ≤
    canonicalLevelCrossingTime E δ θ φ (k + 1) ω at hle
  rw [← hn, ← hm] at hle
  have hnm : n ≤ m := WithTop.coe_le_coe.mp hle
  have hshift : stoppedPotentialFuture (canonicalLevelCrossingTime E δ θ φ k) ω =
      potentialShift n ω := by
    simp only [stoppedPotentialFuture, ← hn, WithTop.untopD_coe]
  have hfresh : canonicalCrossingTime E δ (canonicalPhaseProcess E θ n ω)
      (canonicalPhaseProcess (E + δ) φ n ω + (k : ℝ) * Real.pi)
      (potentialShift n ω) = ((m - n : ℕ) : WithTop ℕ) := by
    simpa only [Int.cast_natCast] using
      canonicalLevelCrossingTime_restart_of_finite E δ θ φ hδ k n m ω hnm hm.symm
  rw [canonicalLevelState_eq_of_time E δ θ φ k n ω hn.symm, hshift, hfresh]
  simp only [canonicalLevelWaitingTime, ← hn, ← hm, Nat.cast_withTop, WithTop.untopD_coe]

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CrossingLaplaceKernel. -/

/-! Unchecked work draft. Actual conditional Laplace kernels for successive
crossing waits. Finiteness is derived in CrossingRestart and the fresh
future is the actual iid conditional kernel, not an assumed renewal law. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory

def canonicalLevelLaplaceFactor (law : PotentialLaw) (E δ θ φ t : ℝ)
    (k : ℕ) (ω : PotentialSpace) : ℝ :=
  Real.exp (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
    canonicalLevelWaitingTime E δ θ φ k ω)

theorem canonicalLevelLaplaceFactor_measurable
    (law : PotentialLaw) (E δ θ φ t : ℝ) (k : ℕ) :
    Measurable (canonicalLevelLaplaceFactor law E δ θ φ t k) :=
  (measurable_const.mul (canonicalLevelWaitingTime_measurable E δ θ φ k)).exp

/-- This is the real stopped-past conditional expectation, retaining
the entire recentered phase pair in its fresh-future integral. -/
theorem canonicalLevelLaplaceFactor_condExp (law : PotentialLaw) (input : Input law)
    (E δ θ φ t : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (ht : 0 ≤ t) (k : ℕ) :
    (iidMeasure law)[canonicalLevelLaplaceFactor law E δ θ φ t k |
      (canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSpace] =ᵐ[
      iidMeasure law] (fun ω => ∫ ξ, Real.exp
        (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (((canonicalCrossingTime E δ (canonicalLevelState E δ θ φ k ω).1
            (canonicalLevelState E δ θ φ k ω).2 ξ).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law) := by
  let τ := canonicalLevelCrossingTime E δ θ φ k
  let X := canonicalLevelState E δ θ φ k
  let f : (ℝ × ℝ) × PotentialSpace → ℝ := fun z => Real.exp
    (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (((canonicalCrossingTime E δ z.1.1 z.1.2 z.2).untopD 0 : ℕ) : ℝ))
  have hτ : IsStoppingTime potentialFiltration τ :=
    canonicalLevelCrossingTime_isStoppingTime E δ θ φ k
  have hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤ :=
    canonicalLevelCrossingTime_ae_finite law input E δ θ φ hδ hδπ hinit hsmall hp k
  have hX : Measurable[hτ.measurableSpace] X :=
    canonicalLevelState_stopped_measurable E δ θ φ k
  have hfm : Measurable f :=
    (measurable_const.mul (canonicalCrossingReal_measurable_initial_path E δ)).exp
  have hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law)) :=
    bounded_block_integrable hfm.stronglyMeasurable (fun z =>
      ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg ht hp.le)) (Nat.cast_nonneg _))⟩)
  have heq : (fun ω => f (X ω, stoppedPotentialFuture τ ω)) =ᵐ[iidMeasure law]
      canonicalLevelLaplaceFactor law E δ θ φ t k := by
    filter_upwards [canonicalLevelWaitingTime_ae_restart law input E δ θ φ
      hδ hδπ hinit hsmall hp k] with ω hω
    change Real.exp (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (((canonicalCrossingTime E δ (canonicalLevelState E δ θ φ k ω).1
        (canonicalLevelState E δ θ φ k ω).2 (stoppedPotentialFuture τ ω)).untopD 0 : ℕ) : ℝ)) = _
    rw [hω]
    rfl
  have hc := iidMeasure_condExp_stopped_futureKernel law hτ hfinite hX hfm hf
  exact (condExp_congr_ae (m := hτ.measurableSpace) heq.symm).trans hc

/-- One compact-energy threshold works for every fixed crossing number.
The initial gap is small at level zero; all later gaps are at most delta
by actual overshoot. No independence of finite-delta waits is asserted. -/
theorem canonicalLevelLaplaceFactor_condExp_uniform (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < d →
        0 < idsCandidate law (E + δ) - idsCandidate law E → ∀ k : ℕ,
        ∀ᵐ ω ∂iidMeasure law,
          |((iidMeasure law)[canonicalLevelLaplaceFactor law E δ θ φ t k |
            (canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSpace]) ω -
              (1 + t)⁻¹| ≤ ε := by
  obtain ⟨d0, hd0, hkernel⟩ := inverseCrossingLaplace_small_gap_uniform
    law input hK ht hε
  let d := min d0 Real.pi
  have hd : 0 < d := lt_min hd0 Real.pi_pos
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp k
  have hδπ : δ < Real.pi := hδd.trans_le (min_le_right _ _)
  have hsmallπ : θ - φ < Real.pi := hsmall.trans_le (min_le_right _ _)
  filter_upwards [canonicalLevelLaplaceFactor_condExp law input E δ θ φ t hδ hδπ
    hinit hsmallπ hp ht k, canonicalLevelCrossingTime_ae_finite law input E δ θ φ
      hδ hδπ hinit hsmallπ hp k] with ω hcω hfω
  rw [hcω]
  have hb := canonicalLevelState_gap_bounds E δ θ φ k hδ hδπ hinit hsmallπ ω hfω
  have hgap : (canonicalLevelState E δ θ φ k ω).1 -
      (canonicalLevelState E δ θ φ k ω).2 < min d0 Real.pi := by
    by_cases hk : k = 0
    · subst k
      rw [canonicalLevelState_eq_of_time E δ θ φ 0 0 ω
        (canonicalLevelCrossingTime_zero E δ θ φ hinit ω)]
      simpa only [Nat.cast_zero, zero_mul, add_zero, canonicalPhaseProcess_zero] using hsmall
    · exact (canonicalLevelState_positive_gap_bounds E δ θ φ k hδ hsmallπ
        (Nat.pos_of_ne_zero hk) ω hfω).2.trans_lt hδd
  exact hkernel E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
    (canonicalLevelState E δ θ φ k ω).1 (canonicalLevelState E δ θ φ k ω).2
    (sub_nonneg.mp hb.1) hgap hp

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: FixedCouplingPoisson/JointProductBudget.lean. -/

/-! Finite conditional products with different target factors. The model
conditional estimates and past measurability must be proved separately. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory

theorem variable_product_error_budget (F a ε : ℕ → ℝ) (m : ℕ)
    (hF0 : F 0 = 1) (ha0 : ∀ b < m, 0 ≤ a b) (ha1 : ∀ b < m, a b ≤ 1)
    (hstep : ∀ b < m, |F (b + 1) - a b * F b| ≤ ε b) :
    |F m - ∏ b ∈ Finset.range m, a b| ≤ ∑ b ∈ Finset.range m, ε b := by
  have hbudget : ∀ n ≤ m,
      |F n - ∏ b ∈ Finset.range n, a b| ≤ ∑ b ∈ Finset.range n, ε b := by
    intro n
    induction n with
    | zero => intro _; simp [hF0]
    | succ n ih =>
      intro hn
      have hnm : n < m := by omega
      have hprev := ih (by omega)
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      have heq : F (n + 1) - (∏ b ∈ Finset.range n, a b) * a n =
          (F (n + 1) - a n * F n) +
            a n * (F n - ∏ b ∈ Finset.range n, a b) := by ring
      rw [heq]
      calc
        _ ≤ |F (n + 1) - a n * F n| +
            |a n * (F n - ∏ b ∈ Finset.range n, a b)| := abs_add_le _ _
        _ ≤ ε n + |F n - ∏ b ∈ Finset.range n, a b| := by
          apply add_le_add (hstep n hnm)
          rw [abs_mul, abs_of_nonneg (ha0 n hnm)]
          exact mul_le_of_le_one_left (abs_nonneg _) (ha1 n hnm)
        _ ≤ ε n + ∑ b ∈ Finset.range n, ε b := add_le_add le_rfl hprev
        _ = _ := add_comm _ _
  exact hbudget m le_rfl

theorem conditional_variable_product_error_budget
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Ψ : ℕ → Ω → ℝ) (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1)
    (M : ℕ → MeasurableSpace Ω) (m : ℕ) (hM : ∀ b < m, M b ≤ m₀)
    (hpast : ∀ b < m, StronglyMeasurable[M b] (prefixProduct Ψ b))
    (a ε : ℕ → ℝ) (ha0 : ∀ b < m, 0 ≤ a b) (ha1 : ∀ b < m, a b ≤ 1)
    (hε : ∀ b < m, 0 ≤ ε b)
    (hkernel : ∀ b < m, ∀ᵐ ω ∂μ, |(μ[Ψ b | M b]) ω - a b| ≤ ε b) :
    |(∫ ω, prefixProduct Ψ m ω ∂μ) - ∏ b ∈ Finset.range m, a b| ≤
      ∑ b ∈ Finset.range m, ε b := by
  apply variable_product_error_budget (fun n => ∫ ω, prefixProduct Ψ n ω ∂μ)
    a ε m (by simp) ha0 ha1
  intro b hb
  have h := conditional_one_step_budget Ψ hmeas hbound (hM b hb) b (hpast b hb)
    (ha0 b hb) (ha1 b hb) (hε b hb) (G := Set.univ) MeasurableSet.univ
    (by filter_upwards [hkernel b hb] with ω hω _; exact hω)
  simpa using h

end FixedCouplingPoisson

/-! Factored proof group: FixedCouplingPoisson/CrossingJointLaplace.lean. -/

/-! Actual finite families of crossing waits: stopped-past measurability
and conditional product replacement. No finite-energy independence of
the waits is assumed. This source is an unchecked work draft. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem canonicalLevelCrossingTime_measurable_at_later_level
    (E δ θ φ : ℝ) {j k : ℕ} (hjk : j ≤ k) :
    Measurable[(canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSpace]
      (canonicalLevelCrossingTime E δ θ φ j) :=
  (canonicalLevelCrossingTime_isStoppingTime E δ θ φ j).measurable.mono
    ((canonicalLevelCrossingTime_isStoppingTime E δ θ φ j).measurableSpace_mono
      (canonicalLevelCrossingTime_isStoppingTime E δ θ φ k)
      (fun ω => canonicalLevelCrossingTime_mono E δ θ φ ω hjk)) le_rfl

theorem canonicalLevelWaitingTime_measurable_at_later_level
    (E δ θ φ : ℝ) {j k : ℕ} (hjk : j + 1 ≤ k) :
    Measurable[(canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSpace]
      (canonicalLevelWaitingTime E δ θ φ j) :=
  (measurable_of_countable (fun z : ℕ × ℕ => ((z.1 - z.2 : ℕ) : ℝ))).comp
    (((WithTop.measurable_untopD 0).comp
      (canonicalLevelCrossingTime_measurable_at_later_level E δ θ φ hjk)).prodMk
        ((WithTop.measurable_untopD 0).comp
          (canonicalLevelCrossingTime_measurable_at_later_level E δ θ φ (by omega))))

theorem canonicalLevelLaplaceFactor_measurable_at_later_level
    (law : PotentialLaw) (E δ θ φ t : ℝ) {j k : ℕ} (hjk : j + 1 ≤ k) :
    Measurable[(canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSpace]
      (canonicalLevelLaplaceFactor law E δ θ φ t j) :=
  (measurable_const.mul
    (canonicalLevelWaitingTime_measurable_at_later_level E δ θ φ hjk)).exp

theorem canonicalLevelLaplaceFactor_bounds (law : PotentialLaw)
    (E δ θ φ t : ℝ) (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E)
    (ht : 0 ≤ t) (j : ℕ) (ω : PotentialSpace) :
    0 ≤ canonicalLevelLaplaceFactor law E δ θ φ t j ω ∧
      canonicalLevelLaplaceFactor law E δ θ φ t j ω ≤ 1 := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg ht hp)) (Nat.cast_nonneg _)

theorem canonicalLevelLaplace_prefix_past (law : PotentialLaw)
    (E δ θ φ : ℝ) (t : ℕ → ℝ) (b : ℕ) :
    StronglyMeasurable[(canonicalLevelCrossingTime_isStoppingTime E δ θ φ b).measurableSpace]
      (prefixProduct (fun j => canonicalLevelLaplaceFactor law E δ θ φ (t j) j) b) := by
  exact (Finset.range b).stronglyMeasurable_fun_prod (fun j hj =>
    (canonicalLevelLaplaceFactor_measurable_at_later_level law E δ θ φ (t j)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).stronglyMeasurable)

theorem canonicalLevelLaplace_product_error_budget (law : PotentialLaw)
    (E δ θ φ : ℝ) (t : ℕ → ℝ) (ht : ∀ j, 0 ≤ t j)
    (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E)
    (m : ℕ) (e : ℝ) (he : 0 ≤ e)
    (hkernel : ∀ b < m, ∀ᵐ ω ∂iidMeasure law,
      |((iidMeasure law)[canonicalLevelLaplaceFactor law E δ θ φ (t b) b |
        (canonicalLevelCrossingTime_isStoppingTime E δ θ φ b).measurableSpace]) ω -
          (1 + t b)⁻¹| ≤ e) :
    |(∫ ω, prefixProduct
        (fun j => canonicalLevelLaplaceFactor law E δ θ φ (t j) j) m ω ∂iidMeasure law) -
      ∏ j ∈ Finset.range m, (1 + t j)⁻¹| ≤ (m : ℝ) * e := by
  have h := conditional_variable_product_error_budget
    (μ := iidMeasure law) (fun j => canonicalLevelLaplaceFactor law E δ θ φ (t j) j)
    (fun j => (canonicalLevelLaplaceFactor_measurable law E δ θ φ (t j) j).stronglyMeasurable)
    (fun j ω => canonicalLevelLaplaceFactor_bounds law E δ θ φ (t j) hp (ht j) j ω)
    (fun j => (canonicalLevelCrossingTime_isStoppingTime E δ θ φ j).measurableSpace) m
    (fun j _ => (canonicalLevelCrossingTime_isStoppingTime E δ θ φ j).measurableSpace_le)
    (fun j _ => canonicalLevelLaplace_prefix_past law E δ θ φ t j)
    (fun j => (1 + t j)⁻¹) (fun _ => e)
    (fun j _ => inv_nonneg.mpr (add_nonneg zero_le_one (ht j)))
    (fun j _ => inv_le_one_of_one_le₀ (le_add_of_nonneg_right (ht j)))
    (fun _ _ => he) hkernel
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

theorem canonicalLevelLaplace_product_tendsto
    {ι : Type*} {F : Filter ι} (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0))
    (t : ℕ → ℝ) (ht : ∀ j, 0 ≤ t j) (m : ℕ) :
    Tendsto (fun i => ∫ ω, prefixProduct
      (fun j => canonicalLevelLaplaceFactor law (E i) (δ i) (θ i) (φ i) (t j) j) m ω
      ∂iidMeasure law) F (𝓝 (∏ j ∈ Finset.range m, (1 + t j)⁻¹)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e : ℝ := ε / (2 * ((m : ℝ) + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hevent : ∀ᶠ i in F, ∀ b ∈ Finset.range m, ∀ᵐ ω ∂iidMeasure law,
      |((iidMeasure law)[canonicalLevelLaplaceFactor law (E i) (δ i) (θ i) (φ i) (t b) b |
        (canonicalLevelCrossingTime_isStoppingTime (E i) (δ i) (θ i) (φ i) b).measurableSpace]) ω -
          (1 + t b)⁻¹| ≤ e := by
    apply (eventually_all_finset (Finset.range m)).mpr
    intro b _
    obtain ⟨d, hd, hk⟩ := canonicalLevelLaplaceFactor_condExp_uniform law input hK (ht b) he
    filter_upwards [hδlim.eventually (Iio_mem_nhds hd),
      hgap.eventually (Iio_mem_nhds hd)] with i hiδ higap
    exact hk (E i) (hE i) (δ i) (hδ i) (hE' i) hiδ
      (θ i) (φ i) (hinit i) higap (hp i) b
  filter_upwards [hevent] with i hi
  rw [Real.dist_eq]
  have hb := canonicalLevelLaplace_product_error_budget law (E i) (δ i) (θ i) (φ i)
    t ht (hp i).le m e he.le (fun b hb => hi b (Finset.mem_range.mpr hb))
  have hsmall : (m : ℝ) * e ≤ ε / 2 := by
    calc
      _ ≤ ((m : ℝ) + 1) * e :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) he.le
      _ = ε / 2 := by
        dsimp [e]
        field_simp [show (m : ℝ) + 1 ≠ 0 by positivity]
        <;> ring
  exact (hb.trans hsmall).trans_lt (half_lt_self hε)

end FixedCouplingPoisson.Furstenberg
