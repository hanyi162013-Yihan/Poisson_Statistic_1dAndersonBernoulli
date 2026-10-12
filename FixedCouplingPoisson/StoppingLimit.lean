import FixedCouplingPoisson.Occupation
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Truncation before unbounded stopping

General probability lemmas derive almost-everywhere finiteness and integrability
from uniform expectations of finite truncations, and only then remove a bounded
stopped-coordinate truncation by dominated convergence. Exact conditional drift
is proved for bounded stopping. These lemmas do not assert that the present
Schrödinger model already satisfies the required drift and coordinate bounds.
-/

namespace FixedCouplingPoisson
namespace Occupation
open MeasureTheory Filter
open scoped Topology BigOperators ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem sum_setIntegral_stopped_increment (τ : Ω → ℕ) (N : ℕ)
    (hτ : ∀ ω, τ ω ≤ N) (hA : ∀ j, MeasurableSet {ω | j < τ ω})
    (W : ℕ → Ω → ℝ) (hW : ∀ j, Integrable (W j) μ)
    (hWτ : Integrable (fun ω => W (τ ω) ω) μ) :
    (∑ j ∈ Finset.range N,
      ∫ ω in {ω | j < τ ω}, W (j + 1) ω - W j ω ∂μ) =
      (∫ ω, W (τ ω) ω ∂μ) - ∫ ω, W 0 ω ∂μ := by
  rw [sum_setIntegral_before_stopping τ N hτ hA (fun j ω => W (j + 1) ω - W j ω)
    (fun j => (hW (j + 1)).sub (hW j))]
  calc
    _ = ∫ ω, W (τ ω) ω - W 0 ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => Finset.sum_range_sub (fun j => W j ω) (τ ω)
    _ = _ := integral_sub hWτ (hW 0)

/-- Exact bounded stopping from a genuine constant conditional drift.
This remains a general probability theorem until the model's harmonic
coordinate and its conditional drift have been proved. -/
theorem bounded_stopped_drift_identity [IsFiniteMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ j, F j ≤ ‹MeasurableSpace Ω›)
    (τ : Ω → ℕ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet[F j] {ω | j < τ ω})
    (W : ℕ → Ω → ℝ) (hW : ∀ j, Integrable (W j) μ)
    (hWτ : Integrable (fun ω => W (τ ω) ω) μ) (c : ℝ)
    (hdrift : ∀ j < N, ∀ᵐ ω ∂μ,
      (μ[W (j + 1) | F j]) ω - W j ω = c) :
    c * (∫ ω, (τ ω : ℝ) ∂μ) =
      (∫ ω, W (τ ω) ω ∂μ) - ∫ ω, W 0 ω ∂μ := by
  classical
  have hstep : ∀ j < N,
      (∫ ω in {ω | j < τ ω}, W (j + 1) ω - W j ω ∂μ) =
        c * (μ {ω | j < τ ω}).toReal := by
    intro j hj
    have hc : (∫ ω in {ω | j < τ ω}, (μ[W (j + 1) | F j]) ω - W j ω ∂μ) =
        ∫ _ω in {ω | j < τ ω}, c ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hdrift j hj))
    rw [integral_sub integrable_condExp.integrableOn (hW j).integrableOn,
      setIntegral_condExp (hF j) (hW (j + 1)) (hA j),
      ← integral_sub (hW (j + 1)).integrableOn (hW j).integrableOn,
      setIntegral_const] at hc
    simpa only [smul_eq_mul, Measure.real, mul_comm c] using hc
  have hsum := Finset.sum_congr rfl fun j (hj : j ∈ Finset.range N) =>
    hstep j (Finset.mem_range.mp hj)
  rw [sum_setIntegral_stopped_increment τ N hτ (fun j => hF j _ (hA j)) W hW hWτ,
    ← Finset.mul_sum] at hsum
  have hcount := sum_setIntegral_before_stopping (μ := μ) τ N hτ
    (fun j => hF j _ (hA j)) (fun _ _ => (1 : ℝ)) (fun _ => integrable_const 1)
  have hcount' : (∑ j ∈ Finset.range N, (μ {ω | j < τ ω}).toReal) =
      ∫ ω, (τ ω : ℝ) ∂μ := by simpa [Measure.real] using hcount
  rw [hcount'] at hsum
  exact hsum.symm

/-- A finite deterministic truncation, retaining the possibility of an
infinite hitting time in the input. -/
def truncatedTime (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) : ℝ :=
  ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0 : ℕ)

theorem truncatedTime_nonneg (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) :
    0 ≤ truncatedTime τ N ω := by
  exact Nat.cast_nonneg _

theorem truncatedTime_le (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω) :
    truncatedTime τ N ω ≤ (N : ℝ) := by
  cases h : τ ω with
  | top => simp only [truncatedTime, h, min_top_left, WithTop.untopD_coe, le_refl]
  | coe n => simp only [truncatedTime, h, ← WithTop.coe_min, WithTop.untopD_coe]
             exact_mod_cast min_le_right n N

theorem truncatedTime_mono (τ : Ω → WithTop ℕ) (ω : Ω) :
    Monotone (fun N : ℕ => truncatedTime τ N ω) := by
  intro n m hnm
  cases h : τ ω with
  | top =>
      simpa only [truncatedTime, h, min_top_left, WithTop.untopD_coe] using
        (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)
  | coe k =>
      simp only [truncatedTime, h, ← WithTop.coe_min, WithTop.untopD_coe]
      exact_mod_cast min_le_min_left k hnm

theorem measurable_truncatedTime {τ : Ω → WithTop ℕ} (hτ : Measurable τ) (N : ℕ) :
    Measurable (truncatedTime τ N) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    ((WithTop.measurable_untopD 0).comp (hτ.min measurable_const))

theorem integrable_truncatedTime [IsFiniteMeasure μ] {τ : Ω → WithTop ℕ}
    (hτ : Measurable τ) (N : ℕ) : Integrable (truncatedTime τ N) μ := by
  apply (integrable_const (N : ℝ)).mono' (measurable_truncatedTime hτ N).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (truncatedTime_nonneg τ N ω)]
    exact truncatedTime_le τ N ω

noncomputable def extendedTime (τ : Ω → WithTop ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal (truncatedTime τ N ω)

theorem extendedTime_top {τ : Ω → WithTop ℕ} {ω : Ω} (h : τ ω = ⊤) :
    extendedTime τ ω = ⊤ := by
  simp only [extendedTime, truncatedTime, h, min_top_left, WithTop.untopD_coe,
    ENNReal.ofReal_natCast]
  exact ENNReal.iSup_natCast

theorem extendedTime_coe {τ : Ω → WithTop ℕ} {ω : Ω} {n : ℕ} (h : τ ω = (WithTop.some n : WithTop ℕ)) :
    extendedTime τ ω = (n : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro N
    simp only [truncatedTime, h, ← WithTop.coe_min, WithTop.untopD_coe,
      ENNReal.ofReal_natCast]
    exact_mod_cast min_le_left n N
  · have hn := le_iSup (fun N : ℕ => ENNReal.ofReal (truncatedTime τ N ω)) n
    simpa only [extendedTime, truncatedTime, h, min_self, WithTop.untopD_coe,
      ENNReal.ofReal_natCast] using hn

theorem measurable_extendedTime {τ : Ω → WithTop ℕ} (hτ : Measurable τ) :
    Measurable (extendedTime τ) :=
  Measurable.iSup fun N : ℕ => (measurable_truncatedTime hτ N).ennreal_ofReal

/-- A uniform bound on truncated expectations proves integrability before
any unbounded stopped identity is used. -/
theorem integrable_time_of_truncated_mean_le [IsFiniteMeasure μ]
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ) {C : ℝ}
    (hbound : ∀ N : ℕ, (∫ ω, truncatedTime τ N ω ∂μ) ≤ C) :
    (∀ᵐ ω ∂μ, τ ω ≠ ⊤) ∧
      Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ ∧
      (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ) ≤ C := by
  have hlin : (∫⁻ ω, extendedTime τ ω ∂μ) ≤ ENNReal.ofReal C := by
    change (∫⁻ ω, ⨆ N : ℕ, ENNReal.ofReal (truncatedTime τ N ω) ∂μ) ≤ ENNReal.ofReal C
    rw [lintegral_iSup
      (fun N : ℕ => (measurable_truncatedTime hτ N).ennreal_ofReal)]
    · apply iSup_le
      intro N
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_truncatedTime hτ N)
        (ae_of_all _ (truncatedTime_nonneg τ N))]
      exact ENNReal.ofReal_le_ofReal (hbound N)
    · intro n m hnm ω
      exact ENNReal.ofReal_le_ofReal (truncatedTime_mono τ ω hnm)
  have hlt : (∫⁻ ω, extendedTime τ ω ∂μ) < ⊤ :=
    hlin.trans_lt ENNReal.ofReal_lt_top
  have hefinite := ae_lt_top (measurable_extendedTime hτ) hlt.ne
  have hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
    filter_upwards [hefinite] with ω hω htop
    rw [extendedTime_top htop] at hω
    exact (lt_irrefl _ hω)
  have heq : (fun ω => (extendedTime τ ω).toReal) =ᵐ[μ]
      (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) := by
    filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    rw [extendedTime_coe hn.symm, ← hn]
    simp only [ENNReal.toReal_natCast, WithTop.untopD_coe]
  have hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ :=
    (integrable_toReal_of_lintegral_ne_top (measurable_extendedTime hτ).aemeasurable
      hlt.ne).congr heq
  refine ⟨hfinite, hi, ?_⟩
  have hnonneg : 0 ≤ ∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ :=
    integral_nonneg fun _ => Nat.cast_nonneg _
  have hC : 0 ≤ C := (integral_nonneg (truncatedTime_nonneg τ 0)).trans (hbound 0)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => Nat.cast_nonneg _)]
  convert hlin using 1
  apply lintegral_congr_ae
  filter_upwards [hfinite] with ω hω
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  rw [extendedTime_coe hn.symm, ← hn]
  simp only [WithTop.untopD_coe, ENNReal.ofReal_natCast]

theorem truncatedTime_eventually_eq {τ : Ω → WithTop ℕ} {ω : Ω}
    (hfinite : τ ω ≠ ⊤) :
    ∀ᶠ N in atTop, truncatedTime τ N ω = (((τ ω).untopD 0 : ℕ) : ℝ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [truncatedTime, ← hn]
  simp only [← WithTop.coe_min, WithTop.untopD_coe, min_eq_left hN]

theorem truncatedTime_integral_tendsto [IsFiniteMeasure μ]
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hi : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ) :
    Tendsto (fun N : ℕ => ∫ ω, truncatedTime τ N ω ∂μ) atTop
      (𝓝 (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ)) := by
  apply integral_tendsto_of_tendsto_of_monotone
    (integrable_truncatedTime hτ) hi
    (ae_of_all _ (truncatedTime_mono τ))
  filter_upwards [hfinite] with ω hω
  have heq : (fun N : ℕ => truncatedTime τ N ω) =ᶠ[atTop]
      (fun _ => (((τ ω).untopD 0 : ℕ) : ℝ)) := truncatedTime_eventually_eq hω
  exact tendsto_const_nhds.congr' heq.symm

/-- Removing a bounded truncation from a stopped observable after
finiteness has already been established. -/
theorem integral_stopped_truncation_tendsto [IsFiniteMeasure μ]
    {τ : Ω → WithTop ℕ} (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (W : ℕ → Ω → ℝ) {B : ℝ}
    (hW : ∀ N : ℕ, AEStronglyMeasurable
      (fun ω => W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω) μ)
    (hbound : ∀ N : ℕ, ∀ᵐ ω ∂μ,
      ‖W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫ ω, W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω ∂μ)
      atTop (𝓝 (∫ ω, W ((τ ω).untopD 0) ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B) hW (integrable_const B) hbound
  filter_upwards [hfinite] with ω hω
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [← hn]
  simp only [← WithTop.coe_min, WithTop.untopD_coe, min_eq_left hN]

/-- Positive drift and bounded truncated stopped coordinates first imply
finite mean time; dominated convergence then gives the exact unbounded
stopped mean. No finiteness assumption is used in the first step. -/
theorem finite_mean_and_stopped_identity [IsProbabilityMeasure μ]
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ) (W : ℕ → Ω → ℝ)
    {B c w₀ : ℝ} (hc : 0 < c)
    (hW : ∀ N : ℕ, AEStronglyMeasurable
      (fun ω => W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω) μ)
    (hbound : ∀ N : ℕ, ∀ᵐ ω ∂μ,
      ‖W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω‖ ≤ B)
    (hdrift : ∀ N : ℕ, c * (∫ ω, truncatedTime τ N ω ∂μ) =
      (∫ ω, W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω ∂μ) - w₀) :
    (∀ᵐ ω ∂μ, τ ω ≠ ⊤) ∧
      Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ ∧
      c * (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ) =
        (∫ ω, W ((τ ω).untopD 0) ω ∂μ) - w₀ := by
  have hWi : ∀ N : ℕ, Integrable
      (fun ω => W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω) μ :=
    fun N : ℕ => (integrable_const B).mono' (hW N) (hbound N)
  have hmean : ∀ N : ℕ, (∫ ω, truncatedTime τ N ω ∂μ) ≤ (B - w₀) / c := by
    intro N
    have hu : (∫ ω, W ((min (τ ω) (WithTop.some N : WithTop ℕ)).untopD 0) ω ∂μ) ≤ B := by
      calc
        _ ≤ ∫ _ω : Ω, B ∂μ := integral_mono_ae (hWi N) (integrable_const B) (by
          filter_upwards [hbound N] with ω hω
          exact (le_abs_self _).trans hω)
        _ = B := by simp
    apply (le_div_iff₀ hc).mpr
    linarith [hdrift N]
  obtain ⟨hfinite, hi, _⟩ := integrable_time_of_truncated_mean_le hτ hmean
  refine ⟨hfinite, hi, ?_⟩
  have hleft := (truncatedTime_integral_tendsto hτ hfinite hi).const_mul c
  have hright := (integral_stopped_truncation_tendsto hfinite W hW hbound).sub_const w₀
  exact tendsto_nhds_unique hleft (hright.congr (fun N : ℕ => (hdrift N).symm))

end Occupation
end FixedCouplingPoisson
