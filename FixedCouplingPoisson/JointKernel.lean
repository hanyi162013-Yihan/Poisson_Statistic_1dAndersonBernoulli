import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite block kernels and backward error budgets

The results here are general finite-product and conditional-expectation lemmas.
Their kernel hypotheses are explicit assumptions of these general lemmas. This
module does not assert that a Schrödinger phase process satisfies those kernel
hypotheses, and does not assert any joint Poisson limit.

Blocks are indexed by `0, …, m-1`; `prefixProduct Ψ b` contains exactly the past
blocks `0, …, b-1`. No independence of the good-start events is required.
-/

open MeasureTheory
open scoped BigOperators

namespace FixedCouplingPoisson

/-- The product of the first `b` block factors. -/
noncomputable def prefixProduct {Ω : Type*} (Ψ : ℕ → Ω → ℝ) (b : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range b, Ψ j ω

@[simp] theorem prefixProduct_zero {Ω : Type*} (Ψ : ℕ → Ω → ℝ) (ω : Ω) :
    prefixProduct Ψ 0 ω = 1 := by simp [prefixProduct]

@[simp] theorem prefixProduct_succ {Ω : Type*} (Ψ : ℕ → Ω → ℝ) (b : ℕ) (ω : Ω) :
    prefixProduct Ψ (b + 1) ω = prefixProduct Ψ b ω * Ψ b ω := by
  simp [prefixProduct, Finset.prod_range_succ]

/-- Exact finite backward telescoping, with no limit or probabilistic input. -/
theorem backward_telescope (F : ℕ → ℝ) (a : ℝ) (m : ℕ) :
    F m - a ^ m * F 0 =
      ∑ b ∈ Finset.range m, a ^ (m - 1 - b) * (F (b + 1) - a * F b) := by
  calc
    F m - a ^ m * F 0 =
        ∑ b ∈ Finset.range m,
          (a ^ (m - (b + 1)) * F (b + 1) - a ^ (m - b) * F b) := by
      simpa only [Nat.sub_self, pow_zero, one_mul, Nat.sub_zero] using
        (Finset.sum_range_sub (fun b ↦ a ^ (m - b) * F b) m).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbm : b < m := Finset.mem_range.mp hb
      have hleft : m - (b + 1) = m - 1 - b := by omega
      have hright : m - b = (m - 1 - b) + 1 := by omega
      rw [hleft, hright, pow_succ]
      ring

/-- Deterministic accumulation of one-step replacement errors. -/
theorem backward_error_budget (F : ℕ → ℝ) (a : ℝ) (m : ℕ) (ε : ℕ → ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hε : ∀ b < m, |F (b + 1) - a * F b| ≤ ε b) :
    |F m - a ^ m * F 0| ≤ ∑ b ∈ Finset.range m, ε b := by
  rw [backward_telescope]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  have hp0 : 0 ≤ a ^ (m - 1 - b) := pow_nonneg ha0 _
  have hp1 : a ^ (m - 1 - b) ≤ 1 := pow_le_one₀ ha0 ha1
  calc
    |a ^ (m - 1 - b) * (F (b + 1) - a * F b)| =
        a ^ (m - 1 - b) * |F (b + 1) - a * F b| := by
      rw [abs_mul, abs_of_nonneg hp0]
    _ ≤ |F (b + 1) - a * F b| :=
      mul_le_of_le_one_left (abs_nonneg _) hp1
    _ ≤ ε b := hε b (Finset.mem_range.mp hb)

section Probability

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Pointwise bounded block factors give bounded past products. -/
theorem prefixProduct_bounds (Ψ : ℕ → Ω → ℝ)
    (hΨ : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1) (b : ℕ) (ω : Ω) :
    0 ≤ prefixProduct Ψ b ω ∧ prefixProduct Ψ b ω ≤ 1 := by
  exact ⟨Finset.prod_nonneg fun j _ ↦ (hΨ j ω).1,
    Finset.prod_le_one (fun j _ ↦ (hΨ j ω).1) (fun j _ ↦ (hΨ j ω).2)⟩

theorem prefixProduct_stronglyMeasurable (Ψ : ℕ → Ω → ℝ)
    (hΨ : ∀ b, StronglyMeasurable (Ψ b)) (b : ℕ) :
    StronglyMeasurable (prefixProduct Ψ b) := by
  exact (Finset.range b).stronglyMeasurable_fun_prod fun j _ ↦ hΨ j

theorem prefixProduct_norm_le_one (Ψ : ℕ → Ω → ℝ)
    (hΨ : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1) (b : ℕ) (ω : Ω) :
    ‖prefixProduct Ψ b ω‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (prefixProduct_bounds Ψ hΨ b ω).1]
  exact (prefixProduct_bounds Ψ hΨ b ω).2

theorem bounded_block_integrable [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : StronglyMeasurable f) (hbound : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all μ fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1]
    exact (hbound ω).2

theorem prefixProduct_integrable [IsFiniteMeasure μ] (Ψ : ℕ → Ω → ℝ)
    (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1) (b : ℕ) :
    Integrable (prefixProduct Ψ b) μ :=
  bounded_block_integrable (prefixProduct_stronglyMeasurable Ψ hmeas b)
    (prefixProduct_bounds Ψ hbound b)

/-- A measurable good event gives an unconditional integral budget; no
conditioning on an intersection of good events is used. -/
theorem good_bad_integral_budget [IsProbabilityMeasure μ] {f : Ω → ℝ}
    {G : Set Ω} {δ B : ℝ} (hf : Integrable f μ) (hG : MeasurableSet G)
    (hδ : 0 ≤ δ) (hglobal : ∀ᵐ ω ∂μ, |f ω| ≤ B)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ G → |f ω| ≤ δ) :
    |∫ ω, f ω ∂μ| ≤ δ + B * μ.real Gᶜ := by
  have hi : Integrable (Gᶜ.indicator (fun _ : Ω ↦ B)) μ :=
    (integrable_const B).indicator hG.compl
  have hdom : ∀ᵐ ω ∂μ, |f ω| ≤ δ + Gᶜ.indicator (fun _ : Ω ↦ B) ω := by
    filter_upwards [hglobal, hgood] with ω hω hωgood
    by_cases hωG : ω ∈ G
    · simpa [Set.indicator_of_notMem, hωG] using hωgood hωG
    · simpa [Set.indicator_of_mem, hωG] using (hω.trans (by linarith : B ≤ δ + B))
  calc
    |∫ ω, f ω ∂μ| ≤ ∫ ω, |f ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (δ + Gᶜ.indicator (fun _ : Ω ↦ B) ω) ∂μ :=
      integral_mono_ae hf.abs ((integrable_const δ).add hi) hdom
    _ = δ + B * μ.real Gᶜ := by
      rw [integral_add (integrable_const δ) hi, integral_indicator_const B hG.compl]
      simp [integral_const, smul_eq_mul, mul_comm]

/-- Conditional expectation retains `[0,1]` bounds almost everywhere. -/
theorem condExp_block_bounds [IsFiniteMeasure μ] {M : MeasurableSpace Ω} (hM : M ≤ m₀)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m₀] f)
    (hbound : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) :
    ∀ᵐ ω ∂μ, 0 ≤ (μ[f | M]) ω ∧ (μ[f | M]) ω ≤ 1 := by
  letI : MeasurableSpace Ω := m₀
  have hnonneg : 0 ≤ᵐ[μ] μ[f | M] :=
    condExp_nonneg (m := M) (ae_of_all μ fun ω ↦ (hbound ω).1)
  have hle : μ[f | M] ≤ᵐ[μ] μ[fun _ : Ω ↦ (1 : ℝ) | M] :=
    condExp_mono (m := M) (μ := μ) (bounded_block_integrable hf hbound)
    (integrable_const (1 : ℝ)) (ae_of_all μ fun ω ↦ (hbound ω).2)
  rw [condExp_const hM] at hle
  filter_upwards [hnonneg, hle] with ω hω0 hω1
  exact ⟨hω0, hω1⟩

/-- Exact one-block conditional replacement inside a past product. -/
theorem integral_prefix_condExp_deviation [IsProbabilityMeasure μ]
    (Ψ : ℕ → Ω → ℝ) (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1)
    {M : MeasurableSpace Ω} (hM : M ≤ m₀) (b : ℕ)
    (hpast : StronglyMeasurable[M] (prefixProduct Ψ b)) (a : ℝ) :
    (∫ ω, prefixProduct Ψ (b + 1) ω ∂μ) - a * (∫ ω, prefixProduct Ψ b ω ∂μ) =
      ∫ ω, prefixProduct Ψ b ω * ((μ[Ψ b | M]) ω - a) ∂μ := by
  letI : MeasurableSpace Ω := m₀
  have hpint := prefixProduct_integrable (μ := μ) Ψ hmeas hbound b
  have hΨint := bounded_block_integrable (μ := μ) (hmeas b) (hbound b)
  have hfg : Integrable (prefixProduct Ψ b * Ψ b) μ := by
    convert prefixProduct_integrable (μ := μ) Ψ hmeas hbound (b + 1) using 1
    funext ω
    exact (prefixProduct_succ Ψ b ω).symm
  have hraw : Integrable (fun ω ↦ prefixProduct Ψ b ω * (μ[Ψ b | M]) ω) μ :=
    integrable_condExp.bdd_mul (prefixProduct_stronglyMeasurable Ψ hmeas b).aestronglyMeasurable
      (ae_of_all μ (prefixProduct_norm_le_one Ψ hbound b))
  have hpull : (∫ ω, prefixProduct Ψ b ω * (μ[Ψ b | M]) ω ∂μ) =
      ∫ ω, prefixProduct Ψ b ω * Ψ b ω ∂μ := by
    calc
      _ = ∫ ω, (μ[prefixProduct Ψ b * Ψ b | M]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hpast hfg hΨint).symm
      _ = _ := integral_condExp hM
  have hsplit : (fun ω ↦ prefixProduct Ψ b ω * ((μ[Ψ b | M]) ω - a)) =
      fun ω ↦ prefixProduct Ψ b ω * (μ[Ψ b | M]) ω - prefixProduct Ψ b ω * a := by
    funext ω
    ring
  rw [hsplit, integral_sub hraw (hpint.mul_const a), integral_mul_const, hpull]
  simp only [prefixProduct_succ]
  ring

/-- Multiplication by a bounded nonnegative past product cannot enlarge an
absolute one-step error. -/
theorem prefixProduct_mul_abs_le (Ψ : ℕ → Ω → ℝ)
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1) (b : ℕ) (ω : Ω) (z : ℝ) :
    |prefixProduct Ψ b ω * z| ≤ |z| := by
  rw [abs_mul]
  have hp : |prefixProduct Ψ b ω| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using prefixProduct_norm_le_one Ψ hbound b ω
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (abs_nonneg z)

/-- The exact backward identity with actual conditional expectations. The only
past information used is measurability of the earlier product. -/
theorem conditional_backward_telescope [IsProbabilityMeasure μ]
    (Ψ : ℕ → Ω → ℝ) (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1)
    (M : ℕ → MeasurableSpace Ω) (m : ℕ) (hM : ∀ b < m, M b ≤ m₀)
    (hpast : ∀ b < m, StronglyMeasurable[M b] (prefixProduct Ψ b)) (a : ℝ) :
    (∫ ω, prefixProduct Ψ m ω ∂μ) - a ^ m =
      ∑ b ∈ Finset.range m, a ^ (m - 1 - b) *
        (∫ ω, prefixProduct Ψ b ω * ((μ[Ψ b | M b]) ω - a) ∂μ) := by
  have hzero : (∫ ω, prefixProduct Ψ 0 ω ∂μ) = 1 := by simp
  calc
    _ = ∑ b ∈ Finset.range m, a ^ (m - 1 - b) *
        ((∫ ω, prefixProduct Ψ (b + 1) ω ∂μ) -
          a * (∫ ω, prefixProduct Ψ b ω ∂μ)) := by
      simpa only [hzero, mul_one] using
        backward_telescope (fun b ↦ ∫ ω, prefixProduct Ψ b ω ∂μ) a m
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [integral_prefix_condExp_deviation Ψ hmeas hbound
        (hM b (Finset.mem_range.mp hb)) b (hpast b (Finset.mem_range.mp hb))]

/-- One true conditional kernel estimate gives a deterministic-error plus
bad-start-probability budget. The estimate is never conditioned on `G` itself. -/
theorem conditional_one_step_budget [IsProbabilityMeasure μ]
    (Ψ : ℕ → Ω → ℝ) (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1)
    {M : MeasurableSpace Ω} (hM : M ≤ m₀) (b : ℕ)
    (hpast : StronglyMeasurable[M] (prefixProduct Ψ b))
    {a δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hδ : 0 ≤ δ)
    {G : Set Ω} (hG : MeasurableSet[m₀] G)
    (hkernel : ∀ᵐ ω ∂μ, ω ∈ G → |(μ[Ψ b | M]) ω - a| ≤ δ) :
    |(∫ ω, prefixProduct Ψ (b + 1) ω ∂μ) -
      a * (∫ ω, prefixProduct Ψ b ω ∂μ)| ≤ δ + 2 * μ.real Gᶜ := by
  letI : MeasurableSpace Ω := m₀
  rw [integral_prefix_condExp_deviation Ψ hmeas hbound hM b hpast]
  have hf : Integrable (fun ω ↦ prefixProduct Ψ b ω * ((μ[Ψ b | M]) ω - a)) μ :=
    (integrable_condExp.sub (integrable_const a)).bdd_mul
      (prefixProduct_stronglyMeasurable Ψ hmeas b).aestronglyMeasurable
      (ae_of_all μ (prefixProduct_norm_le_one Ψ hbound b))
  apply good_bad_integral_budget hf hG hδ
  · filter_upwards [condExp_block_bounds (μ := μ) hM (hmeas b) (hbound b)] with ω hω
    apply (prefixProduct_mul_abs_le Ψ hbound b ω _).trans
    rw [abs_le]
    constructor <;> linarith [hω.1, hω.2]
  · filter_upwards [hkernel] with ω hω hωG
    exact (prefixProduct_mul_abs_le Ψ hbound b ω _).trans (hω hωG)

/-- Finite conditional block errors accumulate with no assumption of independence
of the good-start events. This is the general error-budget statement used by the
manuscript; the Schrödinger-specific conditional kernel bounds remain separate
mathematical obligations. -/
theorem conditional_backward_error_budget [IsProbabilityMeasure μ]
    (Ψ : ℕ → Ω → ℝ) (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1)
    (M : ℕ → MeasurableSpace Ω) (m : ℕ) (hM : ∀ b < m, M b ≤ m₀)
    (hpast : ∀ b < m, StronglyMeasurable[M b] (prefixProduct Ψ b))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (G : ℕ → Set Ω) (hG : ∀ b < m, MeasurableSet (G b))
    (δ : ℕ → ℝ) (hδ : ∀ b < m, 0 ≤ δ b)
    (hkernel : ∀ b < m, ∀ᵐ ω ∂μ, ω ∈ G b → |(μ[Ψ b | M b]) ω - a| ≤ δ b) :
    |(∫ ω, prefixProduct Ψ m ω ∂μ) - a ^ m| ≤
      (∑ b ∈ Finset.range m, δ b) + 2 * ∑ b ∈ Finset.range m, μ.real (G b)ᶜ := by
  have hstep (b : ℕ) (hb : b < m) :
      |(∫ ω, prefixProduct Ψ (b + 1) ω ∂μ) -
        a * (∫ ω, prefixProduct Ψ b ω ∂μ)| ≤ δ b + 2 * μ.real (G b)ᶜ :=
    conditional_one_step_budget Ψ hmeas hbound (hM b hb) b (hpast b hb)
      ha0 ha1 (hδ b hb) (hG b hb) (hkernel b hb)
  have hbudget := backward_error_budget
    (fun b ↦ ∫ ω, prefixProduct Ψ b ω ∂μ) a m
    (fun b ↦ δ b + 2 * μ.real (G b)ᶜ) ha0 ha1 hstep
  have hzero : (∫ ω, prefixProduct Ψ 0 ω ∂μ) = 1 := by simp
  simpa only [hzero, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum] using hbudget

/-- Uniform per-block deterministic errors give the usual `m δ` budget. -/
theorem conditional_backward_uniform_budget [IsProbabilityMeasure μ]
    (Ψ : ℕ → Ω → ℝ) (hmeas : ∀ b, StronglyMeasurable (Ψ b))
    (hbound : ∀ b ω, 0 ≤ Ψ b ω ∧ Ψ b ω ≤ 1)
    (M : ℕ → MeasurableSpace Ω) (m : ℕ) (hM : ∀ b < m, M b ≤ m₀)
    (hpast : ∀ b < m, StronglyMeasurable[M b] (prefixProduct Ψ b))
    {a δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hδ : 0 ≤ δ)
    (G : ℕ → Set Ω) (hG : ∀ b < m, MeasurableSet (G b))
    (hkernel : ∀ b < m, ∀ᵐ ω ∂μ, ω ∈ G b → |(μ[Ψ b | M b]) ω - a| ≤ δ) :
    |(∫ ω, prefixProduct Ψ m ω ∂μ) - a ^ m| ≤
      (m : ℝ) * δ + 2 * ∑ b ∈ Finset.range m, μ.real (G b)ᶜ := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    conditional_backward_error_budget Ψ hmeas hbound M m hM hpast ha0 ha1
      G hG (fun _ ↦ δ) (fun _ _ ↦ hδ) hkernel

end Probability

end FixedCouplingPoisson
