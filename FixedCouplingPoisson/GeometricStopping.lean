import FixedCouplingPoisson.StoppingLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope


/-! Factored proof group: GeometricLaplace. -/

/-! Geometric discount removes the exponential Taylor remainder from
the affine exit argument. Conversion to the ordinary Laplace transform uses
only the displayed first-moment hypothesis. Model stopping-time estimates
are supplied separately. -/
noncomputable section
namespace FixedCouplingPoisson.Occupation
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

/-- The exact affine increment under a geometric discount. Its random
version is obtained from the already proved constant conditional drift. -/
theorem geometric_affine_increment (ρ q c w : ℝ) (n : ℕ)
    (hρ : ρ * (1 + q * c) = 1) :
    ρ ^ (n + 1) * (1 + q * (w + c)) - ρ ^ n * (1 + q * w) =
      -(q ^ 2 * c) * ρ ^ (n + 1) * w := by
  have hpow : ρ ^ n = ρ ^ (n + 1) * (1 + q * c) := by
    rw [pow_succ, mul_assoc, hρ, mul_one]
  rw [hpow]
  ring

theorem geometric_discount_bounds {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    0 ≤ (1 + q * c)⁻¹ ∧ (1 + q * c)⁻¹ ≤ 1 := by
  have hden : 0 < 1 + q * c := by positivity
  refine ⟨(inv_pos.mpr hden).le, ?_⟩
  exact (inv_le_one₀ hden).mpr (le_add_of_nonneg_right (mul_nonneg hq hc))

theorem geometric_discount_relation {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    (1 + q * c)⁻¹ * (1 + q * c) = 1 :=
  inv_mul_cancel₀ (ne_of_gt (by positivity : 0 < 1 + q * c))

/-- On the negative half-line the exponential has Lipschitz constant
one. This elementary estimate avoids a second moment in the conversion. -/
theorem exp_sub_exp_le_sub_of_nonpos {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 0) :
    Real.exp v - Real.exp u ≤ v - u := by
  have hratio : Real.exp (u - v) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr huv)
  have hratio0 : 0 ≤ 1 - Real.exp (u - v) := sub_nonneg.mpr hratio
  have hratio1 : 1 - Real.exp (u - v) ≤ v - u := by
    linarith [Real.add_one_le_exp (u - v)]
  have hvexp : Real.exp v ≤ 1 := Real.exp_le_one_iff.mpr hv
  calc
    _ = Real.exp v * (1 - Real.exp (u - v)) := by
      have heq : Real.exp v * Real.exp (u - v) = Real.exp u := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [mul_sub, mul_one, heq]
    _ ≤ 1 * (v - u) := mul_le_mul hvexp hratio1 hratio0 (by norm_num)
    _ = _ := one_mul _

theorem abs_exp_sub_exp_le_of_nonpos {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp u - Real.exp v| ≤ |u - v| := by
  by_cases huv : u ≤ v
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr huv)),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    linarith [exp_sub_exp_le_sub_of_nonpos huv hv]
  · have hvu : v ≤ u := le_of_not_ge huv
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hvu)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact exp_sub_exp_le_sub_of_nonpos hvu hu

theorem geometric_rate_tendsto (q : ℝ) :
    Tendsto (fun c : ℝ => Real.log (1 + q * c) / c) (𝓝[>] 0) (𝓝 q) := by
  have hmul : HasDerivAt (fun c : ℝ => q * c) q 0 := hasDerivAt_const_mul q
  have harg : HasDerivAt (fun c : ℝ => 1 + q * c) q 0 := hmul.const_add 1
  have hlog : HasDerivAt (fun c : ℝ => Real.log (1 + q * c)) q 0 := by
    simpa only [mul_zero, add_zero, div_one] using
      harg.log (by norm_num : 1 + q * (0 : ℝ) ≠ 0)
  have h := hlog.tendsto_slope_zero_right
  simpa only [zero_add, mul_zero, add_zero, Real.log_one, sub_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem geometric_rate_bounds {q c : ℝ} (hq : 0 ≤ q) (hc : 0 < c) :
    0 ≤ Real.log (1 + q * c) / c ∧ Real.log (1 + q * c) / c ≤ q := by
  have hqc : 0 ≤ q * c := mul_nonneg hq hc.le
  have hden : 0 < 1 + q * c := by positivity
  refine ⟨div_nonneg (Real.log_nonneg (le_add_of_nonneg_right hqc)) hc.le, ?_⟩
  apply (div_le_iff₀ hc).mpr
  linarith [Real.log_le_sub_one_of_pos hden]

theorem geometric_discount_eq_exp {q c : ℝ} (hq : 0 ≤ q) (hc : 0 < c) (n : ℕ) :
    ((1 + q * c)⁻¹) ^ n =
      Real.exp (-(Real.log (1 + q * c) / c) * (c * (n : ℝ))) := by
  have hden : 0 < 1 + q * c := by positivity
  have heq : -(Real.log (1 + q * c) / c) * (c * (n : ℝ)) =
      (n : ℝ) * (-Real.log (1 + q * c)) := by
    field_simp [hc.ne']
  rw [heq, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hden]

section FirstMoment
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_negative_exp {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun ω => Real.exp (-a * Y ω)) μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    (Real.continuous_exp.measurable.comp (hY.const_mul (-a))).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖Real.exp (-a * Y ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (hY0 ω))

/-- Ordinary Laplace transforms are Lipschitz in the parameter with
constant `E Y`. This is enough for geometrically discounted exit laws. -/
theorem first_moment_laplace_lipschitz {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hiY : Integrable Y μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(∫ ω, Real.exp (-a * Y ω) ∂μ) - (∫ ω, Real.exp (-b * Y ω) ∂μ)| ≤
      |a - b| * (∫ ω, Y ω ∂μ) := by
  have hia := integrable_negative_exp (μ := μ) hY hY0 ha
  have hib := integrable_negative_exp (μ := μ) hY hY0 hb
  rw [← integral_sub hia hib, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ ω, ‖Real.exp (-a * Y ω) - Real.exp (-b * Y ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |a - b| * Y ω ∂μ :=
      integral_mono_ae (hia.sub hib).norm (hiY.const_mul |a - b|) (ae_of_all _ fun ω => by
        change ‖Real.exp (-a * Y ω) - Real.exp (-b * Y ω)‖ ≤ |a - b| * Y ω
        rw [Real.norm_eq_abs]
        have h := abs_exp_sub_exp_le_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (hY0 ω))
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (hY0 ω))
        have heq : -a * Y ω - -b * Y ω = -(a - b) * Y ω := by ring
        simpa only [heq, abs_mul, abs_neg, abs_of_nonneg (hY0 ω)] using h)
    _ = _ := integral_const_mul _ _

/-- Conversion of the exact geometric discount to the ordinary Laplace
transform costs only the uniform scaled first moment. -/
theorem geometric_laplace_conversion {τ : Ω → ℕ} (hτ : Measurable τ)
    (hiτ : Integrable (fun ω => (τ ω : ℝ)) μ)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 < c) :
    |(∫ ω, ((1 + q * c)⁻¹) ^ τ ω ∂μ) -
      (∫ ω, Real.exp (-q * (c * (τ ω : ℝ))) ∂μ)| ≤
        (q - Real.log (1 + q * c) / c) *
          (c * (∫ ω, (τ ω : ℝ) ∂μ)) := by
  let Y := fun ω => c * (τ ω : ℝ)
  have hYm : Measurable Y :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hτ).const_mul c
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => mul_nonneg hc.le (Nat.cast_nonneg _)
  have hiY : Integrable Y μ := hiτ.const_mul c
  have hrate := geometric_rate_bounds hq hc
  have h := first_moment_laplace_lipschitz (μ := μ) hYm hY0 hiY hrate.1 hq
  have heq : (fun ω => Real.exp (-(Real.log (1 + q * c) / c) * Y ω)) =
      (fun ω => ((1 + q * c)⁻¹) ^ τ ω) := by
    funext ω
    exact (geometric_discount_eq_exp hq hc (τ ω)).symm
  rw [heq] at h
  have hrateabs : |Real.log (1 + q * c) / c - q| =
      q - Real.log (1 + q * c) / c := by
    rw [abs_of_nonpos (sub_nonpos.mpr hrate.2)]
    ring
  rw [hrateabs] at h
  simpa only [Y, integral_const_mul] using h

end FirstMoment
end FixedCouplingPoisson.Occupation

/-! Factored proof group: GeometricStopping. -/

/-! Exact bounded stopping for geometrically discounted affine coordinates.
The input is an explicit genuine constant conditional drift; its actual
CDF-process specialization is established separately. -/
noncomputable section
namespace FixedCouplingPoisson.Occupation
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

def geometricAffineProcess (ρ q : ℝ) (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ρ ^ n * (1 + q * W n ω)

theorem integrable_geometricAffineProcess (ρ q : ℝ) (W : ℕ → Ω → ℝ)
    (hW : ∀ n, Integrable (W n) μ) (n : ℕ) :
    Integrable (geometricAffineProcess ρ q W n) μ :=
  ((integrable_const (μ := μ) (1 : ℝ)).add ((hW n).const_mul q)).const_mul (ρ ^ n)

theorem geometricAffineProcess_conditional_drift
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ n, F n ≤ m₀)
    (W : ℕ → Ω → ℝ) (hW : ∀ n, Integrable (W n) μ)
    (ρ q c : ℝ) (hρ : ρ * (1 + q * c) = 1) (n : ℕ)
    (hdrift : ∀ᵐ ω ∂μ, (μ[W (n + 1) | F n]) ω - W n ω = c) :
    ∀ᵐ ω ∂μ,
      (μ[geometricAffineProcess ρ q W (n + 1) | F n]) ω -
        geometricAffineProcess ρ q W n ω = -(q ^ 2 * c) * ρ ^ (n + 1) * W n ω := by
  have hs := condExp_smul (μ := μ) (ρ ^ (n + 1))
    (fun ω => 1 + q * W (n + 1) ω) (F n)
  have ha := condExp_add (integrable_const (μ := μ) (1 : ℝ))
    ((hW (n + 1)).const_mul q) (F n)
  have hq := condExp_smul (μ := μ) q (W (n + 1)) (F n)
  filter_upwards [hs, ha, hq, hdrift] with ω hsω haω hqω hdω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, condExp_const (hF n)] at hsω haω hqω
  change (μ[fun η => 1 + q * W (n + 1) η | F n]) ω =
    1 + (μ[fun η => q * W (n + 1) η | F n]) ω at haω
  change (μ[fun η => q * W (n + 1) η | F n]) ω =
    q * (μ[W (n + 1) | F n]) ω at hqω
  have hcond : (μ[geometricAffineProcess ρ q W (n + 1) | F n]) ω =
      ρ ^ (n + 1) * (1 + q * (μ[W (n + 1) | F n]) ω) := by
    calc
      _ = ρ ^ (n + 1) *
          (μ[fun η => 1 + q * W (n + 1) η | F n]) ω := hsω
      _ = _ := by rw [haω, hqω]
  have hnext : (μ[W (n + 1) | F n]) ω = W n ω + c := by linarith
  change (μ[geometricAffineProcess ρ q W (n + 1) | F n]) ω -
    ρ ^ n * (1 + q * W n ω) = _
  rw [hcond, hnext]
  exact geometric_affine_increment ρ q c (W n ω) n hρ

theorem integrable_geometricAffineProcess_stopped
    (ρ q : ℝ) (W : ℕ → Ω → ℝ) {τ : Ω → ℕ}
    (hτ : Measurable τ) (hWτ : Integrable (fun ω => W (τ ω) ω) μ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun ω => geometricAffineProcess ρ q W (τ ω) ω) μ := by
  have hweight : Measurable (fun ω => ρ ^ τ ω) :=
    (measurable_of_countable (fun n : ℕ => ρ ^ n)).comp hτ
  have hbound : ∀ᵐ ω ∂μ, ‖ρ ^ τ ω‖ ≤ (1 : ℝ) := ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ0 _)]
    exact pow_le_one₀ hρ0 hρ1
  exact ((integrable_const (μ := μ) (1 : ℝ)).add (hWτ.const_mul q)).bdd_mul
    hweight.aestronglyMeasurable hbound

/-- No exponential Taylor estimate is used: the geometric affine error
is exactly a discounted occupation of the original drift coordinate. -/
theorem bounded_stopped_geometric_affine_identity
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ n, F n ≤ m₀)
    (τ : Ω → ℕ) (hτm : Measurable τ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet[F j] {ω | j < τ ω})
    (W : ℕ → Ω → ℝ) (hW : ∀ n, Integrable (W n) μ)
    (hWτ : Integrable (fun ω => W (τ ω) ω) μ)
    (ρ q c : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : ρ * (1 + q * c) = 1)
    (hdrift : ∀ j < N, ∀ᵐ ω ∂μ, (μ[W (j + 1) | F j]) ω - W j ω = c) :
    (∫ ω, ρ ^ τ ω * (1 + q * W (τ ω) ω) ∂μ) -
        (∫ ω, 1 + q * W 0 ω ∂μ) =
      -(q ^ 2 * c) * (∫ ω, ∑ j ∈ Finset.range (τ ω), ρ ^ (j + 1) * W j ω ∂μ) := by
  let V := geometricAffineProcess ρ q W
  have hV : ∀ j, Integrable (V j) μ := integrable_geometricAffineProcess ρ q W hW
  have hVτ : Integrable (fun ω => V (τ ω) ω) μ :=
    integrable_geometricAffineProcess_stopped ρ q W hτm hWτ hρ0 hρ1
  have hstep : ∀ j < N,
      (∫ ω in {ω | j < τ ω}, V (j + 1) ω - V j ω ∂μ) =
        ∫ ω in {ω | j < τ ω}, -(q ^ 2 * c) * ρ ^ (j + 1) * W j ω ∂μ := by
    intro j hj
    have heq :
        (∫ ω in {ω | j < τ ω}, (μ[V (j + 1) | F j]) ω - V j ω ∂μ) =
          ∫ ω in {ω | j < τ ω}, -(q ^ 2 * c) * ρ ^ (j + 1) * W j ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae
        (geometricAffineProcess_conditional_drift F hF W hW ρ q c hρ j (hdrift j hj)))
    rw [integral_sub integrable_condExp.integrableOn (hV j).integrableOn,
      setIntegral_condExp (hF j) (hV (j + 1)) (hA j),
      ← integral_sub (hV (j + 1)).integrableOn (hV j).integrableOn] at heq
    exact heq
  have hsum := Finset.sum_congr rfl (fun j (hj : j ∈ Finset.range N) =>
    hstep j (Finset.mem_range.mp hj))
  rw [sum_setIntegral_stopped_increment τ N hτ (fun j => hF j _ (hA j)) V hV hVτ,
    sum_setIntegral_before_stopping τ N hτ (fun j => hF j _ (hA j))
      (fun j ω => -(q ^ 2 * c) * ρ ^ (j + 1) * W j ω)
      (fun j => (hW j).const_mul (-(q ^ 2 * c) * ρ ^ (j + 1)))] at hsum
  simpa only [V, geometricAffineProcess, pow_zero, one_mul, mul_assoc,
    ← Finset.mul_sum, integral_const_mul] using hsum

end FixedCouplingPoisson.Occupation
