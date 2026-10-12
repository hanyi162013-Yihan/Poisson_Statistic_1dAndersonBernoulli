import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite-block Lyapunov correctors and finite occupation budgets

The algebra below proves the finite-sum corrector construction used in the
manuscript: `V = ∑ j < L, Q^j f` and `QV - V = Q^L f - f`.

`Q` is an explicitly supplied real-linear operator on real-valued functions.
The pointwise block contraction, order preservation, and preservation of the
constant function are hypotheses of the generic lemmas, not claims already
proved for the random Schrödinger pair kernel.  The finite-time drift budget is
also generic.  Constructing that kernel and establishing the manuscript's
probabilistic drift for it remain separate specialization tasks.
-/

open scoped BigOperators

namespace FixedCouplingPoisson
namespace Occupation

variable {X : Type*}

/-- The corrector telescope in an arbitrary real module.  This version can
be used on a space of bounded continuous functions, where a Markov integral
is linear; no linearity on nonmeasurable or nonintegrable functions is needed. -/
theorem linear_corrector_drift_identity {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (Q : Module.End ℝ Y) (L : ℕ) (f : Y) :
    Q (∑ j ∈ Finset.range L, (Q ^ j) f) -
        (∑ j ∈ Finset.range L, (Q ^ j) f) = (Q ^ L) f - f := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, map_add, pow_succ']
      change Q (∑ j ∈ Finset.range L, (Q ^ j) f) + Q ((Q ^ L) f) -
        ((∑ j ∈ Finset.range L, (Q ^ j) f) + (Q ^ L) f) = Q ((Q ^ L) f) - f
      rw [add_sub_add_comm, ih, add_comm, sub_add_sub_cancel]

/-- The manuscript's finite-block Lyapunov corrector. -/
def blockPotential (Q : Module.End ℝ (X → ℝ)) (L : ℕ) (f : X → ℝ) : X → ℝ :=
  ∑ j ∈ Finset.range L, (Q ^ j) f

@[simp] theorem blockPotential_zero (Q : Module.End ℝ (X → ℝ)) (f : X → ℝ) :
    blockPotential Q 0 f = 0 := by
  simp [blockPotential]

theorem blockPotential_succ (Q : Module.End ℝ (X → ℝ)) (L : ℕ) (f : X → ℝ) :
    blockPotential Q (L + 1) f = blockPotential Q L f + (Q ^ L) f := by
  simp [blockPotential, Finset.sum_range_succ]

/-- Exact corrector telescope.  There is no positivity or contraction
assumption in this algebraic identity. -/
theorem blockPotential_drift_identity (Q : Module.End ℝ (X → ℝ))
    (L : ℕ) (f : X → ℝ) :
    Q (blockPotential Q L f) - blockPotential Q L f = (Q ^ L) f - f := by
  exact linear_corrector_drift_identity Q L f

/-- A block contraction produces the one-step Lyapunov drift, pointwise.
The additive perturbation `ε` is displayed explicitly. -/
theorem blockPotential_drift_le (Q : Module.End ℝ (X → ℝ))
    (L : ℕ) (f : X → ℝ) (q ε : ℝ)
    (hblock : ∀ x, ((Q ^ L) f) x ≤ q * f x + ε) :
    ∀ x, (Q (blockPotential Q L f)) x - (blockPotential Q L f) x ≤
      -(1 - q) * f x + ε := by
  intro x
  have hid := congrFun (blockPotential_drift_identity Q L f) x
  dsimp at hid
  rw [hid]
  linarith [hblock x]

/-- Order preservation is enough to preserve nonnegativity under iteration. -/
theorem iterate_nonneg (Q : Module.End ℝ (X → ℝ)) (hQ : Monotone Q)
    (f : X → ℝ) (hf : 0 ≤ f) (j : ℕ) : 0 ≤ (Q ^ j) f := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      rw [pow_succ']
      change 0 ≤ Q ((Q ^ j) f)
      simpa only [map_zero] using hQ ih

theorem blockPotential_nonneg (Q : Module.End ℝ (X → ℝ)) (hQ : Monotone Q)
    (f : X → ℝ) (hf : 0 ≤ f) (L : ℕ) : 0 ≤ blockPotential Q L f := by
  exact Finset.sum_nonneg fun j _ => iterate_nonneg Q hQ f hf j

/-- For positive block length and nonnegative `f`, the corrector contains
the zeroth term `f`, so `f ≤ V`. -/
theorem le_blockPotential (Q : Module.End ℝ (X → ℝ)) (hQ : Monotone Q)
    (f : X → ℝ) (hf : 0 ≤ f) {L : ℕ} (hL : 0 < L) :
    f ≤ blockPotential Q L f := by
  unfold blockPotential
  simpa using Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range L) => iterate_nonneg Q hQ f hf j)
    (Finset.mem_range.mpr hL : 0 ∈ Finset.range L)

/-- A positive unital operator preserves the upper bound by one. -/
theorem iterate_le_one (Q : Module.End ℝ (X → ℝ)) (hQ : Monotone Q)
    (hQone : Q (fun _ : X => 1) = fun _ => 1)
    (f : X → ℝ) (hf : f ≤ fun _ => 1) (j : ℕ) :
    (Q ^ j) f ≤ fun _ => 1 := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      rw [pow_succ']
      change Q ((Q ^ j) f) ≤ fun _ => 1
      simpa only [hQone] using hQ ih

/-- The bound `V ≤ L` for the manuscript's observable `0 ≤ f ≤ 1`. -/
theorem blockPotential_le_length (Q : Module.End ℝ (X → ℝ)) (hQ : Monotone Q)
    (hQone : Q (fun _ : X => 1) = fun _ => 1)
    (f : X → ℝ) (hf : f ≤ fun _ => 1) (L : ℕ) :
    ∀ x, blockPotential Q L f x ≤ (L : ℝ) := by
  intro x
  calc
    blockPotential Q L f x = ∑ j ∈ Finset.range L, ((Q ^ j) f) x := by
      simp [blockPotential]
    _ ≤ ∑ _j ∈ Finset.range L, (1 : ℝ) :=
      Finset.sum_le_sum fun j _ => iterate_le_one Q hQ hQone f hf j x
    _ = (L : ℝ) := by simp

/-- A finite real-valued drift inequality telescopes to an occupation budget.
The sequences may later be instantiated by expectations, but no probability
model or conditional expectation is implicit in this theorem. -/
theorem finite_drift_budget (v f : ℕ → ℝ) (a ε : ℝ) (n : ℕ)
    (hdrift : ∀ j < n, v (j + 1) - v j ≤ -a * f j + ε) :
    a * (∑ j ∈ Finset.range n, f j) ≤ v 0 - v n + (n : ℝ) * ε := by
  have hs := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) =>
    hdrift j (Finset.mem_range.mp hj)
  have hv : (∑ j ∈ Finset.range n, (v (j + 1) - v j)) = v n - v 0 := by
    exact Finset.sum_range_sub v n
  rw [hv] at hs
  have hr : (∑ j ∈ Finset.range n, (-a * f j + ε)) =
      -a * (∑ j ∈ Finset.range n, f j) + (n : ℝ) * ε := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [hr] at hs
  linarith

/-- Discarding a nonnegative terminal Lyapunov value gives the usual weaker
finite occupation bound. -/
theorem finite_drift_budget_of_nonneg_terminal (v f : ℕ → ℝ) (a ε : ℝ) (n : ℕ)
    (hdrift : ∀ j < n, v (j + 1) - v j ≤ -a * f j + ε)
    (hterminal : 0 ≤ v n) :
    a * (∑ j ∈ Finset.range n, f j) ≤ v 0 + (n : ℝ) * ε := by
  linarith [finite_drift_budget v f a ε n hdrift]

/-- A bounded deterministic truncation of the increment sum telescopes at the
truncation index.  Its pointwise use underlies bounded random stopping. -/
theorem stopped_increment_sum (v : ℕ → ℝ) {τ n : ℕ} (hτ : τ ≤ n) :
    (∑ j ∈ Finset.range n, if j < τ then v (j + 1) - v j else 0) =
      v τ - v 0 := by
  classical
  calc
    (∑ j ∈ Finset.range n, if j < τ then v (j + 1) - v j else 0) =
        ∑ j ∈ Finset.range τ, if j < τ then v (j + 1) - v j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hτ)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj]
    _ = ∑ j ∈ Finset.range τ, (v (j + 1) - v j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    _ = v τ - v 0 := Finset.sum_range_sub v τ

/-- A stopped finite sum can be padded to any deterministic bound using
past-event indicators. -/
theorem sum_before_stopping (f : ℕ → ℝ) {τ n : ℕ} (hτ : τ ≤ n) :
    (∑ j ∈ Finset.range n, if j < τ then f j else 0) =
      ∑ j ∈ Finset.range τ, f j := by
  classical
  calc
    (∑ j ∈ Finset.range n, if j < τ then f j else 0) =
        ∑ j ∈ Finset.range τ, if j < τ then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hτ)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj]
    _ = ∑ j ∈ Finset.range τ, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

section ConditionalDrift

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}

/-- A genuine conditional-expectation drift inequality can be integrated on
any event measurable with respect to the conditioning sigma algebra.  In a
stopping-time application that event is `{ω | j < τ ω}`. -/
theorem setIntegral_conditional_drift_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {u v f : Ω → ℝ} {A : Set Ω} {a ε : ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ) (hf : Integrable f μ)
    (hA : MeasurableSet[m] A)
    (hdrift : ∀ᵐ ω ∂μ, (μ[u | m]) ω - v ω ≤ -a * f ω + ε) :
    (∫ ω in A, u ω - v ω ∂μ) ≤
      -a * (∫ ω in A, f ω ∂μ) + ε * (μ A).toReal := by
  have hleft : Integrable (fun ω => (μ[u | m]) ω - v ω) μ :=
    integrable_condExp.sub hv
  have hright : Integrable (fun ω => -a * f ω + ε) μ :=
    (hf.const_mul (-a)).add (integrable_const ε)
  have h : (∫ ω in A, (μ[u | m]) ω - v ω ∂μ) ≤
      ∫ ω in A, -a * f ω + ε ∂μ :=
    integral_mono_ae hleft.integrableOn hright.integrableOn
      (ae_restrict_of_ae hdrift)
  have huc : Integrable (μ[u | m]) μ := integrable_condExp
  rw [integral_sub huc.integrableOn hv.integrableOn,
    setIntegral_condExp hm hu hA,
    integral_add (hf.const_mul (-a)).integrableOn (integrable_const ε),
    integral_const_mul, setIntegral_const] at h
  rw [integral_sub hu.integrableOn hv.integrableOn]
  simpa only [smul_eq_mul, mul_comm ε, Measure.real] using h

/-- Interchanging a bounded stopped sum and expectation uses only finite sums
and measurable past events.  No independence assumption is involved. -/
theorem sum_setIntegral_before_stopping (τ : Ω → ℕ) (N : ℕ)
    (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet {ω | j < τ ω})
    (f : ℕ → Ω → ℝ) (hf : ∀ j, Integrable (f j) μ) :
    (∑ j ∈ Finset.range N, ∫ ω in {ω | j < τ ω}, f j ω ∂μ) =
      ∫ ω, ∑ j ∈ Finset.range (τ ω), f j ω ∂μ := by
  classical
  calc
    (∑ j ∈ Finset.range N, ∫ ω in {ω | j < τ ω}, f j ω ∂μ) =
        ∑ j ∈ Finset.range N,
          ∫ ω, {ω | j < τ ω}.indicator (f j) ω ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_indicator (μ := μ) (f := f j) (hA j)).symm
    _ = ∫ ω, ∑ j ∈ Finset.range N,
        {ω | j < τ ω}.indicator (f j) ω ∂μ := by
      symm
      exact integral_finsetSum _ fun j _ => (hf j).indicator (hA j)
    _ = ∫ ω, ∑ j ∈ Finset.range (τ ω), f j ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
        sum_before_stopping (fun j => f j ω) (hτ ω)

/-- Bounded stopping of an integrated Lyapunov drift.  The step assumptions
can be obtained from `setIntegral_conditional_drift_le` at each filtration
level.  Every integrability and event-measurability obligation is explicit.

This is a general probability lemma: it does not assert that the manuscript's
Schrödinger pair process already satisfies these assumptions. -/
theorem bounded_stopped_occupation [IsFiniteMeasure μ] (τ : Ω → ℕ) (N : ℕ)
    (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet {ω | j < τ ω})
    (V f : ℕ → Ω → ℝ) (hV : ∀ j, Integrable (V j) μ)
    (hf : ∀ j, Integrable (f j) μ)
    (hVτ : Integrable (fun ω => V (τ ω) ω) μ) (a ε : ℝ)
    (hdrift : ∀ j < N,
      (∫ ω in {ω | j < τ ω}, V (j + 1) ω - V j ω ∂μ) ≤
        -a * (∫ ω in {ω | j < τ ω}, f j ω ∂μ) +
          ε * (μ {ω | j < τ ω}).toReal) :
    a * (∫ ω, ∑ j ∈ Finset.range (τ ω), f j ω ∂μ) ≤
      (∫ ω, V 0 ω ∂μ) - (∫ ω, V (τ ω) ω ∂μ) +
        ε * (∫ ω, (τ ω : ℝ) ∂μ) := by
  classical
  have hs := Finset.sum_le_sum fun j (hj : j ∈ Finset.range N) =>
    hdrift j (Finset.mem_range.mp hj)
  have hleft : (∑ j ∈ Finset.range N,
      ∫ ω in {ω | j < τ ω}, V (j + 1) ω - V j ω ∂μ) =
      (∫ ω, V (τ ω) ω ∂μ) - ∫ ω, V 0 ω ∂μ := by
    rw [sum_setIntegral_before_stopping (μ := μ) τ N hτ hA
      (fun j ω => V (j + 1) ω - V j ω)
      (fun j => (hV (j + 1)).sub (hV j))]
    calc
      (∫ ω, ∑ j ∈ Finset.range (τ ω), (V (j + 1) ω - V j ω) ∂μ) =
          ∫ ω, V (τ ω) ω - V 0 ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Finset.sum_range_sub (fun j => V j ω) (τ ω)
      _ = (∫ ω, V (τ ω) ω ∂μ) - ∫ ω, V 0 ω ∂μ := integral_sub hVτ (hV 0)
  have hcount : (∑ j ∈ Finset.range N, (μ {ω | j < τ ω}).toReal) =
      ∫ ω, (τ ω : ℝ) ∂μ := by
    have ht := sum_setIntegral_before_stopping (μ := μ) τ N hτ hA
      (fun _ _ => (1 : ℝ)) (fun _ => integrable_const 1)
    simpa [Measure.real] using ht
  rw [hleft, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_setIntegral_before_stopping (μ := μ) τ N hτ hA f hf, hcount] at hs
  linarith

/-- The bounded stopped occupation budget directly from conditional drift.
`F j` is the sigma algebra at time `j`; the stopping property is supplied in
the exact form needed by the proof, measurability of `{ω | j < τ ω}`.
All these are generic hypotheses that must still be verified for the actual
random pair chain. -/
theorem bounded_stopped_occupation_of_conditional_drift
    [IsFiniteMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ j, F j ≤ m₀)
    (τ : Ω → ℕ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet[F j] {ω | j < τ ω})
    (V f : ℕ → Ω → ℝ) (hV : ∀ j, Integrable (V j) μ)
    (hf : ∀ j, Integrable (f j) μ)
    (hVτ : Integrable (fun ω => V (τ ω) ω) μ) (a ε : ℝ)
    (hdrift : ∀ j < N, ∀ᵐ ω ∂μ,
      (μ[V (j + 1) | F j]) ω - V j ω ≤ -a * f j ω + ε) :
    a * (∫ ω, ∑ j ∈ Finset.range (τ ω), f j ω ∂μ) ≤
      (∫ ω, V 0 ω ∂μ) - (∫ ω, V (τ ω) ω ∂μ) +
        ε * (∫ ω, (τ ω : ℝ) ∂μ) := by
  apply bounded_stopped_occupation τ N hτ (fun j => hF j _ (hA j))
    V f hV hf hVτ a ε
  intro j hj
  exact setIntegral_conditional_drift_le (hF j) (hV (j + 1)) (hV j)
    (hf j) (hA j) (hdrift j hj)

/-- A nonnegative terminal Lyapunov value may be discarded.  This is the
bounded-stopping form of the occupation estimate used before taking any
unbounded hitting-time limit. -/
theorem bounded_stopped_occupation_of_conditional_drift_nonneg
    [IsFiniteMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ j, F j ≤ m₀)
    (τ : Ω → ℕ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N)
    (hA : ∀ j, MeasurableSet[F j] {ω | j < τ ω})
    (V f : ℕ → Ω → ℝ) (hV : ∀ j, Integrable (V j) μ)
    (hf : ∀ j, Integrable (f j) μ)
    (hVτ : Integrable (fun ω => V (τ ω) ω) μ)
    (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ V (τ ω) ω) (a ε : ℝ)
    (hdrift : ∀ j < N, ∀ᵐ ω ∂μ,
      (μ[V (j + 1) | F j]) ω - V j ω ≤ -a * f j ω + ε) :
    a * (∫ ω, ∑ j ∈ Finset.range (τ ω), f j ω ∂μ) ≤
      (∫ ω, V 0 ω ∂μ) + ε * (∫ ω, (τ ω : ℝ) ∂μ) := by
  have hbudget := bounded_stopped_occupation_of_conditional_drift
    F hF τ N hτ hA V f hV hf hVτ a ε hdrift
  have ht : 0 ≤ ∫ ω, V (τ ω) ω ∂μ := integral_nonneg_of_ae hnonneg
  linarith

end ConditionalDrift

end Occupation
end FixedCouplingPoisson
