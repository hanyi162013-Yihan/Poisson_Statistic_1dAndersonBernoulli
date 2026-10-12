import FixedCouplingPoisson.ColoredBlockKernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional finite-color block errors on a past-measurable event

The enclosing-count domination need hold only on the selected past event.
The proof localizes the error with its indicator before conditioning, so
no independence among colors and no global domination are required.
Actual block counts must still supply the explicit hypotheses below.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set
open scoped BigOperators

section Localized
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
    {M : MeasurableSpace Ω} {G : Set Ω}

/-- A pointwise absolute-error budget on a past event remains valid after
conditioning, on that same event. -/
theorem condExp_abs_le_on_measurable_event (hM : M ≤ m₀)
    (hG : MeasurableSet[M] G) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (hbound : ∀ ω ∈ G, |f ω| ≤ g ω) :
    ∀ᵐ ω ∂μ, ω ∈ G → |(μ[f | M]) ω| ≤ (μ[g | M]) ω := by
  let : MeasurableSpace Ω := m₀
  classical
  have hFi : Integrable (G.indicator f) μ := hf.indicator (hM _ hG)
  have hglobal : |G.indicator f| ≤ᵐ[μ] g := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [Pi.abs_apply, Set.indicator_of_mem hω] using hbound ω hω
    · simpa only [Pi.abs_apply, Set.indicator_of_notMem hω, abs_zero] using hg0 ω
  have habs := abs_condExp_ae_le_condExp_abs (μ := μ) (m := M) (G.indicator f)
  have hmono := condExp_mono (m := M) hFi.abs hg hglobal
  have hlocal := condExp_indicator hf hG
  filter_upwards [habs, hmono, hlocal] with ω ha hm hl hω
  have hle := ha.trans hm
  simpa only [Pi.abs_apply, hl, Set.indicator_of_mem hω] using hle

end Localized

section Probability
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]

def twoArrivalIndicator (y : ℕ) : ℝ := if 2 ≤ y then 1 else 0

theorem measurable_twoArrivalIndicator {Y : Ω → ℕ} (hY : Measurable[m₀] Y) :
    Measurable[m₀] (fun ω => twoArrivalIndicator (Y ω)) :=
  (measurable_of_countable twoArrivalIndicator).comp hY

theorem twoArrivalIndicator_bounds (y : ℕ) :
    0 ≤ twoArrivalIndicator y ∧ twoArrivalIndicator y ≤ 1 := by
  unfold twoArrivalIndicator
  split_ifs <;> norm_num

theorem integrable_twoArrivalIndicator {Y : Ω → ℕ} (hY : Measurable[m₀] Y) :
    Integrable (fun ω => twoArrivalIndicator (Y ω)) μ :=
  bounded_block_integrable (measurable_twoArrivalIndicator hY).stronglyMeasurable
    (fun ω => twoArrivalIndicator_bounds (Y ω))

/-- The conditional linear factor is the linear combination of the
conditional one-arrival indicators. -/
theorem condExp_coloredLinearFactor {M : MeasurableSpace Ω} (hM : M ≤ m₀) {s : ℕ}
    (t : Fin s → ℝ) {X : Fin s → Ω → ℕ} (hX : ∀ i, Measurable[m₀] (X i)) :
    μ[(fun ω => coloredLinearFactor t (fun i => X i ω)) | M] =ᵐ[μ]
      fun ω => 1 - ∑ i, firstArrivalWeight (t i) *
        (μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω := by
  let : MeasurableSpace Ω := m₀
  let F : Fin s → Ω → ℝ := fun i ω =>
    firstArrivalWeight (t i) * firstArrivalIndicator (X i ω)
  have hi : ∀ i, Integrable (F i) μ := fun i =>
    (bounded_block_integrable (measurable_firstArrivalIndicator (hX i)).stronglyMeasurable
      (fun ω => firstArrivalIndicator_bounds _)).const_mul _
  have hsum : μ[(fun ω => ∑ i, F i ω) | M] =ᵐ[μ]
      fun ω => ∑ i, (μ[F i | M]) ω := by
    have h := condExp_finsetSum (s := Finset.univ) (fun i _ => hi i) M
    have heq : (∑ i, F i) = (fun ω => ∑ i, F i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq] at h
    filter_upwards [h] with ω hω
    simpa only [Finset.sum_apply] using hω
  have hscalar : ∀ᵐ ω ∂μ, ∀ i,
      (μ[F i | M]) ω = firstArrivalWeight (t i) *
        (μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω := by
    apply ae_all_iff.mpr
    intro i
    have h := condExp_smul (μ := μ) (firstArrivalWeight (t i))
      (fun z => firstArrivalIndicator (X i z)) M
    have heq : firstArrivalWeight (t i) •
        (fun z => firstArrivalIndicator (X i z)) = F i := by
      funext ω
      simp only [F, Pi.smul_apply, smul_eq_mul]
    rw [heq] at h
    filter_upwards [h] with ω hω
    simpa only [Pi.smul_apply, smul_eq_mul] using hω
  have hsub := condExp_sub (μ := μ) (integrable_const (1 : ℝ))
    (integrable_finsetSum Finset.univ (fun i _ => hi i)) M
  filter_upwards [hsum, hscalar, hsub] with ω hsumω hscalarω hsubω
  change (μ[(fun z => 1 - ∑ i, F i z) | M]) ω = _
  change (μ[(fun z => 1 - ∑ i, F i z) | M]) ω =
    (μ[(fun _ => (1 : ℝ)) | M]) ω - (μ[(fun z => ∑ i, F i z) | M]) ω at hsubω
  rw [hsubω, condExp_const hM, hsumω]
  simp only [hscalarω]

/-- The conditional nonlinear error is confined to two enclosing arrivals,
including when domination is known only on the selected past event. -/
theorem condExp_coloredLaplaceFactor_error_le_on_event {M : MeasurableSpace Ω} (hM : M ≤ m₀)
    {G : Set Ω} (hG : MeasurableSet[M] G) {s : ℕ} (t : Fin s → ℝ)
    (ht : ∀ i, 0 ≤ t i) {X : Fin s → Ω → ℕ} {Y : Ω → ℕ}
    (hX : ∀ i, Measurable[m₀] (X i)) (hY : Measurable[m₀] Y)
    (hdom : ∀ ω ∈ G, ∑ i, X i ω ≤ Y ω) :
    ∀ᵐ ω ∂μ, ω ∈ G →
      |(μ[(fun z => coloredLaplaceFactor t (fun i => X i z)) | M]) ω -
        (1 - ∑ i, firstArrivalWeight (t i) *
          (μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω)| ≤
      ((s : ℝ) + 1) * (μ[(fun z => twoArrivalIndicator (Y z)) | M]) ω := by
  let : MeasurableSpace Ω := m₀
  have hψ := integrable_coloredLaplaceFactor t ht hX (μ := μ)
  have hL := integrable_coloredLinearFactor t hX (μ := μ)
  have hbad := (integrable_twoArrivalIndicator hY (μ := μ)).const_mul ((s : ℝ) + 1)
  have hs : 0 ≤ (s : ℝ) + 1 := by positivity
  have hlocal := condExp_abs_le_on_measurable_event hM hG (hψ.sub hL) hbad
    (fun ω => mul_nonneg hs (twoArrivalIndicator_bounds (Y ω)).1)
    (fun ω hω => by
      change |coloredLaplaceFactor t (fun i => X i ω) -
        coloredLinearFactor t (fun i => X i ω)| ≤
          ((s : ℝ) + 1) * twoArrivalIndicator (Y ω)
      simpa only [twoArrivalIndicator, mul_ite, mul_one, mul_zero] using
        coloredLaplaceFactor_linear_error_le_bad_indicator t ht
          (fun i => X i ω) (Y ω) (hdom ω hω))
  have hsub := condExp_sub hψ hL M
  have hlinear := condExp_coloredLinearFactor hM t hX (μ := μ)
  have hscalar := condExp_smul (μ := μ) ((s : ℝ) + 1)
    (fun z => twoArrivalIndicator (Y z)) M
  filter_upwards [hlocal, hsub, hlinear, hscalar] with ω hl hsubω hlinω hscω hω
  have hbound := hl hω
  change |(μ[(fun z => coloredLaplaceFactor t (fun i => X i z)) -
      (fun z => coloredLinearFactor t (fun i => X i z)) | M]) ω| ≤
    (μ[((s : ℝ) + 1) • (fun z => twoArrivalIndicator (Y z)) | M]) ω at hbound
  simpa only [hsubω, Pi.sub_apply, hlinω, hscω, Pi.smul_apply, smul_eq_mul] using hbound

/-- Conditional one-arrival approximation errors can be added pointwise;
the comparison values may depend on the past outcome. -/
theorem condExp_coloredLaplaceFactor_error_le_on_event_of_arrival_approx
    {M : MeasurableSpace Ω} (hM : M ≤ m₀) {G : Set Ω} (hG : MeasurableSet[M] G) {s : ℕ}
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i)
    {X : Fin s → Ω → ℕ} {Y : Ω → ℕ}
    (hX : ∀ i, Measurable[m₀] (X i)) (hY : Measurable[m₀] Y)
    (hdom : ∀ ω ∈ G, ∑ i, X i ω ≤ Y ω) (q : Fin s → Ω → ℝ) :
    ∀ᵐ ω ∂μ, ω ∈ G →
      |(μ[(fun z => coloredLaplaceFactor t (fun i => X i z)) | M]) ω -
        (1 - ∑ i, firstArrivalWeight (t i) * q i ω)| ≤
      ((s : ℝ) + 1) * (μ[(fun z => twoArrivalIndicator (Y z)) | M]) ω +
        ∑ i, |(μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω - q i ω| := by
  let : MeasurableSpace Ω := m₀
  filter_upwards [condExp_coloredLaplaceFactor_error_le_on_event hM hG t ht hX hY hdom]
    with ω hbase hω
  have hlin : |(1 - ∑ i, firstArrivalWeight (t i) *
      (μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω) -
      (1 - ∑ i, firstArrivalWeight (t i) * q i ω)| ≤
      ∑ i, |(μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω - q i ω| := by
    have heq : (1 - ∑ i, firstArrivalWeight (t i) *
        (μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω) -
        (1 - ∑ i, firstArrivalWeight (t i) * q i ω) =
        -(∑ i, firstArrivalWeight (t i) *
          ((μ[(fun z => firstArrivalIndicator (X i z)) | M]) ω - q i ω)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    rw [heq, abs_neg]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul, abs_of_nonneg (firstArrivalWeight_bounds (ht i)).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (firstArrivalWeight_bounds (ht i)).2
  exact (abs_sub_le _ _ _).trans (add_le_add (hbase hω) hlin)

end Probability
end FixedCouplingPoisson
