import FixedCouplingPoisson.ActualColoredBlock
import FixedCouplingPoisson.GammaSmallTime

/-! Uniform small-block errors for the actual phase model. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

def coloredQuadraticBudget (s : ℕ) (τ : Fin s → ℝ) (T : ℝ) : ℝ :=
  ((s : ℝ) + 1) * (T ^ 2 / 2) + ∑ i, (τ i) ^ 2 / 2

theorem colored_arrival_quadratic_budget (s : ℕ) (τ : Fin s → ℝ) (T ε : ℝ)
    (hτ : ∀ i, 0 ≤ τ i) (hT : 0 ≤ T) (f : Fin s → ℝ) (g : ℝ)
    (hf : ∀ i, |f i - cdf (exponentialSumLaw 1 : Measure ℝ) (τ i)| ≤ ε)
    (hg : g ≤ cdf (exponentialSumLaw 2 : Measure ℝ) T + ε) :
    ((s : ℝ) + 1) * g + ∑ i, |f i - τ i| ≤
      coloredQuadraticBudget s τ T + (2 * (s : ℝ) + 1) * ε := by
  have hfirst (i : Fin s) : |f i - τ i| ≤ ε + (τ i) ^ 2 / 2 := by
    exact (abs_sub_le (f i) (cdf (exponentialSumLaw 1 : Measure ℝ) (τ i))
      (τ i)).trans (add_le_add (hf i)
        (cdf_exponentialSumLaw_one_error_le_half_sq (τ i) (hτ i)))
  have htwo : g ≤ T ^ 2 / 2 + ε :=
    hg.trans (add_le_add (cdf_exponentialSumLaw_two_le_half_sq T hT) le_rfl)
  calc
    _ ≤ ((s : ℝ) + 1) * (T ^ 2 / 2 + ε) + ∑ i : Fin s, (ε + (τ i) ^ 2 / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left htwo (by positivity))
        (Finset.sum_le_sum fun i _ => hfirst i)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold coloredQuadraticBudget
      ring

/-- For a fixed number of energy colors, the true conditional block kernel has
the quadratic Gamma error uniformly over all good past states and block starts.
Every fresh-iid arrival approximation is discharged by the phase-model theorem. -/
theorem canonicalColoredBlock_conditional_error_uniform
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s : ℕ) (E₀ : ℝ)
    (hcompact : ∀ n i, i ≤ s → e n i ∈ K)
    (horder : ∀ n i, i < s → e n i ≤ e n (i + 1))
    (houter : ∀ n, e n 0 ≤ e n s)
    (hp : ∀ n i, i < s → 0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hpouter : ∀ n, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
    (helim : ∀ i, i ≤ s → Tendsto (fun n => e n i) atTop (𝓝 E₀))
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ℓ : ℕ → ℕ) (τ : Fin s → ℝ) (T : ℝ) (hτ : ∀ i, 0 ≤ τ i) (hT : 0 ≤ T)
    (htime : ∀ i : Fin s, Tendsto (fun n =>
      (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (ℓ n : ℝ))
      atTop (𝓝 (τ i)))
    (houtertime : Tendsto (fun n =>
      (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (ℓ n : ℝ))
      atTop (𝓝 T))
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j : ℕ,
      ∀ᵐ ω ∂iidMeasure law, ω ∈ canonicalColoredGoodStart (e n) s j (r n) →
        |((iidMeasure law)[(fun z => coloredLaplaceFactor t
          (canonicalColoredBlock (e n) s j (ℓ n) z)) | pastMeasurableSpace j]) ω -
            (1 - ∑ i, firstArrivalWeight (t i) * τ i)| ≤
          coloredQuadraticBudget s τ T + (2 * (s : ℝ) + 1) * ε := by
  have hplus (a b : ℝ) : a + (b - a) = b := by ring
  have hfirst : ∀ i : Fin s, ∀ᶠ n in atTop, ∀ θ φ : ℝ, ∀ j : ℕ,
      ∀ ω : PotentialSpace,
      canonicalCrossingResidual (e n i.val) (e n (i.val + 1) - e n i.val) θ φ j ω ≤ r n →
      |freshCountTailKernel law (e n i.val) (e n (i.val + 1) - e n i.val) 1 (ℓ n)
          (canonicalResidualState (e n i.val) (e n (i.val + 1) - e n i.val) θ φ j ω) -
        cdf (exponentialSumLaw 1 : Measure ℝ) (τ i)| < ε := by
    intro i
    apply canonicalBlockCount_tailKernel_uniform_on_small_residual law input hK
      (fun n => e n i.val) (fun n => e n (i.val + 1) - e n i.val) r
    · exact fun n => hcompact n i.val (Nat.le_of_lt i.isLt)
    · intro n
      simpa only [hplus] using hcompact n (i.val + 1) (by omega)
    · exact fun n => sub_nonneg.mpr (horder n i.val i.isLt)
    · exact hr
    · intro n
      simpa only [hplus] using hp n i.val i.isLt
    · simpa only [sub_self] using
        (helim (i.val + 1) (by omega)).sub (helim i.val (Nat.le_of_lt i.isLt))
    · exact hrlim
    · simpa only [hplus] using htime i
    · norm_num
    · exact hε
  have htwo : ∀ᶠ n in atTop, ∀ θ φ : ℝ, ∀ j : ℕ, ∀ ω : PotentialSpace,
      canonicalCrossingResidual (e n 0) (e n s - e n 0) θ φ j ω ≤ r n →
      |freshCountTailKernel law (e n 0) (e n s - e n 0) 2 (ℓ n)
          (canonicalResidualState (e n 0) (e n s - e n 0) θ φ j ω) -
        cdf (exponentialSumLaw 2 : Measure ℝ) T| < ε := by
    apply canonicalBlockCount_tailKernel_uniform_on_small_residual law input hK
      (fun n => e n 0) (fun n => e n s - e n 0) r
    · exact fun n => hcompact n 0 (Nat.zero_le s)
    · intro n
      simpa only [hplus] using hcompact n s (le_refl s)
    · exact fun n => sub_nonneg.mpr (houter n)
    · exact hr
    · intro n
      simpa only [hplus] using hpouter n
    · simpa only [sub_self] using (helim s (le_refl s)).sub (helim 0 (Nat.zero_le s))
    · exact hrlim
    · simpa only [hplus] using houtertime
    · norm_num
    · exact hε
  have hrsmall : ∀ᶠ n in atTop, (s : ℝ) * r n < Real.pi := by
    have hlim : Tendsto (fun n => (s : ℝ) * r n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hrlim
    exact hlim.eventually (gt_mem_nhds Real.pi_pos)
  filter_upwards [eventually_all.mpr hfirst, htwo, hrsmall] with n hnfirst hntwo hnsmall
  intro j
  filter_upwards [canonicalColoredBlock_conditional_error_budget law (e n) s j (ℓ n)
    (horder n) (houter n) (r n) hnsmall t τ ht] with ω hbase hgood
  apply (hbase hgood).trans
  apply colored_arrival_quadratic_budget s τ T ε hτ hT
  · intro i
    exact (hnfirst i 0 0 j ω (hgood.1 i)).le
  · have h := (hntwo 0 0 j ω hgood.2).le
    have hu := (le_abs_self _).trans h
    linarith

end FixedCouplingPoisson.Furstenberg
