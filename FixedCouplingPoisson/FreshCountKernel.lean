import FixedCouplingPoisson.UniformArrivalCDF
import FixedCouplingPoisson.IIDKernel

/-! Actual iid fresh-future count-tail kernels with arbitrary past states.
The later recentering lemma must identify the fresh count with the original
path increment; that identity is not assumed or asserted in this module. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory

theorem canonicalNaturalCrossingCount_measurable_initial_path
    (E δ : ℝ) (L : ℕ) :
    Measurable (fun z : (ℝ × ℝ) × PotentialSpace =>
      canonicalNaturalCrossingCount E δ z.1.1 z.1.2 L z.2) :=
  (measurable_of_countable Int.toNat).comp
    (((canonicalGapProcess_measurable_initial_path E δ L).div_const Real.pi).floor)

def freshCountTailObservable (E δ : ℝ) (k L : ℕ) :
    (ℝ × ℝ) × PotentialSpace → ℝ :=
  {z | k ≤ canonicalNaturalCrossingCount E δ z.1.1 z.1.2 L z.2}.indicator
    (fun _ => 1)

def freshCountTailKernel (law : PotentialLaw) (E δ : ℝ) (k L : ℕ)
    (x : ℝ × ℝ) : ℝ :=
  futureKernel law (freshCountTailObservable E δ k L) x

theorem freshCountTailObservable_measurable (E δ : ℝ) (k L : ℕ) :
    Measurable (freshCountTailObservable E δ k L) :=
  measurable_const.indicator (measurableSet_le measurable_const
    (canonicalNaturalCrossingCount_measurable_initial_path E δ L))

theorem freshCountTailObservable_bounds (E δ : ℝ) (k L : ℕ)
    (z : (ℝ × ℝ) × PotentialSpace) :
    0 ≤ freshCountTailObservable E δ k L z ∧ freshCountTailObservable E δ k L z ≤ 1 := by
  by_cases hz : k ≤ canonicalNaturalCrossingCount E δ z.1.1 z.1.2 L z.2
  · simp [freshCountTailObservable, hz]
  · simp [freshCountTailObservable, hz]

theorem freshCountTailKernel_eq_probability (law : PotentialLaw) (E δ θ φ : ℝ)
    (k L : ℕ) :
    freshCountTailKernel law E δ k L (θ, φ) =
      (iidMeasure law).real {ω | k ≤ canonicalNaturalCrossingCount E δ θ φ L ω} := by
  unfold freshCountTailKernel futureKernel
  have heq : (fun ω => freshCountTailObservable E δ k L ((θ, φ), ω)) =
      {ω | k ≤ canonicalNaturalCrossingCount E δ θ φ L ω}.indicator
        (fun _ => (1 : ℝ)) := rfl
  rw [heq, integral_indicator_const _ (measurableSet_le measurable_const
    (canonicalNaturalCrossingCount_measurable E δ θ φ L))]
  simp only [smul_eq_mul, mul_one]

theorem freshCountTail_condExp (law : PotentialLaw) (E δ : ℝ) (k j L : ℕ)
    {X : PotentialSpace → ℝ × ℝ} (hX : Measurable[pastMeasurableSpace j] X) :
    (iidMeasure law)[(fun ω => freshCountTailObservable E δ k L
      (X ω, potentialShift j ω)) | pastMeasurableSpace j] =ᵐ[iidMeasure law]
        (fun ω => freshCountTailKernel law E δ k L (X ω)) := by
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le j) le_rfl
  let ν : ProbabilityMeasure (ℝ × ℝ) := ⟨(iidMeasure law).map X,
    Measure.isProbabilityMeasure_map hXm.aemeasurable⟩
  have hi : Integrable (freshCountTailObservable E δ k L)
      (((iidMeasure law).map X).prod (iidMeasure law)) := by
    apply (integrable_const (1 : ℝ)).mono'
      (freshCountTailObservable_measurable E δ k L).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (freshCountTailObservable_bounds E δ k L z).1]
      exact (freshCountTailObservable_bounds E δ k L z).2
  exact iidMeasure_condExp_past_futureKernel law j hX
    (freshCountTailObservable_measurable E δ k L) hi

theorem freshCountTailKernel_uniform_small_gap
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
    ∀ᶠ n in atTop, ∀ θ φ : ℝ, 0 ≤ θ - φ → θ - φ ≤ r n →
      |freshCountTailKernel law (E n) (δ n) k (ℓ n) (θ, φ) -
        cdf (exponentialSumLaw k : Measure ℝ) t| < ε := by
  have h := canonical_arrival_cdf_uniform_initial_gap law input hK E δ r
    hE hE' hδ hr hp hδlim hrlim ℓ htime k hk ε hε
  filter_upwards [h] with n hn
  intro θ φ hd0 hdr
  have hstate := hn θ (θ - φ) hd0 hdr
  have heq : θ - (θ - φ) = φ := by ring
  simpa only [freshCountTailKernel_eq_probability, canonicalCountTailProbability, heq]
    using hstate

end FixedCouplingPoisson.Furstenberg
