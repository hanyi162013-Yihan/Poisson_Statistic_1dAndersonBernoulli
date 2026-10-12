import FixedCouplingPoisson.ScalarCrossingCounts
import FixedCouplingPoisson.GammaTails
import FixedCouplingPoisson.WeakMovingThreshold

/-! Finite arrival truncation and the actual short-window probability
required for residual pinning. Only this assembled module is published. -/

/-! A finite arrival truncation controls a short interval containing
at least one count increase. No independent-increment premise is used. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem nat_increment_probability_le_tail_budget
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℕ) (hX : Measurable X) (hXY : ∀ ω, X ω ≤ Y ω) (M : ℕ) :
    μ.real {ω | X ω < Y ω} ≤ μ.real {ω | M ≤ Y ω} +
      ∑ k ∈ Finset.range M,
        (μ.real {ω | k + 1 ≤ Y ω} - μ.real {ω | k + 1 ≤ X ω}) := by
  let B : ℕ → Set Ω := fun k => {ω | k + 1 ≤ Y ω} \ {ω | k + 1 ≤ X ω}
  have hs : {ω | X ω < Y ω} ⊆
      {ω | M ≤ Y ω} ∪ ⋃ k ∈ Finset.range M, B k := by
    intro ω hω
    by_cases hM : M ≤ Y ω
    · exact Or.inl hM
    · right
      have hXM : X ω < M := hω.trans (lt_of_not_ge hM)
      refine mem_iUnion.mpr ⟨X ω, mem_iUnion.mpr ⟨Finset.mem_range.mpr hXM, ?_⟩⟩
      exact ⟨Nat.succ_le_of_lt hω, Nat.not_succ_le_self _⟩
  have hdiff (k : ℕ) : μ.real (B k) =
      μ.real {ω | k + 1 ≤ Y ω} - μ.real {ω | k + 1 ≤ X ω} := by
    apply measureReal_sdiff
    · exact fun ω hω => hω.trans (hXY ω)
    · exact measurableSet_le measurable_const hX
    · exact measure_ne_top μ _
  calc
    μ.real {ω | X ω < Y ω} ≤
        μ.real ({ω | M ≤ Y ω} ∪ ⋃ k ∈ Finset.range M, B k) := measureReal_mono hs
    _ ≤ μ.real {ω | M ≤ Y ω} + μ.real (⋃ k ∈ Finset.range M, B k) :=
      measureReal_union_le _ _
    _ ≤ μ.real {ω | M ≤ Y ω} + ∑ k ∈ Finset.range M, μ.real (B k) :=
      add_le_add le_rfl (measureReal_biUnion_finset_le (μ := μ) (Finset.range M) B)
    _ = _ := by simp_rw [hdiff]

def shortWindowLimitBudget (M : ℕ) (t u : ℝ) : ℝ :=
  cdf (exponentialSumLaw M : Measure ℝ) u +
    ∑ k ∈ Finset.range M,
      (cdf (exponentialSumLaw (k + 1) : Measure ℝ) u -
        cdf (exponentialSumLaw (k + 1) : Measure ℝ) t)

theorem continuous_shortWindowLimitBudget (M : ℕ) (hM : 0 < M) (t : ℝ) :
    Continuous (shortWindowLimitBudget M t) := by
  have hc : Continuous (cdf (exponentialSumLaw M : Measure ℝ)) := by
    cases M with
    | zero => omega
    | succ M => exact continuous_cdf_exponentialSumLaw_succ M
  exact hc.add (continuous_finsetSum _ fun k _ =>
    (continuous_cdf_exponentialSumLaw_succ k).sub continuous_const)

theorem shortWindowLimitBudget_self (M : ℕ) (t : ℝ) :
    shortWindowLimitBudget M t t = cdf (exponentialSumLaw M : Measure ℝ) t := by
  simp only [shortWindowLimitBudget, sub_self, Finset.sum_const_zero, add_zero]

/-- Choose a finite arrival cutoff, and then a genuinely positive short
rescaled interval. Only continuity and the proved arrival cutoff tail enter. -/
theorem exists_shortWindowLimitBudget_lt (t ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ ∃ η : ℝ, 0 < η ∧
      shortWindowLimitBudget M t (t + η) < ε := by
  have he := (tendsto_cdf_exponentialSumLaw_atTop_zero t).eventually
    (Iio_mem_nhds hε)
  obtain ⟨M, hM, htail⟩ := (eventually_gt_atTop 0).and he |>.exists
  have hb : shortWindowLimitBudget M t t < ε := by
    simpa only [shortWindowLimitBudget_self] using htail
  have hnear := (continuous_shortWindowLimitBudget M hM t).continuousAt.tendsto.eventually
    (Iio_mem_nhds hb)
  obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨M, hM, r / 2, by positivity, ?_⟩
  apply hrg
  rw [Real.dist_eq, show t + r / 2 - t = r / 2 by ring,
    abs_of_pos (by positivity : 0 < r / 2)]
  linarith

end FixedCouplingPoisson


/-! Actual small probabilities of a crossing in a suitable positive
rescaled short interval. This is enough for the upper-residual argument. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def positiveScaledHorizon (η p : ℝ) : ℕ := ⌈η / p⌉₊

theorem positiveScaledHorizon_bounds (η p : ℝ) (hη : 0 < η) (hp : 0 < p) :
    η ≤ p * (positiveScaledHorizon η p : ℝ) ∧
      p * (positiveScaledHorizon η p : ℝ) < η + p := by
  have hlo := mul_le_mul_of_nonneg_left (Nat.le_ceil (η / p)) hp.le
  have hhi := mul_lt_mul_of_pos_left
    (Nat.ceil_lt_add_one (div_nonneg hη.le hp.le)) hp
  have hc : p * (η / p) = η := by field_simp
  unfold positiveScaledHorizon
  constructor <;> nlinarith

theorem positiveScaledHorizon_tendsto {ι : Type*} {F : Filter ι}
    {ps : ι → ℝ} (hp : ∀ i, 0 < ps i) (hps : Tendsto ps F (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun i => ps i * (positiveScaledHorizon η (ps i) : ℝ)) F (𝓝 η) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using tendsto_const_nhds.add hps)
  · exact fun i => (positiveScaledHorizon_bounds η (ps i) hη (hp i)).1
  · exact fun i => (positiveScaledHorizon_bounds η (ps i) hη (hp i)).2.le

namespace Furstenberg

theorem idsCandidate_increment_tendsto_zero_on_compact
    {ι : Type*} {F : Filter ι} (law : PotentialLaw)
    {K : Set ℝ} (hK : IsCompact K) (E δ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hδlim : Tendsto δ F (𝓝 0)) :
    Tendsto (fun i => idsCandidate law (E i + δ i) - idsCandidate law (E i))
      F (𝓝 0) := by
  have hp (i : ι) : 0 ≤ idsCandidate law (E i + δ i) - idsCandidate law (E i) :=
    sub_nonneg.mpr ((monotone_idsCandidate law) (le_add_of_nonneg_right (hδ i)))
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le (hp i)
  · intro a ha
    obtain ⟨d, hd, hb⟩ := idsCandidate_increment_uniform law hK ha
    filter_upwards [hδlim.eventually (Iio_mem_nhds hd)] with i hi
    exact (hb (E i) (hE i) (δ i) (hδ i) (hE' i) hi).2

/-- The short-window conclusion required by residual pinning, obtained from
actual count-tail limits and continuous actual exponential-sum laws. -/
theorem canonicalCrossingCount_short_windows
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0))
    (j : ι → ℕ) {t : ℝ}
    (htime : Tendsto (fun i =>
      (idsCandidate law (E i + δ i) - idsCandidate law (E i)) * (j i : ℝ)) F (𝓝 t))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ι → ℕ, ∃ a : ℝ, 0 < a ∧
      (∀ᶠ i in F, a ≤ (idsCandidate law (E i + δ i) - idsCandidate law (E i)) * (L i : ℝ)) ∧
      ∀ᶠ i in F, iidMeasure law
        {ω | canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i) ω <
          canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i + L i) ω} ≤
            ENNReal.ofReal ε := by
  let p : ι → ℝ := fun i => idsCandidate law (E i + δ i) - idsCandidate law (E i)
  obtain ⟨M, hM, η, hη, hbudget⟩ := exists_shortWindowLimitBudget_lt t ε hε
  let L : ι → ℕ := fun i => positiveScaledHorizon η (p i)
  have hp0 : Tendsto p F (𝓝 0) :=
    idsCandidate_increment_tendsto_zero_on_compact law hK E δ hE hE' hδ hδlim
  have hL : Tendsto (fun i => p i * (L i : ℝ)) F (𝓝 η) :=
    positiveScaledHorizon_tendsto hp hp0 hη
  have htime' : Tendsto (fun i => p i * ((j i + L i : ℕ) : ℝ)) F (𝓝 (t + η)) := by
    simpa only [Nat.cast_add, mul_add] using htime.add hL
  let A : ι → ℕ → ℝ := fun i k => (iidMeasure law).real
    {ω | k ≤ canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (j i) ω}
  let B : ι → ℕ → ℝ := fun i k => (iidMeasure law).real
    {ω | k ≤ canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (j i + L i) ω}
  have hA (k : ℕ) (hk : 0 < k) :
      Tendsto (fun i => A i k) F (𝓝 (cdf (exponentialSumLaw k : Measure ℝ) t)) :=
    canonicalNaturalCrossingCount_tail_tendsto law input hK E δ θ φ
      hE hE' hδ hinit hp hδlim hgap j htime k hk
  have hB (k : ℕ) (hk : 0 < k) :
      Tendsto (fun i => B i k) F (𝓝 (cdf (exponentialSumLaw k : Measure ℝ) (t + η))) :=
    canonicalNaturalCrossingCount_tail_tendsto law input hK E δ θ φ
      hE hE' hδ hinit hp hδlim hgap (fun i => j i + L i) htime' k hk
  have hsum : Tendsto (fun i => B i M +
      ∑ k ∈ Finset.range M, (B i (k + 1) - A i (k + 1))) F
        (𝓝 (shortWindowLimitBudget M t (t + η))) :=
    (hB M hM).add (tendsto_finsetSum _ fun k _ =>
      (hB (k + 1) (Nat.succ_pos k)).sub (hA (k + 1) (Nat.succ_pos k)))
  refine ⟨L, η, hη, Eventually.of_forall
    (fun i => (positiveScaledHorizon_bounds η (p i) hη (hp i)).1), ?_⟩
  filter_upwards [hsum.eventually (Iio_mem_nhds hbudget)] with i hi
  let X := canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (j i)
  let Y := canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (j i + L i)
  have hXY : ∀ ω, X ω ≤ Y ω := by
    intro ω
    exact Int.toNat_le_toNat ((canonicalCrossingCount_mono
      (E i) (δ i) (θ i) (φ i) (hδ i) ω) (Nat.le_add_right _ _))
  have hbound : (iidMeasure law).real {ω | X ω < Y ω} < ε :=
    (nat_increment_probability_le_tail_budget (iidMeasure law) X Y
      (canonicalNaturalCrossingCount_measurable (E i) (δ i) (θ i) (φ i) (j i))
      hXY M).trans_lt hi
  have hevent : {ω | canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i) ω <
      canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i + L i) ω} =
        {ω | X ω < Y ω} := by
    ext ω
    have hx := Int.toNat_of_nonneg
      (canonicalCrossingCount_nonneg (E i) (δ i) (θ i) (φ i) (hδ i) (hinit i) (j i) ω)
    have hy := Int.toNat_of_nonneg
      (canonicalCrossingCount_nonneg (E i) (δ i) (θ i) (φ i) (hδ i) (hinit i) (j i + L i) ω)
    change canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i) ω <
      canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i + L i) ω ↔
      (canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i) ω).toNat <
      (canonicalCrossingCount (E i) (δ i) (θ i) (φ i) (j i + L i) ω).toNat
    omega
  rw [hevent, ← ENNReal.ofReal_toReal (measure_ne_top (iidMeasure law) {ω | X ω < Y ω})]
  exact ENNReal.ofReal_le_ofReal hbound.le

end Furstenberg
end FixedCouplingPoisson
