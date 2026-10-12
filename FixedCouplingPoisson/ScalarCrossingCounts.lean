import FixedCouplingPoisson.CrossingArrivalVector
import FixedCouplingPoisson.GammaArrivals
import FixedCouplingPoisson.CanonicalResidual
import FixedCouplingPoisson.WeakMovingThreshold

/-! Actual arrival laws, pathwise count/arrival equivalence and moving-time
count-tail convergence. The three editing groups are published only through
this assembled module, so their declarations are not duplicated. -/

/-! Genuine scalar locations of successive crossings converge to actual
sums of independent exponential variables, including the zero location. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def scaledCanonicalLevelArrival (law : PotentialLaw) (E δ θ φ : ℝ) (k : ℕ)
    (ω : PotentialSpace) : ℝ :=
  (idsCandidate law (E + δ) - idsCandidate law E) *
    (((canonicalLevelCrossingTime E δ θ φ k ω).untopD 0 : ℕ) : ℝ)

theorem measurable_scaledCanonicalLevelArrival (law : PotentialLaw)
    (E δ θ φ : ℝ) (k : ℕ) :
    Measurable (scaledCanonicalLevelArrival law E δ θ φ k) :=
  measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    ((WithTop.measurable_untopD 0).comp
      (canonicalLevelCrossingTime_measurable E δ θ φ k)))

def scaledCanonicalLevelArrivalLaw (law : PotentialLaw) (E δ θ φ : ℝ) (k : ℕ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_scaledCanonicalLevelArrival law E δ θ φ k).aemeasurable

theorem scaledCanonicalLevelArrival_ae_sum (law : PotentialLaw)
    (input : Input law) (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (k : ℕ) :
    scaledCanonicalLevelArrival law E δ θ φ k =ᵐ[iidMeasure law]
      (exponentialSum k ∘ scaledCanonicalWaitingVector law E δ θ φ k) := by
  filter_upwards [canonicalLevelCrossingTime_ae_finite law input
    E δ θ φ hδ hδπ hinit hsmall hp k] with ω hω
  change _ = ∑ j : Fin k, (idsCandidate law (E + δ) - idsCandidate law E) *
    canonicalLevelWaitingTime E δ θ φ j.val ω
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (idsCandidate law (E + δ) - idsCandidate law E) *
      canonicalLevelWaitingTime E δ θ φ j ω) k, ← Finset.mul_sum,
    sum_canonicalLevelWaitingTime E δ θ φ hinit k ω hω]
  rfl

theorem scaledCanonicalLevelArrivalLaw_eq_map (law : PotentialLaw)
    (input : Input law) (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (k : ℕ) :
    scaledCanonicalLevelArrivalLaw law E δ θ φ k =
      (scaledCanonicalWaitingLaw law E δ θ φ k).map
        (continuous_exponentialSum k).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidMeasure law).map (scaledCanonicalLevelArrival law E δ θ φ k) =
    ((iidMeasure law).map (scaledCanonicalWaitingVector law E δ θ φ k)).map
      (exponentialSum k)
  rw [Measure.map_map (continuous_exponentialSum k).measurable
    (measurable_scaledCanonicalWaitingVector law E δ θ φ k)]
  exact Measure.map_congr (scaledCanonicalLevelArrival_ae_sum law input
    E δ θ φ hδ hδπ hinit hsmall hp k)

theorem scaledCanonicalLevelArrivalLaw_tendsto
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0)) (k : ℕ) :
    Tendsto (fun i => scaledCanonicalLevelArrivalLaw law (E i) (δ i) (θ i) (φ i) k)
      F (𝓝 (exponentialSumLaw k)) := by
  have hwait := scaledCanonicalWaitingLaw_tendsto_exponentialProduct law input hK
    E δ θ φ hE hE' hδ hinit hp hδlim hgap k
  have hsum := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hwait (continuous_exponentialSum k)
  apply hsum.congr'
  filter_upwards [hδlim.eventually (Iio_mem_nhds Real.pi_pos),
    hgap.eventually (Iio_mem_nhds Real.pi_pos)] with i hiδ higap
  exact (scaledCanonicalLevelArrivalLaw_eq_map law input (E i) (δ i) (θ i) (φ i)
    (hδ i) hiδ (hinit i) higap (hp i) k).symm

end FixedCouplingPoisson.Furstenberg


/-! The actual integer and natural crossing counts are precisely the
counts of the already constructed level-arrival times. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem canonicalCrossingCount_ge_iff_gap (E δ θ φ : ℝ)
    (k : ℤ) (n : ℕ) (ω : PotentialSpace) :
    k ≤ canonicalCrossingCount E δ θ φ n ω ↔
      (k : ℝ) * Real.pi ≤ canonicalGapProcess E δ θ φ n ω := by
  rw [canonicalCrossingCount, Int.le_floor, le_div_iff₀ Real.pi_pos]

theorem canonicalCrossingCount_ge_iff_arrival (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (k n : ℕ) (ω : PotentialSpace) :
    (k : ℤ) ≤ canonicalCrossingCount E δ θ φ n ω ↔
      canonicalLevelCrossingTime E δ θ φ k ω ≤ n := by
  rw [canonicalCrossingCount_ge_iff_gap,
    canonicalLevelCrossingTime_le_iff_gap E δ θ φ hδ]
  simp only [Int.cast_natCast]

theorem canonicalCrossingCount_nonneg (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (n : ℕ) (ω : PotentialSpace) :
    0 ≤ canonicalCrossingCount E δ θ φ n ω := by
  apply (canonicalCrossingCount_ge_iff_arrival E δ θ φ hδ 0 n ω).mpr
  rw [canonicalLevelCrossingTime_zero E δ θ φ hinit ω]
  exact bot_le

theorem canonicalCrossingCount_mono (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (ω : PotentialSpace) :
    Monotone (fun n => canonicalCrossingCount E δ θ φ n ω) := by
  intro j n hjn
  apply (canonicalCrossingCount_ge_iff_gap E δ θ φ _ n ω).mpr
  exact canonicalGapProcess_period_persists E δ θ φ hδ
    (canonicalCrossingCount E δ θ φ j ω) j n ω hjn
    ((canonicalCrossingCount_ge_iff_gap E δ θ φ _ j ω).mp le_rfl)

def canonicalNaturalCrossingCount (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℕ :=
  (canonicalCrossingCount E δ θ φ n ω).toNat

theorem canonicalNaturalCrossingCount_measurable (E δ θ φ : ℝ) (n : ℕ) :
    Measurable (canonicalNaturalCrossingCount E δ θ φ n) :=
  (measurable_of_countable Int.toNat).comp
    (canonicalCrossingCount_measurable E δ θ φ n)

theorem canonicalNaturalCrossingCount_ge_iff_arrival (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (k n : ℕ) (ω : PotentialSpace) :
    k ≤ canonicalNaturalCrossingCount E δ θ φ n ω ↔
      canonicalLevelCrossingTime E δ θ φ k ω ≤ n := by
  rw [canonicalNaturalCrossingCount,
    Int.le_toNat (canonicalCrossingCount_nonneg E δ θ φ hδ hinit n ω)]
  exact canonicalCrossingCount_ge_iff_arrival E δ θ φ hδ k n ω

theorem canonicalNaturalCrossingCount_ge_iff_scaled_arrival (E δ θ φ p : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hp : 0 < p) (k n : ℕ) (ω : PotentialSpace)
    (hfinite : canonicalLevelCrossingTime E δ θ φ k ω ≠ ⊤) :
    k ≤ canonicalNaturalCrossingCount E δ θ φ n ω ↔
      p * (((canonicalLevelCrossingTime E δ θ φ k ω).untopD 0 : ℕ) : ℝ) ≤
        p * (n : ℝ) := by
  rw [canonicalNaturalCrossingCount_ge_iff_arrival E δ θ φ hδ hinit,
    mul_le_mul_iff_right₀ hp, Nat.cast_le, WithTop.untopD_le_iff hfinite]
  rfl

def canonicalNaturalCrossingCountLaw (law : PotentialLaw) (E δ θ φ : ℝ) (n : ℕ) :
    ProbabilityMeasure ℕ :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (canonicalNaturalCrossingCount_measurable E δ θ φ n).aemeasurable

end FixedCouplingPoisson.Furstenberg


/-! Actual crossing-count tails at moving deterministic observation times.
The target here is the proved finite exponential-sum CDF; identification
with Poisson probabilities is a separate mathematical theorem. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem canonicalNaturalCrossingCount_tail_eq_arrival_probability
    (law : PotentialLaw) (input : Input law) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hδπ : δ < Real.pi) (hinit : φ ≤ θ)
    (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (k n : ℕ) :
    (iidMeasure law).real {ω | k ≤ canonicalNaturalCrossingCount E δ θ φ n ω} =
      (scaledCanonicalLevelArrivalLaw law E δ θ φ k : Measure ℝ).real
        (Iic ((idsCandidate law (E + δ) - idsCandidate law E) * (n : ℝ))) := by
  have hm : iidMeasure law {ω | k ≤ canonicalNaturalCrossingCount E δ θ φ n ω} =
      (scaledCanonicalLevelArrivalLaw law E δ θ φ k : Measure ℝ)
        (Iic ((idsCandidate law (E + δ) - idsCandidate law E) * (n : ℝ))) := by
    change _ = ((iidMeasure law).map (scaledCanonicalLevelArrival law E δ θ φ k)) _
    rw [Measure.map_apply (measurable_scaledCanonicalLevelArrival law E δ θ φ k)
      measurableSet_Iic]
    apply measure_congr
    filter_upwards [canonicalLevelCrossingTime_ae_finite law input
      E δ θ φ hδ hδπ hinit hsmall hp k] with ω hω
    exact propext (canonicalNaturalCrossingCount_ge_iff_scaled_arrival E δ θ φ
      (idsCandidate law (E + δ) - idsCandidate law E) hδ hinit hp k n ω hω)
  exact congrArg ENNReal.toReal hm

theorem canonicalNaturalCrossingCount_tail_tendsto
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0))
    (n : ι → ℕ) {t : ℝ}
    (htime : Tendsto (fun i =>
      (idsCandidate law (E i + δ i) - idsCandidate law (E i)) * (n i : ℝ)) F (𝓝 t))
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun i => (iidMeasure law).real
      {ω | k ≤ canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (n i) ω})
      F (𝓝 (cdf (exponentialSumLaw k : Measure ℝ) t)) := by
  have hw := scaledCanonicalLevelArrivalLaw_tendsto law input hK
    E δ θ φ hE hE' hδ hinit hp hδlim hgap k
  have hnull : ∀ x, (exponentialSumLaw k : Measure ℝ) {x} = 0 := by
    cases k with
    | zero => omega
    | succ k =>
      letI := exponentialSumLaw_succ_nullSingletonClass k
      exact fun x => measure_singleton x
  have hc : Continuous (cdf (exponentialSumLaw k : Measure ℝ)) := by
    cases k with
    | zero => omega
    | succ k => exact continuous_cdf_exponentialSumLaw_succ k
  have ht := cdf_moving_threshold_tendsto_of_weak hw hnull hc.continuousAt htime
  rw [← cdf_eq_real] at ht
  apply ht.congr'
  filter_upwards [hδlim.eventually (Iio_mem_nhds Real.pi_pos),
    hgap.eventually (Iio_mem_nhds Real.pi_pos)] with i hiδ higap
  exact (canonicalNaturalCrossingCount_tail_eq_arrival_probability law input
    (E i) (δ i) (θ i) (φ i) (hδ i) hiδ (hinit i) higap (hp i) k (n i)).symm

end FixedCouplingPoisson.Furstenberg
