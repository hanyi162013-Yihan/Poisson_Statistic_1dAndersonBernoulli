import FixedCouplingPoisson.CrossingJointWeak

/-! The actual successive crossing locations are sums of the proved
consecutive waits. Their finite-dimensional laws converge by the genuine
continuous partial-sum map. No arrival-law premise is introduced. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Telescope natural waiting times when the terminal extended time is finite. -/
theorem sum_withTop_waiting_times (τ : ℕ → WithTop ℕ) (hτ : Monotone τ)
    (hzero : τ 0 = 0) (m : ℕ) (hfinite : τ m ≠ ⊤) :
    (∑ j ∈ Finset.range m, ((τ (j + 1)).untopD 0 - (τ j).untopD 0 : ℕ)) =
      (τ m).untopD 0 := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero, hzero]
    rfl
  | succ m ih =>
    have hle : τ m ≤ τ (m + 1) := hτ (Nat.le_succ m)
    have hm : τ m ≠ ⊤ := ne_top_of_le_ne_top hfinite hle
    have hn : (τ m).untopD 0 ≤ (τ (m + 1)).untopD 0 :=
      WithTop.untopD_mono hfinite hle
    rw [Finset.sum_range_succ, ih hm]
    omega

/-- The continuous vector of all nonempty partial sums. -/
def arrivalPartialSums {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ k : Fin (j.val + 1), x ⟨k.val, k.isLt.trans_le (Nat.succ_le_of_lt j.isLt)⟩

theorem continuous_arrivalPartialSums (m : ℕ) :
    Continuous (arrivalPartialSums (m := m)) := by
  apply continuous_pi
  intro j
  exact continuous_finsetSum _ fun k _ =>
    continuous_apply (⟨k.val, k.isLt.trans_le (Nat.succ_le_of_lt j.isLt)⟩ : Fin m)

/-- The actual law of the first finitely many locations in exponential renewal. -/
def exponentialArrivalVectorLaw (m : ℕ) : ProbabilityMeasure (Fin m → ℝ) :=
  ProbabilityMeasure.map (exponentialProduct (Fin m))
    (continuous_arrivalPartialSums m).measurable.aemeasurable

namespace Furstenberg

theorem sum_canonicalLevelWaitingTime (E δ θ φ : ℝ) (hinit : φ ≤ θ)
    (m : ℕ) (ω : PotentialSpace)
    (hfinite : canonicalLevelCrossingTime E δ θ φ m ω ≠ ⊤) :
    (∑ j ∈ Finset.range m, canonicalLevelWaitingTime E δ θ φ j ω) =
      (((canonicalLevelCrossingTime E δ θ φ m ω).untopD 0 : ℕ) : ℝ) := by
  have h := sum_withTop_waiting_times
    (fun j => canonicalLevelCrossingTime E δ θ φ j ω)
    (canonicalLevelCrossingTime_mono E δ θ φ ω)
    (canonicalLevelCrossingTime_zero E δ θ φ hinit ω) m hfinite
  change (∑ j ∈ Finset.range m,
    (((canonicalLevelCrossingTime E δ θ φ (j + 1) ω).untopD 0 -
      (canonicalLevelCrossingTime E δ θ φ j ω).untopD 0 : ℕ) : ℝ)) = _
  rw [← Nat.cast_sum]
  exact congrArg (fun n : ℕ => (n : ℝ)) h

def scaledCanonicalArrivalVector (law : PotentialLaw) (E δ θ φ : ℝ) (m : ℕ)
    (ω : PotentialSpace) (j : Fin m) : ℝ :=
  (idsCandidate law (E + δ) - idsCandidate law E) *
    (((canonicalLevelCrossingTime E δ θ φ (j.val + 1) ω).untopD 0 : ℕ) : ℝ)

theorem measurable_scaledCanonicalArrivalVector (law : PotentialLaw)
    (E δ θ φ : ℝ) (m : ℕ) :
    Measurable (scaledCanonicalArrivalVector law E δ θ φ m) :=
  measurable_pi_lambda _ fun j => measurable_const.mul
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((WithTop.measurable_untopD 0).comp
        (canonicalLevelCrossingTime_measurable E δ θ φ (j.val + 1))))

theorem scaledCanonicalArrivalVector_ae_partialSums (law : PotentialLaw)
    (input : Input law) (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (m : ℕ) :
    scaledCanonicalArrivalVector law E δ θ φ m =ᵐ[iidMeasure law]
      (arrivalPartialSums ∘ scaledCanonicalWaitingVector law E δ θ φ m) := by
  have hf : ∀ᵐ ω ∂iidMeasure law, ∀ j : Fin m,
      canonicalLevelCrossingTime E δ θ φ (j.val + 1) ω ≠ ⊤ :=
    eventually_all.mpr fun j => canonicalLevelCrossingTime_ae_finite law input
      E δ θ φ hδ hδπ hinit hsmall hp (j.val + 1)
  filter_upwards [hf] with ω hω
  funext j
  change _ = ∑ k : Fin (j.val + 1),
    (idsCandidate law (E + δ) - idsCandidate law E) *
      canonicalLevelWaitingTime E δ θ φ k.val ω
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (idsCandidate law (E + δ) - idsCandidate law E) *
      canonicalLevelWaitingTime E δ θ φ k ω) (j.val + 1), ← Finset.mul_sum,
    sum_canonicalLevelWaitingTime E δ θ φ hinit (j.val + 1) ω (hω j)]
  rfl

def scaledCanonicalArrivalVectorLaw (law : PotentialLaw) (E δ θ φ : ℝ) (m : ℕ) :
    ProbabilityMeasure (Fin m → ℝ) :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_scaledCanonicalArrivalVector law E δ θ φ m).aemeasurable

theorem scaledCanonicalArrivalVectorLaw_eq_map (law : PotentialLaw)
    (input : Input law) (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hδπ : δ < Real.pi)
    (hinit : φ ≤ θ) (hsmall : θ - φ < Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) (m : ℕ) :
    scaledCanonicalArrivalVectorLaw law E δ θ φ m =
      (scaledCanonicalWaitingLaw law E δ θ φ m).map
        (continuous_arrivalPartialSums m).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (iidMeasure law).map (scaledCanonicalArrivalVector law E δ θ φ m) =
    ((iidMeasure law).map (scaledCanonicalWaitingVector law E δ θ φ m)).map
      arrivalPartialSums
  rw [Measure.map_map (continuous_arrivalPartialSums m).measurable
    (measurable_scaledCanonicalWaitingVector law E δ θ φ m)]
  exact Measure.map_congr (scaledCanonicalArrivalVector_ae_partialSums law input
    E δ θ φ hδ hδπ hinit hsmall hp m)

/-- Full actual finite-dimensional arrival convergence, uniformly through
arbitrary allowed energy/initial-state families. -/
theorem scaledCanonicalArrivalVectorLaw_tendsto
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0)) (m : ℕ) :
    Tendsto (fun i => scaledCanonicalArrivalVectorLaw law (E i) (δ i) (θ i) (φ i) m)
      F (𝓝 (exponentialArrivalVectorLaw m)) := by
  have hwait := scaledCanonicalWaitingLaw_tendsto_exponentialProduct law input hK
    E δ θ φ hE hE' hδ hinit hp hδlim hgap m
  have hsum := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hwait (continuous_arrivalPartialSums m)
  apply hsum.congr'
  filter_upwards [hδlim.eventually (Iio_mem_nhds Real.pi_pos),
    hgap.eventually (Iio_mem_nhds Real.pi_pos)] with i hiδ higap
  exact (scaledCanonicalArrivalVectorLaw_eq_map law input (E i) (δ i) (θ i) (φ i)
    (hδ i) hiδ (hinit i) higap (hp i) m).symm

end Furstenberg
end FixedCouplingPoisson
