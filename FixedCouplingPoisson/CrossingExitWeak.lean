import FixedCouplingPoisson.CDFExitUniform
import FixedCouplingPoisson.LaplaceWeak


/-! Factored proof group: CrossingExitWeak. -/

/-! Unchecked work draft. The real first-crossing random variables and
their actual iid laws converge to the mean-one exponential law. This
specializes the uniform exit estimate; it assumes no exit-limit interface.
The positive IDS increment also gives actual almost-sure finite times in
CDFDynamics, independently of the default value assigned at infinity. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology

def scaledCanonicalCrossingTime (law : PotentialLaw) (E δ θ φ : ℝ)
    (ω : PotentialSpace) : ℝ :=
  (idsCandidate law (E + δ) - idsCandidate law E) *
    (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)

theorem measurable_scaledCanonicalCrossingTime
    (law : PotentialLaw) (E δ θ φ : ℝ) :
    Measurable (scaledCanonicalCrossingTime law E δ θ φ) :=
  measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    ((WithTop.measurable_untopD 0).comp (canonicalCrossingTime_measurable E δ θ φ)))

def scaledCanonicalCrossingLaw (law : PotentialLaw) (E δ θ φ : ℝ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_scaledCanonicalCrossingTime law E δ θ φ).aemeasurable

/-- Uniformity in the two initial phases is used before selecting a
converging family. No convergence of either individual phase is needed. -/
theorem inverseCrossingLaplace_tendsto_small_gap
    {ι : Type*} {F : Filter ι} (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun i => ∫ ω, Real.exp
      (-t * scaledCanonicalCrossingTime law (E i) (δ i) (θ i) (φ i) ω)
      ∂iidMeasure law) F (𝓝 ((1 + t)⁻¹)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd, he⟩ := inverseCrossingLaplace_small_gap_uniform
    law input hK ht (half_pos hε)
  have hδevent : ∀ᶠ i in F, δ i < d := hδlim.eventually (Iio_mem_nhds hd)
  have hgapevent : ∀ᶠ i in F, θ i - φ i < min d Real.pi :=
    hgap.eventually (Iio_mem_nhds (lt_min hd Real.pi_pos))
  filter_upwards [hδevent, hgapevent] with i hiδ higap
  have hb := he (E i) (hE i) (δ i) (hδ i) (hE' i) hiδ
    (θ i) (φ i) (hinit i) higap (hp i)
  have hfun : (fun ω => Real.exp
      (-(t * (idsCandidate law (E i + δ i) - idsCandidate law (E i))) *
        (((canonicalCrossingTime (E i) (δ i) (θ i) (φ i) ω).untopD 0 : ℕ) : ℝ))) =
      (fun ω => Real.exp
        (-t * scaledCanonicalCrossingTime law (E i) (δ i) (θ i) (φ i) ω)) := by
    funext ω
    congr 1
    dsimp only [scaledCanonicalCrossingTime]
    ring
  rw [hfun] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt (half_lt_self hε)

/-- The actual iid pushforward laws have the ordinary weak exponential
limit, using positive integer Laplace transforms and the proved generic
probability identification. -/
theorem scaledCanonicalCrossingLaw_tendsto_exponentialOne
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0)) :
    Tendsto (fun i => scaledCanonicalCrossingLaw law (E i) (δ i) (θ i) (φ i))
      F (𝓝 exponentialOne) := by
  let P : ProbabilityMeasure PotentialSpace := ⟨iidMeasure law, inferInstance⟩
  apply laws_tendsto_exponentialOne_of_positive_integer_laplace P
    (fun i => scaledCanonicalCrossingTime law (E i) (δ i) (θ i) (φ i))
    (fun i => measurable_scaledCanonicalCrossingTime law (E i) (δ i) (θ i) (φ i))
    (fun i ω => mul_nonneg (hp i).le (Nat.cast_nonneg _))
  intro m _hm
  have h := inverseCrossingLaplace_tendsto_small_gap law input hK E δ θ φ
    hE hE' hδ hinit hp hδlim hgap (Nat.cast_nonneg m)
  simpa only [P, ProbabilityMeasure.coe_mk, one_div, add_comm] using h

end FixedCouplingPoisson.Furstenberg
