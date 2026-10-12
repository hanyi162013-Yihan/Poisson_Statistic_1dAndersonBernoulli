import FixedCouplingPoisson.ActualJointBlockBudget
import FixedCouplingPoisson.JointBlockLimitEpsilon
import FixedCouplingPoisson.PoissonProduct

/-! Joint Poisson convergence of the actual adjacent crossing counts. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal

section Cluster
variable (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
  (e : ℕ → ℕ → ℝ) (s : ℕ) (E₀ : ℝ)
  (hcompact : ∀ n i, i ≤ s → e n i ∈ K)
  (horder : ∀ n i, i < s → e n i ≤ e n (i + 1))
  (houter : ∀ n, e n 0 ≤ e n s)
  (hp : ∀ n i, i < s → 0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
  (hpouter : ∀ n, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
  (helim : ∀ i, i ≤ s → Tendsto (fun n => e n i) atTop (𝓝 E₀))
  (w : Fin s → ℝ) (W : ℝ) (hw : ∀ i, 0 ≤ w i) (hW : 0 ≤ W)
  (hscale : ∀ i : Fin s, Tendsto (fun n =>
    (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (n : ℝ))
    atTop (𝓝 (w i)))
  (houterScale : Tendsto (fun n =>
    (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (n : ℝ)) atTop (𝓝 W))

include input hK hcompact horder houter hp hpouter helim hw hW hscale houterScale

/-- The true finite vector has the independent Poisson mixed Laplace limit.
No conditional-kernel, residual-tail, or count-law premise is left. -/
theorem canonicalColoredCount_laplace_tendsto (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Tendsto (fun n => ∫ ω, coloredLaplaceFactor t (fun i =>
      canonicalNaturalCrossingCount (e n i.val) (e n (i.val + 1) - e n i.val)
        0 0 n ω) ∂iidMeasure law) atTop
      (𝓝 (Real.exp (-(∑ i, firstArrivalWeight (t i) * w i)))) := by
  apply jointBlockLimit_of_twoStage_eventual_bound _
    (∑ i, firstArrivalWeight (t i) * w i) (coloredQuadraticBudget s w W)
  have hΛ : 0 ≤ ∑ i, firstArrivalWeight (t i) * w i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (firstArrivalWeight_bounds (ht i)).1 (hw i)
  filter_upwards [coloredLinearFactor_bounds_eventually _ hΛ] with m hm
  intro η hη
  exact canonicalColoredCount_twoStage_budget law input hK e s E₀
    hcompact horder houter hp hpouter helim w W hw hW hscale houterScale t ht
    hm.1 hm.2.1 η hη

end Cluster

def canonicalColoredCountVector (e : ℕ → ℝ) (s n : ℕ) (ω : PotentialSpace) : Fin s → ℕ :=
  fun i => canonicalNaturalCrossingCount (e i.val) (e (i.val + 1) - e i.val) 0 0 n ω

theorem canonicalColoredCountVector_measurable (e : ℕ → ℝ) (s n : ℕ) :
    Measurable (canonicalColoredCountVector e s n) :=
  measurable_pi_lambda _ fun i => canonicalNaturalCrossingCount_measurable _ _ _ _ _

def canonicalColoredCountRealLaw (law : PotentialLaw) (e : ℕ → ℝ) (s n : ℕ) :
    ProbabilityMeasure (Fin s → ℝ) :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    ((show Measurable (fun x : Fin s → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
      (canonicalColoredCountVector_measurable e s n)).aemeasurable

/-- Ordinary weak convergence of the actual real-valued count vector law to
the actual independent finite Poisson product. -/
theorem canonicalColoredCountRealLaw_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s : ℕ) (E₀ : ℝ)
    (hcompact : ∀ n i, i ≤ s → e n i ∈ K)
    (horder : ∀ n i, i < s → e n i ≤ e n (i + 1))
    (houter : ∀ n, e n 0 ≤ e n s)
    (hp : ∀ n i, i < s → 0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hpouter : ∀ n, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
    (helim : ∀ i, i ≤ s → Tendsto (fun n => e n i) atTop (𝓝 E₀))
    (w : Fin s → ℝ≥0) (W : ℝ) (hW : 0 ≤ W)
    (hscale : ∀ i : Fin s, Tendsto (fun n =>
      (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (n : ℝ))
      atTop (𝓝 (w i : ℝ)))
    (houterScale : Tendsto (fun n =>
      (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (n : ℝ)) atTop (𝓝 W)) :
    Tendsto (fun n => canonicalColoredCountRealLaw law (e n) s n)
      atTop (𝓝 (poissonRealProduct w)) := by
  apply poissonReal_laws_tendsto_of_mixed_integer_laplace
    (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (fun n => canonicalColoredCountVector (e n) s n)
    (fun n => canonicalColoredCountVector_measurable (e n) s n) w
  intro a
  have h := canonicalColoredCount_laplace_tendsto law input hK e s E₀
    hcompact horder houter hp hpouter helim (fun i => (w i : ℝ)) W
    (fun i => (w i).coe_nonneg) hW hscale houterScale
    (fun i => (a i : ℝ)) (fun i => Nat.cast_nonneg _)
  simpa only [coloredLaplaceFactor, poissonMixedLaplaceTest, canonicalColoredCountVector,
    firstArrivalWeight, ProbabilityMeasure.coe_mk, mul_comm] using h

end FixedCouplingPoisson.Furstenberg
