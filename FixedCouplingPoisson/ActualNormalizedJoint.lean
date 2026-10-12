import FixedCouplingPoisson.ActualIDSJoint
import FixedCouplingPoisson.ActualLinearJoint
import FixedCouplingPoisson.SpectralVagueWindowLaws

/-! Actual interval-vector laws of the original two normalized spectral point processes. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set Furstenberg
open scoped Topology NNReal

def partitionPoissonRates (x : ℕ → ℝ) (s : ℕ) (hx : StrictMonoOn x (Iic s)) :
    Fin s → ℝ≥0 := fun i =>
  ⟨x (i.val + 1) - x i.val, sub_nonneg.mpr
    (hx (by exact i.isLt.le) (by change i.val + 1 ≤ s; omega)
      (Nat.lt_succ_self i.val)).le⟩

/-- The count vectors belong to the original IDS-normalized point measure,
including eigenvalues outside the local inverse-IDS neighborhood. -/
theorem idsSpectralVagueWindowRealLaw_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J)
    (x : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hx : StrictMonoOn x (Iic s))
    (κ : ℕ) (hκ : κ ≤ s) (hzero : x κ = 0) :
    Tendsto (fun n => idsSpectralVagueWindowRealLaw law E x s n) atTop
      (𝓝 (poissonRealProduct (partitionPoissonRates x s hx))) := by
  have h := idsUnfolding_physicalWindowRealLaw_tendsto_poisson law input
    hJ hstrict x s hs hx κ hκ hzero
  apply h.congr'
  filter_upwards [idsSpectralVagueWindowRealLaw_eventually_eq_physical law hJ hstrict x s]
    with n hn
  exact hn.symm

theorem linearSpectralVagueWindowRealLaw_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ)
    (x : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hx : StrictMonoOn x (Iic s))
    (κ : ℕ) (hκ : κ ≤ s) (hzero : x κ = 0) :
    Tendsto (fun n => linearSpectralVagueWindowRealLaw law E ρ x s n) atTop
      (𝓝 (poissonRealProduct (partitionPoissonRates x s hx))) := by
  have h := linear_physicalWindowRealLaw_tendsto_poisson law input
    hderiv hρ x s hs hx κ hκ hzero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (linearSpectralVagueWindowRealLaw_eq_physical law E ρ x s n hn hρ).symm

/-- The same theorem stated as an intrinsic projection of the genuine
original vague-space probability law. -/
theorem idsSpectralVagueLaw_interval_projection_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J)
    (x : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hx : StrictMonoOn x (Iic s))
    (κ : ℕ) (hκ : κ ≤ s) (hzero : x κ = 0) :
    Tendsto (fun n => (idsSpectralVagueLaw law E n).map
      (RealVagueMeasure.measurable_intervalMassVector x s).aemeasurable) atTop
      (𝓝 (poissonRealProduct (partitionPoissonRates x s hx))) := by
  simpa only [map_idsSpectralVagueLaw_intervalMassVector] using
    idsSpectralVagueWindowRealLaw_tendsto_poisson law input hJ hstrict x s hs hx κ hκ hzero

theorem linearSpectralVagueLaw_interval_projection_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ)
    (x : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hx : StrictMonoOn x (Iic s))
    (κ : ℕ) (hκ : κ ≤ s) (hzero : x κ = 0) :
    Tendsto (fun n => (linearSpectralVagueLaw law E ρ n).map
      (RealVagueMeasure.measurable_intervalMassVector x s).aemeasurable) atTop
      (𝓝 (poissonRealProduct (partitionPoissonRates x s hx))) := by
  simpa only [map_linearSpectralVagueLaw_intervalMassVector] using
    linearSpectralVagueWindowRealLaw_tendsto_poisson law input hderiv hρ x s hs hx κ hκ hzero

end FixedCouplingPoisson
