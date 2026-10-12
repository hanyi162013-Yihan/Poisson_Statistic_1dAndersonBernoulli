import FixedCouplingPoisson.SpectralVagueModel
import FixedCouplingPoisson.ActualJointSpectral
import FixedCouplingPoisson.RealVagueEvaluation

/-! The actual interval-mass vectors of the original normalized point measures.
Their laws are genuine pushforwards of the iid measure at every volume.
Exact finite-volume or eventual equalities identify them with the physical
Dirichlet window laws used in the proved joint Poisson theorem. -/
noncomputable section
namespace FixedCouplingPoisson
open Filter MeasureTheory Set Furstenberg
open scoped Topology

/-- Intrinsic interval evaluation of a genuine locally finite measure. -/
def RealVagueMeasure.intervalMassVector (x : ℕ → ℝ) (s : ℕ)
    (μ : RealVagueMeasure) : Fin s → ℝ := fun i =>
  (μ : Measure ℝ).real (Ioc (x i.val) (x (i.val + 1)))

theorem RealVagueMeasure.measurable_intervalMassVector (x : ℕ → ℝ) (s : ℕ) :
    Measurable (RealVagueMeasure.intervalMassVector x s) :=
  measurable_pi_lambda _ fun i =>
    RealVagueMeasure.measurable_measureReal_Ioc (x i.val) (x (i.val + 1))

def idsSpectralVagueWindowVector (law : PotentialLaw) (E : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) (ω : PotentialSpace) : Fin s → ℝ := fun i =>
  (idsSpectralVagueProcess law E n ω : Measure ℝ).real (Ioc (x i.val) (x (i.val + 1)))

def linearSpectralVagueWindowVector (E ρ : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) (ω : PotentialSpace) : Fin s → ℝ := fun i =>
  (linearSpectralVagueProcess E ρ n ω : Measure ℝ).real (Ioc (x i.val) (x (i.val + 1)))

/-- All volumes, including zero: the actual vague interval vector is exactly
its finite eigenvalue-cardinality vector cast to the reals. -/
theorem idsSpectralVagueWindowVector_eq_card (law : PotentialLaw) (E : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) (ω : PotentialSpace) :
    idsSpectralVagueWindowVector law E x s n ω = fun i =>
      (idsUnfoldedWindowCount law E n (potentialBlock 0 n ω)
        (x i.val) (x (i.val + 1)) : ℝ) := by
  funext i
  exact idsSpectralVagueProcess_real_Ioc law E n ω _ _

theorem linearSpectralVagueWindowVector_eq_card (E ρ : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) (ω : PotentialSpace) :
    linearSpectralVagueWindowVector E ρ x s n ω = fun i =>
      (((Finset.univ.filter (fun j =>
        x i.val < (n : ℝ) * ρ * (dirichletEigenvalues n (potentialBlock 0 n ω) j - E) ∧
        (n : ℝ) * ρ * (dirichletEigenvalues n (potentialBlock 0 n ω) j - E) ≤
          x (i.val + 1))).card : ℕ) : ℝ) := by
  funext i
  exact linearSpectralVagueProcess_real_Ioc E ρ n ω _ _

theorem measurable_idsSpectralVagueWindowVector (law : PotentialLaw) (E : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) : Measurable (idsSpectralVagueWindowVector law E x s n) := by
  apply measurable_pi_lambda
  intro i
  have hg : Measurable (fun z : ℝ => (n : ℝ) * (idsCandidate law z - idsCandidate law E)) :=
    ((continuous_idsCandidate law).measurable.sub_const _).const_mul _
  have hm := (measurable_dirichletMarkedWindowCount n _ hg (x i.val) (x (i.val + 1))).comp
    (measurable_potentialBlock 0 n)
  have hc := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm
  convert hc using 1
  funext ω
  simp only [idsSpectralVagueWindowVector, idsSpectralVagueProcess_real_Ioc,
    idsUnfoldedWindowCount, dirichletUnfoldedWindowCount, dirichletUnfoldedCoordinate,
    Function.comp_def]
  apply congrArg (fun k : ℕ => (k : ℝ))
  apply congrArg Finset.card
  ext j
  constructor
  · intro hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩

theorem measurable_linearSpectralVagueWindowVector (E ρ : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) : Measurable (linearSpectralVagueWindowVector E ρ x s n) := by
  apply measurable_pi_lambda
  intro i
  have hg : Measurable (fun z : ℝ => (n : ℝ) * ρ * (z - E)) :=
    (measurable_id.sub_const E).const_mul _
  have hm := (measurable_dirichletMarkedWindowCount n _ hg (x i.val) (x (i.val + 1))).comp
    (measurable_potentialBlock 0 n)
  have hc := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm
  simpa only [linearSpectralVagueWindowVector, linearSpectralVagueProcess_real_Ioc,
    Function.comp_def] using hc

def idsSpectralVagueWindowRealLaw (law : PotentialLaw) (E : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) : ProbabilityMeasure (Fin s → ℝ) :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_idsSpectralVagueWindowVector law E x s n).aemeasurable

def linearSpectralVagueWindowRealLaw (law : PotentialLaw) (E ρ : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) : ProbabilityMeasure (Fin s → ℝ) :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_linearSpectralVagueWindowVector E ρ x s n).aemeasurable

/-- The interval vector law is the projection of the original vague law,
not a separately chosen substitute random object. -/
theorem map_idsSpectralVagueLaw_intervalMassVector (law : PotentialLaw) (E : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) :
    (idsSpectralVagueLaw law E n).map
      (RealVagueMeasure.measurable_intervalMassVector x s).aemeasurable =
      idsSpectralVagueWindowRealLaw law E x s n := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((iidMeasure law).map (idsSpectralVagueProcess law E n)).map
    (RealVagueMeasure.intervalMassVector x s) =
      (iidMeasure law).map (idsSpectralVagueWindowVector law E x s n)
  rw [Measure.map_map (RealVagueMeasure.measurable_intervalMassVector x s)
    (measurable_idsSpectralVagueProcess law E n)]
  rfl

theorem map_linearSpectralVagueLaw_intervalMassVector (law : PotentialLaw) (E ρ : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) :
    (linearSpectralVagueLaw law E ρ n).map
      (RealVagueMeasure.measurable_intervalMassVector x s).aemeasurable =
      linearSpectralVagueWindowRealLaw law E ρ x s n := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((iidMeasure law).map (linearSpectralVagueProcess E ρ n)).map
    (RealVagueMeasure.intervalMassVector x s) =
      (iidMeasure law).map (linearSpectralVagueWindowVector E ρ x s n)
  rw [Measure.map_map (RealVagueMeasure.measurable_intervalMassVector x s)
    (measurable_linearSpectralVagueProcess E ρ n)]
  rfl

@[simp] theorem coe_idsSpectralVagueWindowRealLaw (law : PotentialLaw) (E : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) :
    (idsSpectralVagueWindowRealLaw law E x s n : Measure (Fin s → ℝ)) =
      (iidMeasure law).map (idsSpectralVagueWindowVector law E x s n) := rfl

@[simp] theorem coe_linearSpectralVagueWindowRealLaw (law : PotentialLaw) (E ρ : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) :
    (linearSpectralVagueWindowRealLaw law E ρ x s n : Measure (Fin s → ℝ)) =
      (iidMeasure law).map (linearSpectralVagueWindowVector E ρ x s n) := rfl

theorem idsSpectralVagueWindowVector_eventually_eq_physical
    (law : PotentialLaw) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (s : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ ω : PotentialSpace,
      idsSpectralVagueWindowVector law E x s n ω =
        fun i => (actualEnergyWindowCountVector (idsUnfoldingEndpointArray law E J x)
          s n ω i : ℝ) := by
  have hs : ∀ i : Fin s, ∀ᶠ n : ℕ in atTop, ∀ ω : PotentialSpace,
      (idsSpectralVagueProcess law E n ω : Measure ℝ).real (Ioc (x i.val) (x (i.val + 1))) =
        (dirichletEnergyWindowCount n (potentialBlock 0 n ω)
          (idsUnfoldingEndpoint law E J (x i.val) n)
          (idsUnfoldingEndpoint law E J (x (i.val + 1)) n) : ℝ) :=
    fun i => idsSpectralVagueProcess_real_Ioc_eventually_eq_energyWindowCount law hJ hstrict _ _
  filter_upwards [Filter.eventually_all.mpr hs] with n hn
  intro ω
  funext i
  have hblock : potentialBlock 0 n ω = (fun j : Fin n => ω j.val) := by
    funext j
    exact congrArg ω (Nat.zero_add j.val)
  simpa only [idsSpectralVagueWindowVector, actualEnergyWindowCountVector,
    idsUnfoldingEndpointArray, hblock] using hn i ω

theorem linearSpectralVagueWindowVector_eq_physical (E ρ : ℝ) (x : ℕ → ℝ)
    (s n : ℕ) (hn : 0 < n) (hρ : 0 < ρ) (ω : PotentialSpace) :
    linearSpectralVagueWindowVector E ρ x s n ω =
      fun i => (actualEnergyWindowCountVector (fun n i => linearEndpoint E ρ (x i) n)
        s n ω i : ℝ) := by
  funext i
  have hblock : potentialBlock 0 n ω = (fun j : Fin n => ω j.val) := by
    funext j
    exact congrArg ω (Nat.zero_add j.val)
  simpa only [linearSpectralVagueWindowVector, actualEnergyWindowCountVector, hblock] using
    linearSpectralVagueProcess_real_Ioc_eq_energyWindowCount E ρ n ω
      (x i.val) (x (i.val + 1)) hn hρ

theorem idsSpectralVagueWindowRealLaw_eventually_eq_physical
    (law : PotentialLaw) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (s : ℕ) :
    ∀ᶠ n : ℕ in atTop, idsSpectralVagueWindowRealLaw law E x s n =
      actualEnergyWindowCountRealLaw law (idsUnfoldingEndpointArray law E J x) s n := by
  filter_upwards [idsSpectralVagueWindowVector_eventually_eq_physical law hJ hstrict x s]
    with n hn
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_congr (Eventually.of_forall hn)

theorem linearSpectralVagueWindowRealLaw_eq_physical (law : PotentialLaw) (E ρ : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) (hn : 0 < n) (hρ : 0 < ρ) :
    linearSpectralVagueWindowRealLaw law E ρ x s n =
      actualEnergyWindowCountRealLaw law (fun n i => linearEndpoint E ρ (x i) n) s n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_congr (Eventually.of_forall
    (linearSpectralVagueWindowVector_eq_physical E ρ x s n hn hρ))

end FixedCouplingPoisson
