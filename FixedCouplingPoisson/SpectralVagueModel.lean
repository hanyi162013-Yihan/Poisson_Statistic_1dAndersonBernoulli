import FixedCouplingPoisson.OrderedDirichletSpectrum
import FixedCouplingPoisson.UnfoldedEndpointProcess
import FixedCouplingPoisson.IDSContinuity

/-! The original IDS and linear spectral measures, bundled in the genuine
vague space on the actual iid sample space. All finite-volume maps and
probability laws are measurable globally. Exact interval identities relate
these original point measures to the already used physical counts. -/
noncomputable section
namespace FixedCouplingPoisson
open Filter MeasureTheory Set Furstenberg
open scoped Topology ENNReal

def idsSpectralVagueProcess (law : PotentialLaw) (E : ℝ) (n : ℕ)
    (ω : PotentialSpace) : RealVagueMeasure :=
  RealVagueMeasure.ofMeasure
    (unfoldedSpectralMeasure n (potentialBlock 0 n ω) (idsCandidate law) E)

def linearSpectralVagueProcess (E ρ : ℝ) (n : ℕ)
    (ω : PotentialSpace) : RealVagueMeasure :=
  RealVagueMeasure.ofMeasure (linearSpectralMeasure n (potentialBlock 0 n ω) E ρ)

@[simp] theorem coe_idsSpectralVagueProcess (law : PotentialLaw) (E : ℝ) (n : ℕ)
    (ω : PotentialSpace) : (idsSpectralVagueProcess law E n ω : Measure ℝ) =
      unfoldedSpectralMeasure n (potentialBlock 0 n ω) (idsCandidate law) E := rfl

@[simp] theorem coe_linearSpectralVagueProcess (E ρ : ℝ) (n : ℕ)
    (ω : PotentialSpace) : (linearSpectralVagueProcess E ρ n ω : Measure ℝ) =
      linearSpectralMeasure n (potentialBlock 0 n ω) E ρ := rfl

theorem measurable_idsSpectralVagueProcess (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    Measurable (idsSpectralVagueProcess law E n) :=
  (measurable_unfoldedSpectralVagueMeasure n (idsCandidate law) E
    (continuous_idsCandidate law).measurable).comp (measurable_potentialBlock 0 n)

theorem measurable_linearSpectralVagueProcess (E ρ : ℝ) (n : ℕ) :
    Measurable (linearSpectralVagueProcess E ρ n) :=
  (measurable_linearSpectralVagueMeasure n E ρ).comp (measurable_potentialBlock 0 n)

def idsSpectralVagueLaw (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    ProbabilityMeasure RealVagueMeasure :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_idsSpectralVagueProcess law E n).aemeasurable

def linearSpectralVagueLaw (law : PotentialLaw) (E ρ : ℝ) (n : ℕ) :
    ProbabilityMeasure RealVagueMeasure :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_linearSpectralVagueProcess E ρ n).aemeasurable

@[simp] theorem coe_idsSpectralVagueLaw (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    (idsSpectralVagueLaw law E n : Measure RealVagueMeasure) =
      (iidMeasure law).map (idsSpectralVagueProcess law E n) := rfl

@[simp] theorem coe_linearSpectralVagueLaw (law : PotentialLaw) (E ρ : ℝ) (n : ℕ) :
    (linearSpectralVagueLaw law E ρ n : Measure RealVagueMeasure) =
      (iidMeasure law).map (linearSpectralVagueProcess E ρ n) := rfl

/-- The original IDS-normalized point measure has its exact finite cardinality
on every half-open interval, at every volume. -/
theorem idsSpectralVagueProcess_Ioc (law : PotentialLaw) (E : ℝ) (n : ℕ)
    (ω : PotentialSpace) (a b : ℝ) :
    (idsSpectralVagueProcess law E n ω : Measure ℝ) (Ioc a b) =
      (idsUnfoldedWindowCount law E n (potentialBlock 0 n ω) a b : ℝ≥0∞) :=
  unfoldedSpectralMeasure_Ioc n (potentialBlock 0 n ω) (idsCandidate law) E a b

theorem idsSpectralVagueProcess_real_Ioc (law : PotentialLaw) (E : ℝ) (n : ℕ)
    (ω : PotentialSpace) (a b : ℝ) :
    (idsSpectralVagueProcess law E n ω : Measure ℝ).real (Ioc a b) =
      (idsUnfoldedWindowCount law E n (potentialBlock 0 n ω) a b : ℝ) := by
  rw [measureReal_def, idsSpectralVagueProcess_Ioc]
  simp only [ENNReal.toReal_natCast]

theorem linearSpectralMeasure_Ioc (n : ℕ) (v : Fin n → ℝ) (E ρ a b : ℝ) :
    linearSpectralMeasure n v E ρ (Ioc a b) =
      ((Finset.univ.filter (fun i =>
        a < (n : ℝ) * ρ * (dirichletEigenvalues n v i - E) ∧
        (n : ℝ) * ρ * (dirichletEigenvalues n v i - E) ≤ b)).card : ℝ≥0∞) := by
  classical
  simp only [linearSpectralMeasure, Measure.finsetSum_apply,
    Measure.dirac_apply' _ measurableSet_Ioc, Set.indicator_apply,
    Set.mem_Ioc, Pi.one_apply]
  simp only [Finset.sum_boole]

theorem linearSpectralVagueProcess_real_Ioc (E ρ : ℝ) (n : ℕ)
    (ω : PotentialSpace) (a b : ℝ) :
    (linearSpectralVagueProcess E ρ n ω : Measure ℝ).real (Ioc a b) =
      (((Finset.univ.filter (fun i =>
        a < (n : ℝ) * ρ * (dirichletEigenvalues n (potentialBlock 0 n ω) i - E) ∧
        (n : ℝ) * ρ * (dirichletEigenvalues n (potentialBlock 0 n ω) i - E) ≤ b)).card : ℕ) : ℝ) := by
  rw [measureReal_def, coe_linearSpectralVagueProcess, linearSpectralMeasure_Ioc]
  simp only [ENNReal.toReal_natCast]

theorem linear_coordinate_mem_Ioc_iff {E ρ a b u : ℝ} {n : ℕ}
    (hn : 0 < n) (hρ : 0 < ρ) :
    (a < (n : ℝ) * ρ * (u - E) ∧ (n : ℝ) * ρ * (u - E) ≤ b) ↔
      (linearEndpoint E ρ a n < u ∧ u ≤ linearEndpoint E ρ b n) := by
  have hp : 0 < (n : ℝ) * ρ := mul_pos (Nat.cast_pos.mpr hn) hρ
  unfold linearEndpoint
  constructor
  · rintro ⟨ha, hb⟩
    have ha' : a / ((n : ℝ) * ρ) < u - E :=
      (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using ha)
    have hb' : u - E ≤ b / ((n : ℝ) * ρ) :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hb)
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    have ha' : a / ((n : ℝ) * ρ) < u - E := by linarith
    have hb' : u - E ≤ b / ((n : ℝ) * ρ) := by linarith
    exact ⟨by simpa only [mul_comm] using (div_lt_iff₀ hp).mp ha',
      by simpa only [mul_comm] using (le_div_iff₀ hp).mp hb'⟩

/-- The original linearly scaled interval count equals the actual physical
energy-window cardinality. No inverse IDS or local regularity is needed. -/
theorem linearSpectralVagueProcess_real_Ioc_eq_energyWindowCount
    (E ρ : ℝ) (n : ℕ) (ω : PotentialSpace) (a b : ℝ) (hn : 0 < n) (hρ : 0 < ρ) :
    (linearSpectralVagueProcess E ρ n ω : Measure ℝ).real (Ioc a b) =
      (dirichletEnergyWindowCount n (potentialBlock 0 n ω)
        (linearEndpoint E ρ a n) (linearEndpoint E ρ b n) : ℝ) := by
  classical
  rw [linearSpectralVagueProcess_real_Ioc]
  unfold dirichletEnergyWindowCount
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact linear_coordinate_mem_Ioc_iff hn hρ

/-- Actual inverse-IDS cuts identify every interval of the original point
measure eventually, on every iid sample. -/
theorem idsSpectralVagueProcess_real_Ioc_eventually_eq_energyWindowCount
    (law : PotentialLaw) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ ω : PotentialSpace,
      (idsSpectralVagueProcess law E n ω : Measure ℝ).real (Ioc a b) =
        (dirichletEnergyWindowCount n (potentialBlock 0 n ω)
          (idsUnfoldingEndpoint law E J a n) (idsUnfoldingEndpoint law E J b n) : ℝ) := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict a,
    idsUnfoldingEndpoint_eventually_target law hJ hstrict b,
    idsUnfoldingEndpoint_eventually_nhds law hJ hstrict a,
    idsUnfoldingEndpoint_eventually_nhds law hJ hstrict b,
    eventually_gt_atTop (0 : ℕ)] with n ha hb hna hnb hn
  intro ω
  rw [idsSpectralVagueProcess_real_Ioc,
    idsUnfoldedWindowCount_eq_energyWindowCount law hstrict hna hnb hn ha.2 hb.2]

end FixedCouplingPoisson
