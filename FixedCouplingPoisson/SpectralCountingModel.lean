import FixedCouplingPoisson.SpectralVagueModel
import FixedCouplingPoisson.RealCountingWeak

/-! Genuine counting-space lifts of the original normalized finite Dirichlet
spectra. The displayed laws are actual iid pushforwards and their vague
images equal the original model laws exactly at every volume. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory

theorem measurable_iidDirichletMarkedCountingMeasure (n : ℕ) (g : ℝ → ℝ)
    (hg : Measurable g) : Measurable (fun ω : PotentialSpace =>
      RealCountingMeasure.finiteAtoms
        (fun i => g (dirichletEigenvalues n (potentialBlock 0 n ω) i))) :=
  (RealCountingMeasure.continuous_finiteAtoms.measurable.comp
    (measurable_pi_lambda _ fun i => hg.comp (measurable_dirichletEigenvalue n i))).comp
      (measurable_potentialBlock 0 n)

def idsSpectralCountingProcess (law : PotentialLaw) (E : ℝ) (n : ℕ)
    (ω : PotentialSpace) : RealCountingMeasure :=
  RealCountingMeasure.finiteAtoms (fun i =>
    (n : ℝ) * (idsCandidate law (dirichletEigenvalues n (potentialBlock 0 n ω) i) -
      idsCandidate law E))

def linearSpectralCountingProcess (E ρ : ℝ) (n : ℕ)
    (ω : PotentialSpace) : RealCountingMeasure :=
  RealCountingMeasure.finiteAtoms (fun i =>
    (n : ℝ) * ρ * (dirichletEigenvalues n (potentialBlock 0 n ω) i - E))

@[simp] theorem toVague_idsSpectralCountingProcess (law : PotentialLaw) (E : ℝ)
    (n : ℕ) (ω : PotentialSpace) :
    RealCountingMeasure.toVague (idsSpectralCountingProcess law E n ω) =
      idsSpectralVagueProcess law E n ω := rfl

@[simp] theorem toVague_linearSpectralCountingProcess (E ρ : ℝ)
    (n : ℕ) (ω : PotentialSpace) :
    RealCountingMeasure.toVague (linearSpectralCountingProcess E ρ n ω) =
      linearSpectralVagueProcess E ρ n ω := rfl

@[simp] theorem coe_idsSpectralCountingProcess (law : PotentialLaw) (E : ℝ)
    (n : ℕ) (ω : PotentialSpace) :
    (idsSpectralCountingProcess law E n ω : Measure ℝ) =
      unfoldedSpectralMeasure n (potentialBlock 0 n ω) (idsCandidate law) E := rfl

@[simp] theorem coe_linearSpectralCountingProcess (E ρ : ℝ)
    (n : ℕ) (ω : PotentialSpace) :
    (linearSpectralCountingProcess E ρ n ω : Measure ℝ) =
      linearSpectralMeasure n (potentialBlock 0 n ω) E ρ := rfl

theorem measurable_idsSpectralCountingProcess (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    Measurable (idsSpectralCountingProcess law E n) := by
  apply RealCountingMeasure.measurable_iff_toVague.mpr
  simpa only [Function.comp_def, toVague_idsSpectralCountingProcess] using
    measurable_idsSpectralVagueProcess law E n

theorem measurable_linearSpectralCountingProcess (E ρ : ℝ) (n : ℕ) :
    Measurable (linearSpectralCountingProcess E ρ n) := by
  apply RealCountingMeasure.measurable_iff_toVague.mpr
  simpa only [Function.comp_def, toVague_linearSpectralCountingProcess] using
    measurable_linearSpectralVagueProcess E ρ n

def idsSpectralCountingLaw (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    ProbabilityMeasure RealCountingMeasure :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_idsSpectralCountingProcess law E n).aemeasurable

def linearSpectralCountingLaw (law : PotentialLaw) (E ρ : ℝ) (n : ℕ) :
    ProbabilityMeasure RealCountingMeasure :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_linearSpectralCountingProcess E ρ n).aemeasurable

@[simp] theorem coe_idsSpectralCountingLaw (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    (idsSpectralCountingLaw law E n : Measure RealCountingMeasure) =
      (iidMeasure law).map (idsSpectralCountingProcess law E n) := rfl

@[simp] theorem coe_linearSpectralCountingLaw (law : PotentialLaw) (E ρ : ℝ) (n : ℕ) :
    (linearSpectralCountingLaw law E ρ n : Measure RealCountingMeasure) =
      (iidMeasure law).map (linearSpectralCountingProcess E ρ n) := rfl

theorem idsSpectralCountingLaw_map_toVague (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    (idsSpectralCountingLaw law E n).map RealCountingMeasure.measurable_toVague.aemeasurable =
      idsSpectralVagueLaw law E n := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((iidMeasure law).map (idsSpectralCountingProcess law E n)).map
      RealCountingMeasure.toVague =
    (iidMeasure law).map (idsSpectralVagueProcess law E n)
  rw [Measure.map_map RealCountingMeasure.measurable_toVague
    (measurable_idsSpectralCountingProcess law E n)]
  rfl

theorem linearSpectralCountingLaw_map_toVague (law : PotentialLaw) (E ρ : ℝ) (n : ℕ) :
    (linearSpectralCountingLaw law E ρ n).map RealCountingMeasure.measurable_toVague.aemeasurable =
      linearSpectralVagueLaw law E ρ n := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((iidMeasure law).map (linearSpectralCountingProcess E ρ n)).map
      RealCountingMeasure.toVague =
    (iidMeasure law).map (linearSpectralVagueProcess E ρ n)
  rw [Measure.map_map RealCountingMeasure.measurable_toVague
    (measurable_linearSpectralCountingProcess E ρ n)]
  rfl

end FixedCouplingPoisson
