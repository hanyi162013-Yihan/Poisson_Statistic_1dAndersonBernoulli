import FixedCouplingPoisson.Law
import FixedCouplingPoisson.Spectral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete spectral quantities

Definitions refer to the actual finite Dirichlet matrix and its spectral-theorem
list, and to finite products of the actual potential law. The IDS limit and the
Poisson limit are NOT asserted by this module. In particular no unspecified IDS
or unproved limiting law is installed as a class assumption.
-/
namespace FixedCouplingPoisson
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The finite-volume iid law; the coupling is part of `law.measure`. -/
noncomputable def finitePotentialMeasure (law : PotentialLaw) (n : ℕ) :
    Measure (Fin n → ℝ) := Measure.pi (fun _ => law.measure)

instance finitePotentialMeasure_probability (law : PotentialLaw) (n : ℕ) :
    IsProbabilityMeasure (finitePotentialMeasure law n) := by
  dsimp [finitePotentialMeasure]
  infer_instance

/-- Expected non-strict eigenvalue count for the actual n-site operator. -/
noncomputable def meanSpectralCount (law : PotentialLaw) (n : ℕ) (E : ℝ) : ℝ :=
  ∫ v, (nonstrictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n

noncomputable def normalizedMeanCount (law : PotentialLaw) (E : ℝ) (n : ℕ) : ℝ :=
  meanSpectralCount law n E / (n : ℝ)

/-- Canonical candidate value; proving that this limsup is the actual limit is
an outstanding IDS-existence obligation. -/
noncomputable def idsCandidate (law : PotentialLaw) (E : ℝ) : ℝ :=
  limsup (normalizedMeanCount law E) atTop

/-- A proposition describing the required limit, with no inhabitant assumed. -/
def HasIDS (law : PotentialLaw) (N : ℝ → ℝ) : Prop :=
  ∀ E, Tendsto (normalizedMeanCount law E) atTop (𝓝 (N E))

/-- IDS-unfolded finite spectral counting measure. -/
noncomputable def unfoldedSpectralMeasure (n : ℕ) (v : Fin n → ℝ)
    (N : ℝ → ℝ) (E : ℝ) : Measure ℝ :=
  ∑ i : Fin n, Measure.dirac ((n : ℝ) * (N (dirichletEigenvalues n v i) - N E))

/-- Linearly scaled finite spectral counting measure. -/
noncomputable def linearSpectralMeasure (n : ℕ) (v : Fin n → ℝ)
    (E ρ : ℝ) : Measure ℝ :=
  ∑ i : Fin n, Measure.dirac ((n : ℝ) * ρ * (dirichletEigenvalues n v i - E))

/-- Finite spectral measures keep exactly n atoms, even if unfolding coalesces
some of their locations. -/
theorem unfoldedSpectralMeasure_univ (n : ℕ) (v : Fin n → ℝ) (N : ℝ → ℝ) (E : ℝ) :
    unfoldedSpectralMeasure n v N E Set.univ = n := by
  simp [unfoldedSpectralMeasure]

theorem linearSpectralMeasure_univ (n : ℕ) (v : Fin n → ℝ) (E ρ : ℝ) :
    linearSpectralMeasure n v E ρ Set.univ = n := by
  simp [linearSpectralMeasure]

instance unfoldedSpectralMeasure_finite (n : ℕ) (v : Fin n → ℝ) (N : ℝ → ℝ) (E : ℝ) :
    IsFiniteMeasure (unfoldedSpectralMeasure n v N E) := by
  dsimp [unfoldedSpectralMeasure]
  infer_instance

instance linearSpectralMeasure_finite (n : ℕ) (v : Fin n → ℝ) (E ρ : ℝ) :
    IsFiniteMeasure (linearSpectralMeasure n v E ρ) := by
  dsimp [linearSpectralMeasure]
  infer_instance

/-- The IDS-unfolded interval mass counts all actual eigenvalues, with exact
half-open endpoint convention. -/
theorem unfoldedSpectralMeasure_Ioc (n : ℕ) (v : Fin n → ℝ)
    (N : ℝ → ℝ) (E a b : ℝ) :
    unfoldedSpectralMeasure n v N E (Set.Ioc a b) =
      ((Finset.univ.filter (fun i : Fin n =>
        a < (n : ℝ) * (N (dirichletEigenvalues n v i) - N E) ∧
        (n : ℝ) * (N (dirichletEigenvalues n v i) - N E) ≤ b)).card : ℝ≥0∞) := by
  classical
  simp only [unfoldedSpectralMeasure, Measure.finsetSum_apply,
    Measure.dirac_apply' _ measurableSet_Ioc, Set.indicator_apply,
    Set.mem_Ioc, Pi.one_apply]
  simp only [Finset.sum_boole]

end FixedCouplingPoisson
