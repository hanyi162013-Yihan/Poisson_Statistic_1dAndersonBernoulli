import FixedCouplingPoisson.SpectralCounting
import FixedCouplingPoisson.IIDModel
import FixedCouplingPoisson.RealVagueAtoms
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-! The original matrix spectral theorem reuses matrix indices through a
fixed permutation. Undoing that fixed permutation and reversing its
antitone list gives an increasing actual eigenvalue enumeration. Count
sublevels then prove measurability, including the original enumeration. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set

/-- This permutation depends only on the finite index type, not the potential. -/
def orderedDirichletIndexEquiv (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.revPerm : Fin n ≃ Fin n).trans
    ((finCongr (Fintype.card_fin n).symm).trans
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))))

def orderedDirichletEigenvalues (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => dirichletEigenvalues n v (orderedDirichletIndexEquiv n i)

theorem orderedDirichletEigenvalues_monotone (n : ℕ) (v : Fin n → ℝ) :
    Monotone (orderedDirichletEigenvalues n v) := by
  intro i j hij
  unfold orderedDirichletEigenvalues dirichletEigenvalues Matrix.IsHermitian.eigenvalues
    orderedDirichletIndexEquiv
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  apply Matrix.IsHermitian.eigenvalues₀_antitone
  change j.rev ≤ i.rev
  exact Fin.rev_le_rev.mpr hij

theorem orderedDirichletEigenvalues_count (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    (Finset.univ.filter (fun i => orderedDirichletEigenvalues n v i ≤ E)).card =
      nonstrictSpectralCount n v E := by
  classical
  unfold nonstrictSpectralCount
  apply Finset.card_equiv (orderedDirichletIndexEquiv n)
  intro i
  constructor
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

theorem orderedDirichletEigenvalue_le_iff_count (n : ℕ) (v : Fin n → ℝ) (i : Fin n) (E : ℝ) :
    orderedDirichletEigenvalues n v i ≤ E ↔ i.val < nonstrictSpectralCount n v E := by
  classical
  rw [← orderedDirichletEigenvalues_count]
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone
    (orderedDirichletEigenvalues_monotone n v)).symm

theorem measurable_orderedDirichletEigenvalue (n : ℕ) (i : Fin n) :
    Measurable (fun v : Fin n → ℝ => orderedDirichletEigenvalues n v i) := by
  apply measurable_of_Iic
  intro E
  have he : (fun v : Fin n → ℝ => orderedDirichletEigenvalues n v i) ⁻¹' Iic E =
      {v | i.val < nonstrictSpectralCount n v E} := by
    ext v
    exact orderedDirichletEigenvalue_le_iff_count n v i E
  rw [he]
  exact measurableSet_lt measurable_const (measurable_nonstrictSpectralCount n E)

/-- Each original spectral-theorem eigenvalue is measurable as well, since
its reindexing permutation is fixed before the potential is varied. -/
theorem measurable_dirichletEigenvalue (n : ℕ) (i : Fin n) :
    Measurable (fun v : Fin n → ℝ => dirichletEigenvalues n v i) := by
  simpa only [orderedDirichletEigenvalues, Equiv.apply_symm_apply] using
    measurable_orderedDirichletEigenvalue n ((orderedDirichletIndexEquiv n).symm i)

theorem finiteAtoms_orderedDirichletEigenvalues (n : ℕ) (v : Fin n → ℝ) :
    RealVagueMeasure.finiteAtoms (orderedDirichletEigenvalues n v) =
      RealVagueMeasure.finiteAtoms (dirichletEigenvalues n v) := by
  apply RealVagueMeasure.toMeasure_injective
  simp only [RealVagueMeasure.coe_finiteAtoms, orderedDirichletEigenvalues]
  exact Equiv.sum_comp (orderedDirichletIndexEquiv n) (fun i => Measure.dirac (dirichletEigenvalues n v i))

theorem measurable_dirichletPointMeasure (n : ℕ) :
    Measurable (fun v : Fin n → ℝ => RealVagueMeasure.finiteAtoms (dirichletEigenvalues n v)) :=
  RealVagueMeasure.continuous_finiteAtoms.measurable.comp
    (measurable_pi_lambda _ (measurable_dirichletEigenvalue n))

/-- Measurable energy marks include linear and IDS unfolding. -/
theorem measurable_dirichletMarkedPointMeasure (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (fun v : Fin n → ℝ =>
      RealVagueMeasure.finiteAtoms (fun i => g (dirichletEigenvalues n v i))) :=
  RealVagueMeasure.continuous_finiteAtoms.measurable.comp
    (measurable_pi_lambda _ (fun i => hg.comp (measurable_dirichletEigenvalue n i)))

theorem measurable_iidDirichletMarkedPointMeasure (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (fun ω : PotentialSpace => RealVagueMeasure.finiteAtoms
      (fun i => g (dirichletEigenvalues n (potentialBlock 0 n ω) i))) :=
  (measurable_dirichletMarkedPointMeasure n g hg).comp (measurable_potentialBlock 0 n)

/-- Direct finite window counts are measurable at every volume, without
selecting inverse cuts or assuming a locally strict mark. -/
theorem measurable_dirichletMarkedWindowCount (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (a b : ℝ) : Measurable (fun v : Fin n → ℝ =>
      (Finset.univ.filter (fun i =>
        a < g (dirichletEigenvalues n v i) ∧ g (dirichletEigenvalues n v i) ≤ b)).card) := by
  classical
  have hmark (i : Fin n) := hg.comp (measurable_dirichletEigenvalue n i)
  have hi (i : Fin n) : Measurable (fun v : Fin n → ℝ =>
      if a < g (dirichletEigenvalues n v i) ∧ g (dirichletEigenvalues n v i) ≤ b
        then (1 : ℕ) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_const (hmark i)).inter
      (measurableSet_le (hmark i) measurable_const)) measurable_const measurable_const
  simpa using Finset.univ.measurable_fun_sum (fun i _ => hi i)

/-- This is exactly the original IDS-unfolded spectral measure bundled in
the vague space, including coalescing marks and zero volume. -/
theorem finiteAtoms_unfoldedSpectralMeasure (n : ℕ) (v : Fin n → ℝ)
    (N : ℝ → ℝ) (E : ℝ) :
    RealVagueMeasure.finiteAtoms
      (fun i => (n : ℝ) * (N (dirichletEigenvalues n v i) - N E)) =
      RealVagueMeasure.ofMeasure (unfoldedSpectralMeasure n v N E) := rfl

theorem measurable_unfoldedSpectralVagueMeasure (n : ℕ) (N : ℝ → ℝ) (E : ℝ)
    (hN : Measurable N) :
    Measurable (fun v : Fin n → ℝ =>
      RealVagueMeasure.ofMeasure (unfoldedSpectralMeasure n v N E)) :=
  measurable_dirichletMarkedPointMeasure n (fun x => (n : ℝ) * (N x - N E))
    ((hN.sub measurable_const).const_mul (n : ℝ))

theorem finiteAtoms_linearSpectralMeasure (n : ℕ) (v : Fin n → ℝ) (E ρ : ℝ) :
    RealVagueMeasure.finiteAtoms
      (fun i => (n : ℝ) * ρ * (dirichletEigenvalues n v i - E)) =
      RealVagueMeasure.ofMeasure (linearSpectralMeasure n v E ρ) := rfl

theorem measurable_linearSpectralVagueMeasure (n : ℕ) (E ρ : ℝ) :
    Measurable (fun v : Fin n → ℝ =>
      RealVagueMeasure.ofMeasure (linearSpectralMeasure n v E ρ)) :=
  measurable_dirichletMarkedPointMeasure n (fun x => (n : ℝ) * ρ * (x - E))
    ((measurable_id.sub_const E).const_mul ((n : ℝ) * ρ))

end FixedCouplingPoisson
