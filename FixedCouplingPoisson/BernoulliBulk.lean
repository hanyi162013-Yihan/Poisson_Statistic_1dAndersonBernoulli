import FixedCouplingPoisson.BernoulliBlockMass
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-! The manuscript's Bernoulli local strictness conclusion, proved by
selective constant-block cutting. Full upper support inclusion is not
needed for this conclusion and is not asserted here. -/
noncomputable section
namespace FixedCouplingPoisson
open ProbabilityTheory MeasureTheory Set
open scoped Topology

def bernoulliClosedBands (a b : ℝ) : Set ℝ :=
  Icc (a - 2) (a + 2) ∪ Icc (b - 2) (b + 2)

theorem bernoulliLaw_mass_right (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (bernoulliLaw a b hab p hp0 hp1).measure.real {b} = 1 - p := by
  exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton b)
    (by simpa using hab.ne) (by simp)

/-- A nonempty open interval contained in the two closed bands contains
an interior point of at least one band, including when the bands touch. -/
theorem exists_openBand_point_of_interval_subset (a b E F : ℝ) (hEF : E < F)
    (hsub : Ioo E F ⊆ bernoulliClosedBands a b) :
    ∃ z ∈ Ioo E F, z ∈ Ioo (a - 2) (a + 2) ∪ Ioo (b - 2) (b + 2) := by
  let endpoints : Set ℝ := {a - 2, a + 2, b - 2, b + 2}
  have hinfinite := (Set.Ioo_infinite hEF).sdiff (show endpoints.Finite by simp [endpoints])
  obtain ⟨z, hz⟩ := hinfinite.nonempty
  have hza₀ : z ≠ a - 2 := by intro h; exact hz.2 (by simp [endpoints, h])
  have hza₁ : z ≠ a + 2 := by intro h; exact hz.2 (by simp [endpoints, h])
  have hzb₀ : z ≠ b - 2 := by intro h; exact hz.2 (by simp [endpoints, h])
  have hzb₁ : z ≠ b + 2 := by intro h; exact hz.2 (by simp [endpoints, h])
  refine ⟨z, hz.1, ?_⟩
  rcases hsub hz.1 with ha | hb
  · left
    constructor
    · exact lt_of_le_of_ne ha.1 hza₀.symm
    · exact lt_of_le_of_ne ha.2 hza₁
  · right
    constructor
    · exact lt_of_le_of_ne hb.1 hzb₀.symm
    · exact lt_of_le_of_ne hb.2 hzb₁

/-- Canonical Bernoulli IDS is strictly increasing on any open interval
contained in the closed bands. This includes an interval across a touching
band edge; it never assumes strictness as an external input. -/
theorem bernoulli_idsCandidate_strictMonoOn_interval (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (lo hi : ℝ) (hsub : Ioo lo hi ⊆ bernoulliClosedBands a b) :
    StrictMonoOn (idsCandidate (bernoulliLaw a b hab p hp0 hp1)) (Ioo lo hi) := by
  intro E hE F hF hEF
  have hEFsub : Ioo E F ⊆ bernoulliClosedBands a b := by
    intro z hz
    exact hsub ⟨hE.1.trans hz.1, hz.2.trans hF.2⟩
  obtain ⟨z, hz, hza | hzb⟩ := exists_openBand_point_of_interval_subset a b E F hEF hEFsub
  · have hm : 0 < (bernoulliLaw a b hab p hp0 hp1).measure.real {a} := by
      rw [bernoulliLaw_mass_left]
      exact hp0
    exact sub_pos.mp (idsCandidate_increment_pos_of_atom _ a E F z hm hza hz)
  · have hm : 0 < (bernoulliLaw a b hab p hp0 hp1).measure.real {b} := by
      rw [bernoulliLaw_mass_right]
      linarith
    exact sub_pos.mp (idsCandidate_increment_pos_of_atom _ b E F z hm hzb hz)

/-- The local strictness used for the paper's Bernoulli unfolding: every
interior energy has an open neighborhood where the actual canonical IDS
is strictly increasing. -/
theorem bernoulli_idsCandidate_locally_strictMono (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (E : ℝ)
    (hE : E ∈ interior (bernoulliClosedBands a b)) :
    ∃ lo hi : ℝ, E ∈ Ioo lo hi ∧ Ioo lo hi ⊆ bernoulliClosedBands a b ∧
      StrictMonoOn (idsCandidate (bernoulliLaw a b hab p hp0 hp1)) (Ioo lo hi) := by
  have hn := mem_interior_iff_mem_nhds.mp hE
  obtain ⟨lo, hi, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  exact ⟨lo, hi, hmem, hsub,
    bernoulli_idsCandidate_strictMonoOn_interval a b hab p hp0 hp1 lo hi hsub⟩

/-- Neighborhood form accepted directly by the IDS unfolding endpoint API. -/
theorem bernoulli_idsCandidate_strictMonoOn_nhds (a b : ℝ) (hab : a < b)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (E : ℝ)
    (hE : E ∈ interior (bernoulliClosedBands a b)) :
    ∃ J : Set ℝ, J ∈ 𝓝 E ∧
      StrictMonoOn (idsCandidate (bernoulliLaw a b hab p hp0 hp1)) J := by
  obtain ⟨lo, hi, hmem, _, hstrict⟩ :=
    bernoulli_idsCandidate_locally_strictMono a b hab p hp0 hp1 E hE
  exact ⟨Ioo lo hi, Ioo_mem_nhds hmem.1 hmem.2, hstrict⟩

end FixedCouplingPoisson
