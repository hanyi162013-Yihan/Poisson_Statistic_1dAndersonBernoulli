import FixedCouplingPoisson.PoissonStepFunctions
import FixedCouplingPoisson.RealVagueSpace

/-! Zero-anchored finite interval partitions uniformly approximate genuine C_c tests. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter
open scoped Topology CompactlySupported BigOperators

/-- The first endpoint above a point puts it in one adjacent half-open cell. -/
theorem exists_adjacent_Ioc_of_mem {x : ℕ → ℝ} {s : ℕ} {y : ℝ}
    (hy : y ∈ Ioc (x 0) (x s)) :
    ∃ i : Fin s, y ∈ Ioc (x i.val) (x (i.val + 1)) := by
  let hex : ∃ j, y ≤ x j := ⟨s, hy.2⟩
  let j := Nat.find hex
  have hjle : j ≤ s := Nat.find_min' hex hy.2
  have hjpos : 0 < j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    have hspec := Nat.find_spec hex
    change y ≤ x j at hspec
    rw [hj0] at hspec
    exact (not_le_of_gt hy.1) hspec
  have hjlt : j - 1 < j := by omega
  have hprev : x (j - 1) < y := lt_of_not_ge (Nat.find_min hex hjlt)
  refine ⟨⟨j - 1, by omega⟩, hprev, ?_⟩
  have heq : j - 1 + 1 = j := by omega
  simpa only [heq] using Nat.find_spec hex

/-- Strictly ordered endpoints give pairwise disjoint adjacent half-open cells. -/
theorem adjacent_Ioc_pairwise_disjoint (x : ℕ → ℝ) (s : ℕ)
    (hx : StrictMonoOn x (Iic s)) :
    Pairwise (fun i j : Fin s => Disjoint
      (Ioc (x i.val) (x (i.val + 1))) (Ioc (x j.val) (x (j.val + 1)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : x (i.val + 1) ≤ x j.val :=
      hx.monotoneOn (by change i.val + 1 ≤ s; omega) j.isLt.le (by change i.val < j.val at h; omega)
    exact (not_lt_of_ge (hyi.2.trans hle)) hyj.1
  · have hle : x (j.val + 1) ≤ x i.val :=
      hx.monotoneOn (by change j.val + 1 ≤ s; omega) i.isLt.le (by change j.val < i.val at h; omega)
    exact (not_lt_of_ge (hyj.2.trans hle)) hyi.1

def symmetricGrid (R : ℝ) (m i : ℕ) : ℝ := (i : ℝ) * (R / m) - R

theorem symmetricGrid_strictMono {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m) :
    StrictMono (symmetricGrid R m) := by
  intro i j hij
  exact sub_lt_sub_right (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij)
    (div_pos hR (Nat.cast_pos.mpr hm))) R

theorem symmetricGrid_endpoints (R : ℝ) {m : ℕ} (hm : 0 < m) :
    symmetricGrid R m 0 = -R ∧ symmetricGrid R m m = 0 ∧
      symmetricGrid R m (2 * m) = R := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  unfold symmetricGrid
  constructor
  · simp
  constructor <;> push_cast <;> field_simp [hm0] <;> ring

def symmetricStep (f : C_c(ℝ, ℝ)) (R : ℝ) (m : ℕ) : ℝ → ℝ :=
  poissonStepDensity (fun i : Fin (2 * m) =>
    Ioc (symmetricGrid R m i.val) (symmetricGrid R m (i.val + 1)))
    (fun i => f (symmetricGrid R m i.val))

theorem exists_symmetric_support_window (f : C_c(ℝ, ℝ)) :
    ∃ R : ℝ, 0 < R ∧ tsupport f ⊆ Ioo (-R) R := by
  obtain ⟨a, ha⟩ := f.hasCompactSupport.bddBelow
  obtain ⟨b, hb⟩ := f.hasCompactSupport.bddAbove
  obtain ⟨r, hr⟩ := exists_nat_gt (max (max (-a) b) 0)
  refine ⟨r, (le_max_right _ _).trans_lt hr, ?_⟩
  intro y hy
  have hA : -a < (r : ℝ) := ((le_max_left (-a) b).trans
    (le_max_left (max (-a) b) 0)).trans_lt hr
  have hB : b < (r : ℝ) := ((le_max_right (-a) b).trans
    (le_max_left (max (-a) b) 0)).trans_lt hr
  constructor <;> linarith [ha hy, hb hy]

/-- The partition is symmetric, includes zero exactly, and never asks for
continuity of an interval indicator or for convergence of expected counts. -/
theorem symmetricStep_uniform_approx (f : C_c(ℝ, ℝ)) {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport f ⊆ Ioo (-R) R) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : ℝ, |f y - symmetricStep f R m y| ≤ η := by
  classical
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp (CompactlySupportedContinuousMapClass.uniformContinuous f) η hη
  obtain ⟨m, hm⟩ := exists_nat_gt (max (R / δ) 0)
  have hmpos : 0 < m := Nat.cast_pos.mp ((le_max_right _ _).trans_lt hm)
  have hmesh : R / (m : ℝ) < δ := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hmpos)).mpr
    have h := (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hm)
    nlinarith
  have hx := (symmetricGrid_strictMono hR hmpos).strictMonoOn (Iic (2 * m))
  have hend := symmetricGrid_endpoints R hmpos
  refine ⟨m, hmpos, fun y => ?_⟩
  by_cases hy : y ∈ Ioc (-R) R
  · obtain ⟨i, hi⟩ := exists_adjacent_Ioc_of_mem
      (x := symmetricGrid R m) (s := 2 * m) (by simpa only [hend.1, hend.2.2] using hy)
    have hdist : dist y (symmetricGrid R m i.val) < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hi.1)]
      have hwidth : symmetricGrid R m (i.val + 1) - symmetricGrid R m i.val = R / m := by
        simp only [symmetricGrid, Nat.cast_add, Nat.cast_one]
        ring
      calc
        y - symmetricGrid R m i.val ≤
            symmetricGrid R m (i.val + 1) - symmetricGrid R m i.val := sub_le_sub_right hi.2 _
        _ = R / m := hwidth
        _ < δ := hmesh
    have h := hclose hdist
    change dist (f y) (f (symmetricGrid R m i.val)) < η at h
    rw [symmetricStep, poissonStepDensity_eq_of_mem _ _
      (adjacent_Ioc_pairwise_disjoint _ _ hx) y i hi]
    exact (by simpa only [Real.dist_eq] using h.le)
  · have hnot (i : Fin (2 * m)) : y ∉ Ioc (symmetricGrid R m i.val)
        (symmetricGrid R m (i.val + 1)) := by
      intro hi
      apply hy
      have hleft := hx.monotoneOn (Nat.zero_le (2 * m)) i.isLt.le (Nat.zero_le _)
      have hright := hx.monotoneOn (by change i.val + 1 ≤ 2 * m; omega) (by change 2 * m ≤ 2 * m; exact le_rfl)
        (by change i.val + 1 ≤ 2 * m; omega)
      constructor
      · exact (by simpa only [hend.1] using hleft.trans_lt hi.1)
      · exact (by simpa only [hend.2.2] using hi.2.trans hright)
    have hfzero : f y = 0 := by
      by_contra hne
      have hs := hsupp (subset_tsupport f (Function.mem_support.mpr hne))
      exact hy ⟨hs.1, hs.2.le⟩
    rw [symmetricStep, poissonStepDensity_eq_zero_of_not_mem _ _ y hnot, hfzero, sub_zero,
      abs_zero]
    exact hη.le

end FixedCouplingPoisson
