import FixedCouplingPoisson.PhaseProcess


/-! Factored proof group: CrossingLevels. -/

/-! Unchecked work draft. Actual successive crossing levels for the
fixed-number restart argument. No independence of the waiting times at
finite energy separation is assumed or asserted. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set

def canonicalLevelCrossingTime (E δ θ φ : ℝ) (k : ℕ) : PotentialSpace → WithTop ℕ :=
  hittingAfter (canonicalGapProcess E δ θ φ) (Ici ((k : ℝ) * Real.pi)) 0

theorem canonicalLevelCrossingTime_one (E δ θ φ : ℝ) :
    canonicalLevelCrossingTime E δ θ φ 1 = canonicalCrossingTime E δ θ φ := by
  simp only [canonicalLevelCrossingTime, Nat.cast_one, one_mul, canonicalCrossingTime]

theorem canonicalLevelCrossingTime_isStoppingTime (E δ θ φ : ℝ) (k : ℕ) :
    IsStoppingTime potentialFiltration (canonicalLevelCrossingTime E δ θ φ k) :=
  (canonicalGapProcess_adapted E δ θ φ).isStoppingTime_hittingAfter measurableSet_Ici

theorem canonicalLevelCrossingTime_le_iff (E δ θ φ : ℝ)
    (k n : ℕ) (ω : PotentialSpace) :
    canonicalLevelCrossingTime E δ θ φ k ω ≤ n ↔
      ∃ j ≤ n, (k : ℝ) * Real.pi ≤ canonicalGapProcess E δ θ φ j ω :=
  hittingAfter_bot_le_iff

theorem canonicalLevelCrossingTime_le_iff_gap (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (k n : ℕ) (ω : PotentialSpace) :
    canonicalLevelCrossingTime E δ θ φ k ω ≤ n ↔
      (k : ℝ) * Real.pi ≤ canonicalGapProcess E δ θ φ n ω := by
  rw [canonicalLevelCrossingTime_le_iff]
  constructor
  · rintro ⟨j, hjn, hj⟩
    have h := canonicalGapProcess_period_persists E δ θ φ hδ (k : ℤ) j n ω hjn
    simpa only [Int.cast_natCast] using h (by simpa only [Int.cast_natCast] using hj)
  · intro hn
    exact ⟨n, le_rfl, hn⟩

theorem canonicalLevelCrossingTime_before (E δ θ φ : ℝ)
    (k n : ℕ) (ω : PotentialSpace)
    (hn : (n : WithTop ℕ) < canonicalLevelCrossingTime E δ θ φ k ω) :
    canonicalGapProcess E δ θ φ n ω < (k : ℝ) * Real.pi :=
  lt_of_not_ge (notMem_of_lt_hittingAfter hn (Nat.zero_le n))

theorem canonicalLevelCrossingTime_hits (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (k n : ℕ) (ω : PotentialSpace)
    (hn : canonicalLevelCrossingTime E δ θ φ k ω = n) :
    (k : ℝ) * Real.pi ≤ canonicalGapProcess E δ θ φ n ω :=
  (canonicalLevelCrossingTime_le_iff_gap E δ θ φ hδ k n ω).mp hn.le

theorem canonicalLevelCrossingTime_overshoot (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (k n : ℕ) (ω : PotentialSpace)
    (hn : canonicalLevelCrossingTime E δ θ φ k ω = ((n + 1 : ℕ) : WithTop ℕ)) :
    (k : ℝ) * Real.pi ≤ canonicalGapProcess E δ θ φ (n + 1) ω ∧
      canonicalGapProcess E δ θ φ (n + 1) ω ≤ (k : ℝ) * Real.pi + δ := by
  have hbefore : (n : WithTop ℕ) < canonicalLevelCrossingTime E δ θ φ k ω := by
    rw [hn]
    exact_mod_cast Nat.lt_succ_self n
  have hprev := canonicalLevelCrossingTime_before E δ θ φ k n ω hbefore
  have hcross := canonicalLevelCrossingTime_hits E δ θ φ hδ k (n + 1) ω hn
  simpa only [Int.cast_natCast] using
    canonicalGapProcess_crossing_overshoot E δ θ φ hδ (k : ℤ) n ω
      (by simpa only [Int.cast_natCast] using hprev)
      (by simpa only [Int.cast_natCast] using hcross)

theorem canonicalLevelCrossingTime_measurable (E δ θ φ : ℝ) (k : ℕ) :
    Measurable (canonicalLevelCrossingTime E δ θ φ k) := by
  apply measurable_of_Iic
  intro n
  induction n using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    exact pastMeasurableSpace_le n _
      ((canonicalLevelCrossingTime_isStoppingTime E δ θ φ k).measurableSet_le n)

theorem canonicalLevelCrossingTime_mono (E δ θ φ : ℝ) (ω : PotentialSpace) :
    Monotone (fun k => canonicalLevelCrossingTime E δ θ φ k ω) := by
  intro k l hkl
  change canonicalLevelCrossingTime E δ θ φ k ω ≤ canonicalLevelCrossingTime E δ θ φ l ω
  by_cases hl : canonicalLevelCrossingTime E δ θ φ l ω = ⊤
  · rw [hl]
    exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hl
  rw [← hn]
  obtain ⟨j, hjn, hj⟩ :=
    (canonicalLevelCrossingTime_le_iff E δ θ φ l n ω).mp hn.symm.le
  apply (canonicalLevelCrossingTime_le_iff E δ θ φ k n ω).mpr
  refine ⟨j, hjn, ?_⟩
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) Real.pi_pos.le).trans hj

theorem canonicalLevelCrossingTime_zero (E δ θ φ : ℝ) (hinit : φ ≤ θ)
    (ω : PotentialSpace) : canonicalLevelCrossingTime E δ θ φ 0 ω = 0 := by
  apply le_antisymm
  · apply (canonicalLevelCrossingTime_le_iff E δ θ φ 0 0 ω).mpr
    exact ⟨0, le_rfl, by simpa only [Nat.cast_zero, zero_mul,
      canonicalGapProcess_zero] using sub_nonneg.mpr hinit⟩
  · exact bot_le

/-- For positive levels the initial gap below pi forces a genuine
positive waiting time, so the actual overshoot lemma applies. -/
theorem canonicalLevelCrossingTime_hits_gap_bounds
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hsmall : θ - φ < Real.pi)
    (k n : ℕ) (hk : 0 < k) (ω : PotentialSpace)
    (hn : canonicalLevelCrossingTime E δ θ φ k ω = n) :
    (k : ℝ) * Real.pi ≤ canonicalGapProcess E δ θ φ n ω ∧
      canonicalGapProcess E δ θ φ n ω ≤ (k : ℝ) * Real.pi + δ := by
  cases n with
  | zero =>
    have hhit := canonicalLevelCrossingTime_hits E δ θ φ hδ k 0 ω hn
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    have hlevel : Real.pi ≤ (k : ℝ) * Real.pi := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1 Real.pi_pos.le
    have hgap0 : canonicalGapProcess E δ θ φ 0 ω = θ - φ := rfl
    rw [hgap0] at hhit
    exact False.elim (not_le_of_gt hsmall (hlevel.trans hhit))
  | succ n =>
    exact canonicalLevelCrossingTime_overshoot E δ θ φ hδ k n ω hn

/-- The first crossing after recentering is the next actual level event.
This pathwise identity permits a common phase depending on the entire past. -/
theorem canonicalLevelCrossingTime_restart_le_iff (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (k u n : ℕ) (ω : PotentialSpace) :
    canonicalCrossingTime E δ (canonicalPhaseProcess E θ u ω)
        (canonicalPhaseProcess (E + δ) φ u ω + (k : ℤ) * Real.pi)
        (potentialShift u ω) ≤ n ↔
      canonicalLevelCrossingTime E δ θ φ (k + 1) ω ≤ ((u + n : ℕ) : WithTop ℕ) := by
  rw [canonicalCrossingTime_le_iff_gap _ _ _ _ hδ,
    canonicalLevelCrossingTime_le_iff_gap _ _ _ _ hδ,
    canonicalGapProcess_restart]
  simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
  constructor <;> intro h <;> nlinarith

/-- The next-level waiting time is exactly the recentered first crossing
of the whole shifted path, with no finite-separation independence claim. -/
theorem canonicalLevelCrossingTime_restart_of_finite
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (k u m : ℕ) (ω : PotentialSpace)
    (hum : u ≤ m)
    (hm : canonicalLevelCrossingTime E δ θ φ (k + 1) ω = m) :
    canonicalCrossingTime E δ (canonicalPhaseProcess E θ u ω)
      (canonicalPhaseProcess (E + δ) φ u ω + (k : ℤ) * Real.pi)
      (potentialShift u ω) = ((m - u : ℕ) : WithTop ℕ) := by
  let S := canonicalCrossingTime E δ (canonicalPhaseProcess E θ u ω)
    (canonicalPhaseProcess (E + δ) φ u ω + (k : ℤ) * Real.pi) (potentialShift u ω)
  have hiff (n : ℕ) : S ≤ n ↔
      canonicalLevelCrossingTime E δ θ φ (k + 1) ω ≤ ((u + n : ℕ) : WithTop ℕ) :=
    canonicalLevelCrossingTime_restart_le_iff E δ θ φ hδ k u n ω
  apply le_antisymm
  · apply (hiff (m - u)).mpr
    rw [hm, Nat.add_sub_of_le hum]
  · by_contra hle
    have hlt : S < ((m - u : ℕ) : WithTop ℕ) := lt_of_not_ge hle
    have hne : S ≠ ⊤ := fun heq => by
      rw [heq] at hlt
      exact not_top_lt hlt
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hne
    have hjlt : j < m - u := by
      rw [← hj] at hlt
      exact WithTop.coe_lt_coe.mp hlt
    have hnext := (hiff j).mp hj.symm.le
    rw [hm] at hnext
    have hmle : m ≤ u + j := WithTop.coe_le_coe.mp hnext
    omega

end FixedCouplingPoisson
