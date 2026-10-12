import FixedCouplingPoisson.PhaseProcess
import FixedCouplingPoisson.IIDRestart

/-!
# Actual upper-layer hitting and full-future restart

The stopping time is computed from the actual two-energy canonical gap.
Restarting before a finite first crossing preserves its entire remaining
waiting time. The stopped pair and whole stopped future have their actual
iid product law, obtained from the already proved iid freshness theorem.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set Filter

/-- First entrance into the actual upper layer, including time zero. -/
def canonicalUpperLayerTime (E δ θ φ h : ℝ) : PotentialSpace → WithTop ℕ :=
  hittingAfter (canonicalGapProcess E δ θ φ) (Ici (Real.pi - h)) 0

theorem canonicalUpperLayerTime_isStoppingTime (E δ θ φ h : ℝ) :
    IsStoppingTime potentialFiltration (canonicalUpperLayerTime E δ θ φ h) :=
  (canonicalGapProcess_adapted E δ θ φ).isStoppingTime_hittingAfter measurableSet_Ici

theorem canonicalUpperLayerTime_le_iff (E δ θ φ h : ℝ) (n : ℕ) (ω : PotentialSpace) :
    canonicalUpperLayerTime E δ θ φ h ω ≤ n ↔
      ∃ j ≤ n, Real.pi - h ≤ canonicalGapProcess E δ θ φ j ω :=
  hittingAfter_bot_le_iff

theorem canonicalUpperLayerTime_before (E δ θ φ h : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : (n : WithTop ℕ) < canonicalUpperLayerTime E δ θ φ h ω) :
    canonicalGapProcess E δ θ φ n ω < Real.pi - h :=
  lt_of_not_ge (notMem_of_lt_hittingAfter hn (Nat.zero_le n))

theorem canonicalUpperLayerTime_hits (E δ θ φ h : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : canonicalUpperLayerTime E δ θ φ h ω = n) :
    Real.pi - h ≤ canonicalGapProcess E δ θ φ n ω := by
  obtain ⟨j, hjn, hj⟩ := (canonicalUpperLayerTime_le_iff E δ θ φ h n ω).mp hn.le
  by_cases hjeq : j = n
  · simpa only [hjeq] using hj
  · have hjlt : j < n := lt_of_le_of_ne hjn hjeq
    have hjbefore : (j : WithTop ℕ) < canonicalUpperLayerTime E δ θ φ h ω := by
      rw [hn]
      exact_mod_cast hjlt
    exact False.elim (not_le_of_gt
      (canonicalUpperLayerTime_before E δ θ φ h j ω hjbefore) hj)

/-- The upper layer is reached no later than the full crossing, pathwise. -/
theorem canonicalUpperLayerTime_le_crossing (E δ θ φ h : ℝ) (hh : 0 ≤ h)
    (ω : PotentialSpace) :
    canonicalUpperLayerTime E δ θ φ h ω ≤ canonicalCrossingTime E δ θ φ ω := by
  by_cases htop : canonicalCrossingTime E δ θ φ ω = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hm]
  apply (canonicalUpperLayerTime_le_iff E δ θ φ h m ω).mpr
  exact ⟨m, le_rfl, by linarith [canonicalCrossingTime_hits E δ θ φ m ω hm.symm]⟩

theorem canonicalUpperLayerTime_ae_finite (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    ∀ᵐ ω ∂iidMeasure law, canonicalUpperLayerTime E δ θ φ h ω ≠ ⊤ := by
  filter_upwards [hfinite] with ω hω
  intro htop
  have hle := canonicalUpperLayerTime_le_crossing E δ θ φ h hh ω
  rw [htop] at hle
  exact hω (top_le_iff.mp hle)

private theorem measurable_gap_level_time_initial_path (E δ a : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × PotentialSpace =>
      hittingAfter (canonicalGapProcess E δ z.1.1 z.1.2) (Ici a) 0 z.2) := by
  apply measurable_of_Iic
  intro n
  induction n using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    change MeasurableSet {z : (ℝ × ℝ) × PotentialSpace |
      hittingAfter (canonicalGapProcess E δ z.1.1 z.1.2) (Ici a) 0 z.2 ≤ (n : WithTop ℕ)}
    have heq : {z : (ℝ × ℝ) × PotentialSpace |
        hittingAfter (canonicalGapProcess E δ z.1.1 z.1.2) (Ici a) 0 z.2 ≤ (n : WithTop ℕ)} =
        ⋃ j : ℕ, ⋃ (_ : j ≤ n),
          {z : (ℝ × ℝ) × PotentialSpace | a ≤ canonicalGapProcess E δ z.1.1 z.1.2 j z.2} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      exact hittingAfter_bot_le_iff
        (u := canonicalGapProcess E δ z.1.1 z.1.2) (s := Ici a) (i := n) (ω := z.2)
    rw [heq]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun (_ : j ≤ n) =>
      measurableSet_le measurable_const (canonicalGapProcess_measurable_initial_path E δ j)

/-- This includes the initial pair and every future coordinate jointly. -/
theorem canonicalCrossingTime_measurable_initial_path (E δ : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × PotentialSpace =>
      canonicalCrossingTime E δ z.1.1 z.1.2 z.2) :=
  measurable_gap_level_time_initial_path E δ Real.pi

theorem canonicalUpperLayerTime_measurable_initial_path (E δ h : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × PotentialSpace =>
      canonicalUpperLayerTime E δ z.1.1 z.1.2 h z.2) :=
  measurable_gap_level_time_initial_path E δ (Real.pi - h)

theorem canonicalUpperLayerTime_measurable (E δ θ φ h : ℝ) :
    Measurable (canonicalUpperLayerTime E δ θ φ h) := by
  have hm : Measurable (fun ω : PotentialSpace => ((θ, φ), ω)) :=
    measurable_const.prodMk measurable_id
  exact (canonicalUpperLayerTime_measurable_initial_path E δ h).comp hm

/-- Restarting at any fixed time before a finite first crossing gives exactly
the natural-number difference, rather than a comparison of one-step events. -/
theorem canonicalCrossingTime_restart_of_finite (E δ θ φ : ℝ) (t m : ℕ)
    (ω : PotentialSpace) (htm : t ≤ m)
    (hT : canonicalCrossingTime E δ θ φ ω = m) :
    canonicalCrossingTime E δ (canonicalPhaseProcess E θ t ω)
      (canonicalPhaseProcess (E + δ) φ t ω) (potentialShift t ω) =
        ((m - t : ℕ) : WithTop ℕ) := by
  let θt := canonicalPhaseProcess E θ t ω
  let φt := canonicalPhaseProcess (E + δ) φ t ω
  have hrestart (n : ℕ) : canonicalGapProcess E δ θt φt n (potentialShift t ω) =
      canonicalGapProcess E δ θ φ (t + n) ω := by
    simpa only [Int.cast_zero, zero_mul, add_zero, sub_zero] using
      canonicalGapProcess_restart E δ θ φ t n (0 : ℤ) ω
  apply le_antisymm
  · apply (canonicalCrossingTime_le_iff E δ θt φt (m - t) (potentialShift t ω)).mpr
    refine ⟨m - t, le_rfl, ?_⟩
    rw [hrestart, Nat.add_sub_of_le htm]
    exact canonicalCrossingTime_hits E δ θ φ m ω hT
  · by_contra hle
    have hlt : canonicalCrossingTime E δ θt φt (potentialShift t ω) <
        ((m - t : ℕ) : WithTop ℕ) := lt_of_not_ge hle
    have hne : canonicalCrossingTime E δ θt φt (potentialShift t ω) ≠ ⊤ := by
      intro heq
      rw [heq] at hlt
      exact not_top_lt hlt
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hne
    have hjlt : j < m - t := by
      rw [← hj] at hlt
      exact WithTop.coe_lt_coe.mp hlt
    have hhit := canonicalCrossingTime_hits E δ θt φt j (potentialShift t ω) hj.symm
    rw [hrestart] at hhit
    have hbefore : ((t + j : ℕ) : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω := by
      rw [hT]
      exact_mod_cast (show t + j < m by omega)
    exact not_le_of_gt (canonicalCrossingTime_before E δ θ φ (t + j) ω hbefore) hhit

/-- The actual real phase pair at the upper-layer stopping time. -/
def canonicalUpperLayerState (E δ θ φ h : ℝ) (ω : PotentialSpace) : ℝ × ℝ :=
  (stoppedValue (canonicalPhaseProcess E θ) (canonicalUpperLayerTime E δ θ φ h) ω,
    stoppedValue (canonicalPhaseProcess (E + δ) φ) (canonicalUpperLayerTime E δ θ φ h) ω)

theorem canonicalUpperLayerState_stopped_measurable (E δ θ φ h : ℝ) :
    Measurable[(canonicalUpperLayerTime_isStoppingTime E δ θ φ h).measurableSpace]
      (canonicalUpperLayerState E δ θ φ h) :=
  (canonicalPhaseProcess_stopped_measurable E θ
    (canonicalUpperLayerTime_isStoppingTime E δ θ φ h)).prodMk
      (canonicalPhaseProcess_stopped_measurable (E + δ) φ
        (canonicalUpperLayerTime_isStoppingTime E δ θ φ h))

theorem canonicalUpperLayerState_eq_of_time (E δ θ φ h : ℝ) (t : ℕ)
    (ω : PotentialSpace) (ht : canonicalUpperLayerTime E δ θ φ h ω = t) :
    canonicalUpperLayerState E δ θ φ h ω =
      (canonicalPhaseProcess E θ t ω, canonicalPhaseProcess (E + δ) φ t ω) := by
  simp only [canonicalUpperLayerState, stoppedValue, ht, WithTop.untopA]
  rfl

/-- A finite entrance before the full crossing lies in the actual half-open upper layer. -/
theorem canonicalUpperLayerState_gap_mem (E δ θ φ h : ℝ) (t : ℕ)
    (ω : PotentialSpace) (ht : canonicalUpperLayerTime E δ θ φ h ω = t)
    (hbefore : (t : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω) :
    (canonicalUpperLayerState E δ θ φ h ω).1 -
      (canonicalUpperLayerState E δ θ φ h ω).2 ∈ Ico (Real.pi - h) Real.pi := by
  rw [canonicalUpperLayerState_eq_of_time E δ θ φ h t ω ht]
  exact ⟨canonicalUpperLayerTime_hits E δ θ φ h t ω ht,
    canonicalCrossingTime_before E δ θ φ t ω hbefore⟩

/-- Already crossed initial states have exactly zero waiting time on every future. -/
theorem canonicalCrossingTime_eq_zero_of_gap (E δ θ φ : ℝ)
    (hgap : Real.pi ≤ θ - φ) (ω : PotentialSpace) :
    canonicalCrossingTime E δ θ φ ω = 0 := by
  apply le_antisymm
  · apply (canonicalCrossingTime_le_iff E δ θ φ 0 ω).mpr
    exact ⟨0, le_rfl, hgap⟩
  · exact bot_le

/-- The full remaining crossing at the stopped state uses the whole stopped iid future. -/
theorem canonicalUpperLayerTime_crossing_restart (E δ θ φ h : ℝ) (hh : 0 ≤ h)
    (ω : PotentialSpace) (hfinite : canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    canonicalCrossingTime E δ (canonicalUpperLayerState E δ θ φ h ω).1
      (canonicalUpperLayerState E δ θ φ h ω).2
      (stoppedPotentialFuture (canonicalUpperLayerTime E δ θ φ h) ω) =
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 -
          (canonicalUpperLayerTime E δ θ φ h ω).untopD 0 : ℕ) : WithTop ℕ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hne : canonicalUpperLayerTime E δ θ φ h ω ≠ ⊤ := by
    intro htop
    have hle := canonicalUpperLayerTime_le_crossing E δ θ φ h hh ω
    rw [htop] at hle
    exact hfinite (top_le_iff.mp hle)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  have htm : t ≤ m := by
    have hle := canonicalUpperLayerTime_le_crossing E δ θ φ h hh ω
    rw [← hm, ← ht] at hle
    exact_mod_cast hle
  rw [canonicalUpperLayerState_eq_of_time E δ θ φ h t ω ht.symm]
  have hfuture : stoppedPotentialFuture (canonicalUpperLayerTime E δ θ φ h) ω =
      potentialShift t ω := by
    simp only [stoppedPotentialFuture, ← ht, WithTop.untopD_coe]
  rw [hfuture, ← hm, ← ht, WithTop.untopD_coe]
  exact canonicalCrossingTime_restart_of_finite E δ θ φ t m ω htm hm.symm

theorem iidMeasure_upperLayer_state_future_map (law : PotentialLaw) (E δ θ φ h : ℝ)
    (hh : 0 ≤ h)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, canonicalCrossingTime E δ θ φ ω ≠ ⊤) :
    (iidMeasure law).map (fun ω => (canonicalUpperLayerState E δ θ φ h ω,
      stoppedPotentialFuture (canonicalUpperLayerTime E δ θ φ h) ω)) =
        ((iidMeasure law).map (canonicalUpperLayerState E δ θ φ h)).prod (iidMeasure law) :=
  iidMeasure_stopped_state_future_map law
    (canonicalUpperLayerTime_isStoppingTime E δ θ φ h)
    (canonicalUpperLayerTime_ae_finite law E δ θ φ h hh hfinite)
    (canonicalUpperLayerState_stopped_measurable E δ θ φ h)

end FixedCouplingPoisson
