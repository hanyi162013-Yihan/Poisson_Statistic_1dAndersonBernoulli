import FixedCouplingPoisson.CanonicalPhase
import FixedCouplingPoisson.IIDModel
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
The actual transfer phase on the canonical iid sample space. At time `n` the
phase has used exactly the potential sites `0, …, n-1`. The first time a pair
of energies has angular gap at least π is a genuine possibly infinite
stopping time for that past filtration.
-/
namespace FixedCouplingPoisson

open MeasureTheory Set Matrix

/-- The real canonical lift iterated along the actual potential coordinates. -/
noncomputable def canonicalPhaseProcess (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  orbit (canonicalPhaseLift E) ω θ n

@[simp] theorem canonicalPhaseProcess_zero (E θ : ℝ) (ω : PotentialSpace) :
    canonicalPhaseProcess E θ 0 ω = θ := rfl

@[simp] theorem canonicalPhaseProcess_succ (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    canonicalPhaseProcess E θ (n + 1) ω =
      canonicalPhase E (ω n) (canonicalPhaseProcess E θ n ω) := rfl

/-- Only the first `n` potential coordinates affect the phase at time `n`. -/
theorem canonicalPhaseProcess_eq_of_prefix (E θ : ℝ) (n : ℕ) (ω ω' : PotentialSpace)
    (hprefix : ∀ j < n, ω j = ω' j) :
    canonicalPhaseProcess E θ n ω = canonicalPhaseProcess E θ n ω' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [canonicalPhaseProcess_succ, canonicalPhaseProcess_succ,
      hprefix n (Nat.lt_succ_self n)]
    rw [ih (fun j hj => hprefix j (Nat.lt_trans hj (Nat.lt_succ_self n)))]

/-- The actual phase is measurable with respect to precisely the available past. -/
theorem canonicalPhaseProcess_past_measurable (E θ : ℝ) (n : ℕ) :
    @Measurable PotentialSpace ℝ (pastMeasurableSpace n) inferInstance
      (canonicalPhaseProcess E θ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hsite : @Measurable PotentialSpace ℝ (pastMeasurableSpace (n + 1)) inferInstance
        (fun ω => ω n) := by
      apply Measurable.of_comap_le
      change siteMeasurableSpace n ≤ pastMeasurableSpace (n + 1)
      exact le_iSup_of_le n (le_iSup_of_le (Nat.lt_succ_self n) le_rfl)
    have hprev : @Measurable PotentialSpace ℝ (pastMeasurableSpace (n + 1)) inferInstance
        (canonicalPhaseProcess E θ n) :=
      ih.mono (pastMeasurableSpace_mono (Nat.le_succ n)) le_rfl
    exact (canonicalPhase_measurable_potential_angle E).comp (hsite.prodMk hprev)

theorem canonicalPhaseProcess_adapted (E θ : ℝ) :
    Adapted potentialFiltration (canonicalPhaseProcess E θ) :=
  canonicalPhaseProcess_past_measurable E θ

theorem canonicalPhaseProcess_measurable (E θ : ℝ) (n : ℕ) :
    Measurable (canonicalPhaseProcess E θ n) :=
  (canonicalPhaseProcess_adapted E θ).measurable

theorem canonicalPhaseProcess_stronglyAdapted (E θ : ℝ) :
    StronglyAdapted potentialFiltration (canonicalPhaseProcess E θ) :=
  (canonicalPhaseProcess_adapted E θ).stronglyAdapted

theorem canonicalPhaseProcess_progressive (E θ : ℝ) :
    IsStronglyProgressive potentialFiltration (canonicalPhaseProcess E θ) :=
  (canonicalPhaseProcess_stronglyAdapted E θ).isStronglyProgressive_of_discrete

/-- The actual phase observed at a stopping time is measurable in the stopped past. -/
theorem canonicalPhaseProcess_stopped_measurable (E θ : ℝ)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ) :
    Measurable[hτ.measurableSpace] (stoppedValue (canonicalPhaseProcess E θ) τ) :=
  measurable_stoppedValue (canonicalPhaseProcess_progressive E θ) hτ

/-- Joint measurability of a finite actual evolution and its starting state. -/
theorem canonicalPhaseProcess_measurable_initial_path (E : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ × PotentialSpace => canonicalPhaseProcess E p.1 n p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact (canonicalPhase_measurable_potential_angle E).comp
      (((measurable_pi_apply n).comp measurable_snd).prodMk ih)

/-- Continuous dependence on energy and initial direction for every fixed path. -/
theorem canonicalPhaseProcess_continuous_energy_initial (n : ℕ) (ω : PotentialSpace) :
    Continuous (fun p : ℝ × ℝ => canonicalPhaseProcess p.1 p.2 n ω) := by
  induction n with
  | zero => exact continuous_snd
  | succ n ih =>
    exact (canonicalPhase_continuous_energy_angle (ω n)).comp
      (continuous_fst.prodMk ih)

/-- Exact pathwise restart uses the actual coordinate shift. -/
theorem canonicalPhaseProcess_restart (E θ : ℝ) (t n : ℕ) (ω : PotentialSpace) :
    canonicalPhaseProcess E (canonicalPhaseProcess E θ t ω) n (potentialShift t ω) =
      canonicalPhaseProcess E θ (t + n) ω := by
  exact orbit_restart (canonicalPhaseLift E) ω θ t n

/-- Integer periods in the initial direction are retained along the whole path. -/
theorem canonicalPhaseProcess_add_int (E θ : ℝ) (k : ℤ) (n : ℕ) (ω : PotentialSpace) :
    canonicalPhaseProcess E (θ + k * Real.pi) n ω =
      canonicalPhaseProcess E θ n ω + k * Real.pi :=
  orbit_add_period (canonicalPhaseLift E) ω θ k n

/-- The actual random restart is the same pathwise transfer evolution on the
whole stopped future. Only the paths with infinite stopping time are excluded. -/
theorem canonicalPhaseProcess_stopped_restart (E θ : ℝ) (n : ℕ)
    (τ : PotentialSpace → WithTop ℕ) (ω : PotentialSpace) (hfinite : τ ω ≠ ⊤) :
    canonicalPhaseProcess E (stoppedValue (canonicalPhaseProcess E θ) τ ω) n
        (stoppedPotentialFuture τ ω) =
      canonicalPhaseProcess E θ ((τ ω).untopD 0 + n) ω := by
  cases ht : τ ω with
  | top => exact False.elim (hfinite ht)
  | coe t =>
    simpa only [stoppedValue, stoppedPotentialFuture, ht, WithTop.untopA,
      WithTop.untopD_coe] using canonicalPhaseProcess_restart E θ t n ω

/-- Almost-sure finiteness suffices for the actual stopped restart identity. -/
theorem canonicalPhaseProcess_ae_stopped_restart (law : PotentialLaw) (E θ : ℝ) (n : ℕ)
    (τ : PotentialSpace → WithTop ℕ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) :
    (fun ω => canonicalPhaseProcess E (stoppedValue (canonicalPhaseProcess E θ) τ ω) n
      (stoppedPotentialFuture τ ω)) =ᵐ[iidMeasure law]
      (fun ω => canonicalPhaseProcess E θ ((τ ω).untopD 0 + n) ω) := by
  filter_upwards [hfinite] with ω hω
  exact canonicalPhaseProcess_stopped_restart E θ n τ ω hω

theorem euclideanNorm_angleVector (θ : ℝ) : euclideanNorm (angleVector θ) = 1 := by
  change Real.sqrt (Real.cos θ ^ 2 + Real.sin θ ^ 2) = 1
  rw [add_comm, Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- Every finite actual transfer product has the iterated angle and a positive scale. -/
theorem canonicalPhaseProcess_product_positive_scale (E θ : ℝ) (n : ℕ)
    (ω : PotentialSpace) :
    ∃ r : ℝ, 0 < r ∧ transferProduct E ω n *ᵥ angleVector θ =
      r • angleVector (canonicalPhaseProcess E θ n ω) := by
  induction n with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [transferProduct, Matrix.one_mulVec, canonicalPhaseProcess_zero, one_smul]
  | succ n ih =>
    obtain ⟨r, hr, hrep⟩ := ih
    let s := euclideanNorm (transfer E (ω n) *ᵥ angleVector (canonicalPhaseProcess E θ n ω))
    have hs : 0 < s := euclideanNorm_pos _
      (sl2_mulVec_ne_zero _ (transfer_det E (ω n)) _ (angleVector_ne_zero _))
    refine ⟨r * s, mul_pos hr hs, ?_⟩
    rw [transferProduct, ← Matrix.mulVec_mulVec, hrep, Matrix.mulVec_smul,
      canonicalPhase_actual_vector, smul_smul, canonicalPhaseProcess_succ]

/-- The scale of the actual finite product is its genuine Euclidean norm. -/
theorem canonicalPhaseProcess_actual_vector (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    transferProduct E ω n *ᵥ angleVector θ =
      euclideanNorm (transferProduct E ω n *ᵥ angleVector θ) •
        angleVector (canonicalPhaseProcess E θ n ω) := by
  obtain ⟨r, hr, hrep⟩ := canonicalPhaseProcess_product_positive_scale E θ n ω
  have hnorm : euclideanNorm (transferProduct E ω n *ᵥ angleVector θ) = r := by
    rw [hrep, euclideanNorm_smul, euclideanNorm_angleVector, abs_of_pos hr, mul_one]
  rw [hnorm]
  exact hrep

/-- The actual finite matrix product induces the iterated projective direction. -/
theorem canonicalPhaseProcess_projective (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    Projectivization.mk ℝ (angleVector (canonicalPhaseProcess E θ n ω))
        (angleVector_ne_zero _) =
      Projectivization.mk ℝ (transferProduct E ω n *ᵥ angleVector θ)
        (sl2_mulVec_ne_zero _ (transferProduct_det E ω n) _ (angleVector_ne_zero θ)) := by
  apply (wedge_eq_zero_iff_projective_eq _ _ _ _).mp
  rw [canonicalPhaseProcess_actual_vector, wedge_smul_right, wedge_self, mul_zero]

/-- The two actual energies are driven by the same iid potential sequence. -/
noncomputable def canonicalGapProcess (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  canonicalPhaseProcess E θ n ω - canonicalPhaseProcess (E + δ) φ n ω

theorem canonicalGapProcess_eq_pairGap (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    canonicalGapProcess E δ θ φ n ω =
      pairGap (canonicalPhaseLift E) (canonicalPhaseLift (E + δ)) ω θ φ n := rfl

@[simp] theorem canonicalGapProcess_zero (E δ θ φ : ℝ) (ω : PotentialSpace) :
    canonicalGapProcess E δ θ φ 0 ω = θ - φ := rfl

theorem canonicalGapProcess_adapted (E δ θ φ : ℝ) :
    Adapted potentialFiltration (canonicalGapProcess E δ θ φ) :=
  (canonicalPhaseProcess_adapted E θ).sub (canonicalPhaseProcess_adapted (E + δ) φ)

theorem canonicalGapProcess_measurable (E δ θ φ : ℝ) (n : ℕ) :
    Measurable (canonicalGapProcess E δ θ φ n) :=
  (canonicalGapProcess_adapted E δ θ φ).measurable

theorem canonicalGapProcess_stronglyAdapted (E δ θ φ : ℝ) :
    StronglyAdapted potentialFiltration (canonicalGapProcess E δ θ φ) :=
  (canonicalGapProcess_adapted E δ θ φ).stronglyAdapted

/-- The actual energy gap observed at a stopping time uses only the stopped past. -/
theorem canonicalGapProcess_stopped_measurable (E δ θ φ : ℝ)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ) :
    Measurable[hτ.measurableSpace] (stoppedValue (canonicalGapProcess E δ θ φ) τ) :=
  measurable_stoppedValue
    (canonicalGapProcess_stronglyAdapted E δ θ φ).isStronglyProgressive_of_discrete hτ

/-- The finite two-energy evolution is jointly measurable in its starting
pair of directions and the entire future sample. -/
theorem canonicalGapProcess_measurable_initial_path (E δ : ℝ) (n : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × PotentialSpace =>
      canonicalGapProcess E δ p.1.1 p.1.2 n p.2) := by
  exact ((canonicalPhaseProcess_measurable_initial_path E n).comp
      ((measurable_fst.fst).prodMk measurable_snd)).sub
    ((canonicalPhaseProcess_measurable_initial_path (E + δ) n).comp
      ((measurable_fst.snd).prodMk measurable_snd))

/-- The energy order follows from the proved concrete one-step phase order. -/
theorem canonicalGapProcess_nonneg (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ)
    (n : ℕ) (ω : PotentialSpace) : 0 ≤ canonicalGapProcess E δ θ φ n ω := by
  exact pairGap_nonneg (canonicalPhaseLift E) (canonicalPhaseLift (E + δ)) ω θ φ
    (fun v x => sub_nonneg.mp (canonicalPhase_energy_close E v x δ hδ).1) hinit n

/-- Completed crossings cannot be lost under the actual transfer dynamics. -/
theorem canonicalGapProcess_count_monotone (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (ω : PotentialSpace) :
    Monotone (fun n => Int.floor (canonicalGapProcess E δ θ φ n ω / Real.pi)) := by
  exact pairCount_monotone (canonicalPhaseLift E) (canonicalPhaseLift (E + δ)) ω θ φ
    (fun v x => sub_nonneg.mp (canonicalPhase_energy_close E v x δ hδ).1)

/-- At an actual crossing the excess is bounded by the energy perturbation. -/
theorem canonicalGapProcess_crossing_overshoot (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (m : ℤ) (n : ℕ) (ω : PotentialSpace)
    (hprev : canonicalGapProcess E δ θ φ n ω < m * Real.pi)
    (hcross : m * Real.pi ≤ canonicalGapProcess E δ θ φ (n + 1) ω) :
    m * Real.pi ≤ canonicalGapProcess E δ θ φ (n + 1) ω ∧
      canonicalGapProcess E δ θ φ (n + 1) ω ≤ m * Real.pi + δ := by
  exact pairGap_crossing_overshoot (canonicalPhaseLift E) (canonicalPhaseLift (E + δ))
    ω θ φ δ (fun v x => (canonicalPhase_energy_close E v x δ hδ).2) m n hprev hcross

/-- A completed integer period persists at every later actual time. -/
theorem canonicalGapProcess_period_persists (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (k : ℤ) (j n : ℕ) (ω : PotentialSpace) (hjn : j ≤ n)
    (hj : k * Real.pi ≤ canonicalGapProcess E δ θ φ j ω) :
    k * Real.pi ≤ canonicalGapProcess E δ θ φ n ω := by
  induction n, hjn using Nat.le_induction with
  | base => exact hj
  | succ m _ hm =>
    exact gap_step_lower
      (F := canonicalPhaseLift E (ω m)) (G := canonicalPhaseLift (E + δ) (ω m))
      (fun x => sub_nonneg.mp (canonicalPhase_energy_close E (ω m) x δ hδ).1) k hm

/-- Restarting a phase gap also removes the selected completed integer periods. -/
theorem canonicalGapProcess_restart (E δ θ φ : ℝ) (t n : ℕ) (k : ℤ)
    (ω : PotentialSpace) :
    canonicalGapProcess E δ (canonicalPhaseProcess E θ t ω)
        (canonicalPhaseProcess (E + δ) φ t ω + k * Real.pi) n (potentialShift t ω) =
      canonicalGapProcess E δ θ φ (t + n) ω - k * Real.pi :=
  pairGap_restart (canonicalPhaseLift E) (canonicalPhaseLift (E + δ)) ω θ φ t n k

/-- The first π crossing, with value `⊤` on paths which never cross. -/
noncomputable def canonicalCrossingTime (E δ θ φ : ℝ) : PotentialSpace → WithTop ℕ :=
  hittingAfter (canonicalGapProcess E δ θ φ) (Ici Real.pi) 0

/-- This uses the actual iid past, rather than an assumed stopping-time property. -/
theorem canonicalCrossingTime_isStoppingTime (E δ θ φ : ℝ) :
    IsStoppingTime potentialFiltration (canonicalCrossingTime E δ θ φ) :=
  (canonicalGapProcess_adapted E δ θ φ).isStoppingTime_hittingAfter measurableSet_Ici

theorem canonicalCrossingTime_le_iff (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    canonicalCrossingTime E δ θ φ ω ≤ n ↔
      ∃ j ≤ n, Real.pi ≤ canonicalGapProcess E δ θ φ j ω := by
  exact hittingAfter_bot_le_iff

/-- Energy ordering makes the first-crossing event equal to the current crossing event. -/
theorem canonicalCrossingTime_le_iff_gap (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (n : ℕ) (ω : PotentialSpace) :
    canonicalCrossingTime E δ θ φ ω ≤ n ↔
      Real.pi ≤ canonicalGapProcess E δ θ φ n ω := by
  rw [canonicalCrossingTime_le_iff]
  constructor
  · rintro ⟨j, hjn, hj⟩
    have h := canonicalGapProcess_period_persists E δ θ φ hδ (1 : ℤ) j n ω hjn
    simpa only [Int.cast_one, one_mul] using h (by simpa only [Int.cast_one, one_mul] using hj)
  · intro hn
    exact ⟨n, le_rfl, hn⟩

theorem canonicalCrossingTime_eq_top_iff (E δ θ φ : ℝ) (ω : PotentialSpace) :
    canonicalCrossingTime E δ θ φ ω = ⊤ ↔
      ∀ n, canonicalGapProcess E δ θ φ n ω < Real.pi := by
  simp only [canonicalCrossingTime, hittingAfter_eq_top_iff, zero_le, true_implies,
    mem_Ici, not_le]

theorem canonicalCrossingTime_before (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω) :
    canonicalGapProcess E δ θ φ n ω < Real.pi := by
  exact lt_of_not_ge (notMem_of_lt_hittingAfter hn (Nat.zero_le n))

/-- A finite first crossing really reaches π at its declared time. -/
theorem canonicalCrossingTime_hits (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace)
    (hn : canonicalCrossingTime E δ θ φ ω = n) :
    Real.pi ≤ canonicalGapProcess E δ θ φ n ω := by
  obtain ⟨j, hjn, hj⟩ := (canonicalCrossingTime_le_iff E δ θ φ n ω).mp hn.le
  by_cases hjeq : j = n
  · simpa only [hjeq] using hj
  · have hjlt : j < n := lt_of_le_of_ne hjn hjeq
    have hjbefore : (j : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω := by
      rw [hn]
      exact_mod_cast hjlt
    exact False.elim (not_le_of_gt (canonicalCrossingTime_before E δ θ φ j ω hjbefore) hj)

/-- The finite first crossing has the actual deterministic one-step overshoot bound. -/
theorem canonicalCrossingTime_overshoot (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (n : ℕ) (ω : PotentialSpace)
    (hn : canonicalCrossingTime E δ θ φ ω = ((n + 1 : ℕ) : WithTop ℕ)) :
    Real.pi ≤ canonicalGapProcess E δ θ φ (n + 1) ω ∧
      canonicalGapProcess E δ θ φ (n + 1) ω ≤ Real.pi + δ := by
  have hbefore : (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω := by
    rw [hn]
    exact_mod_cast Nat.lt_succ_self n
  have hprev := canonicalCrossingTime_before E δ θ φ n ω hbefore
  have hcross := canonicalCrossingTime_hits E δ θ φ (n + 1) ω hn
  simpa only [Int.cast_one, one_mul] using
    canonicalGapProcess_crossing_overshoot E δ θ φ hδ (1 : ℤ) n ω
      (by simpa only [Int.cast_one, one_mul] using hprev)
      (by simpa only [Int.cast_one, one_mul] using hcross)

/-- The possibly infinite first crossing is an ordinary measurable random variable. -/
theorem canonicalCrossingTime_measurable (E δ θ φ : ℝ) :
    Measurable (canonicalCrossingTime E δ θ φ) := by
  apply measurable_of_Iic
  intro n
  induction n using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    exact pastMeasurableSpace_le n _
      ((canonicalCrossingTime_isStoppingTime E δ θ φ).measurableSet_le n)

/-- The crossing time determines measurable finite-time events in the actual past. -/
theorem canonicalCrossingTime_fiber_measurable (E δ θ φ : ℝ) (n : ℕ) :
    MeasurableSet[pastMeasurableSpace n]
      {ω | canonicalCrossingTime E δ θ φ ω = n} :=
  (canonicalCrossingTime_isStoppingTime E δ θ φ).measurableSet_eq n

end FixedCouplingPoisson
