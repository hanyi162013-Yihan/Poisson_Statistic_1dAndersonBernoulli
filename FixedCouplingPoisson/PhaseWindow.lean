import FixedCouplingPoisson.Rounding
import FixedCouplingPoisson.ProjectiveMetric
import FixedCouplingPoisson.Sturm
import Mathlib.MeasureTheory.Function.Floor

/-!
# Actual finite spectral windows, winding integers, and residual arcs

Every quantity is calculated from the actual canonical shooting phase. The
finite Dirichlet window count is exactly the ceiling difference. A terminal
rounding discrepancy locates an exact phase anchor near the Dirichlet cut,
unless some adjacent oriented residual is large.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology BigOperators

/-- The integer winding of an actual adjacent lifted-phase gap. -/
def terminalWindowWinding (θ : ℕ → ℝ) (i : ℕ) : ℤ :=
  ⌊(θ i - θ (i + 1)) / Real.pi⌋

/-- Its actual oriented remainder in `[0,π)`. -/
def terminalWindowResidual (θ : ℕ → ℝ) (i : ℕ) : ℝ :=
  θ i - θ (i + 1) - Real.pi * (terminalWindowWinding θ i : ℝ)

/-- The exact ceiling count between the two terminal phases. -/
def terminalWindowCount (θ : ℕ → ℝ) (cut : ℝ) (i : ℕ) : ℤ :=
  ⌈(θ i - cut) / Real.pi⌉ - ⌈(θ (i + 1) - cut) / Real.pi⌉

/-- The actual cardinality of a half-open energy window in the finite Dirichlet spectrum. -/
def dirichletEnergyWindowCount (n : ℕ) (v : Fin n → ℝ) (E E' : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j =>
    E < dirichletEigenvalues n v j ∧ dirichletEigenvalues n v j ≤ E')).card

theorem dirichletEnergyWindowCount_eq_nonstrict_difference (n : ℕ) (v : Fin n → ℝ)
    (E E' : ℝ) (horder : E ≤ E') :
    (dirichletEnergyWindowCount n v E E' : ℤ) =
      (nonstrictSpectralCount n v E' : ℤ) - (nonstrictSpectralCount n v E : ℤ) := by
  classical
  let a := Finset.univ.filter (fun j => dirichletEigenvalues n v j ≤ E)
  let b := Finset.univ.filter (fun j => dirichletEigenvalues n v j ≤ E')
  have hsub : a ⊆ b := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((Finset.mem_filter.mp hj).2).trans horder⟩
  have hdiff : b \ a = Finset.univ.filter (fun j =>
      E < dirichletEigenvalues n v j ∧ dirichletEigenvalues n v j ≤ E') := by
    ext j
    simp only [a, b, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact and_comm
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [hdiff] at hcard
  have hcount : dirichletEnergyWindowCount n v E E' + nonstrictSpectralCount n v E =
      nonstrictSpectralCount n v E' := hcard
  omega

/-- Actual nonstrict spectral counts give the terminal ceiling count exactly. -/
theorem nonstrictSpectralWindow_eq_phase_ceil (w : ℕ → ℝ) (n : ℕ) (E E' : ℝ) :
    (nonstrictSpectralCount n (fun j => w j.val) E' : ℤ) -
      (nonstrictSpectralCount n (fun j => w j.val) E : ℤ) =
      ⌈(shootingPhase E w n - Real.pi / 2) / Real.pi⌉ -
        ⌈(shootingPhase E' w n - Real.pi / 2) / Real.pi⌉ := by
  have hscaled (x : ℝ) : (x - Real.pi / 2) / Real.pi = x / Real.pi - 1 / 2 := by
    field_simp [Real.pi_ne_zero]
  rw [hscaled, hscaled]
  have hreal : (nonstrictSpectralCount n (fun j => w j.val) E' : ℝ) -
      (nonstrictSpectralCount n (fun j => w j.val) E : ℝ) =
      (⌈shootingPhase E w n / Real.pi - 1 / 2⌉ : ℝ) -
        (⌈shootingPhase E' w n / Real.pi - 1 / 2⌉ : ℝ) := by
    rw [nonstrictSpectralCount_shooting_real, nonstrictSpectralCount_shooting_real]
    ring
  exact_mod_cast hreal

theorem terminalWindowResidual_mem (θ : ℕ → ℝ) (i : ℕ) :
    terminalWindowResidual θ i ∈ Set.Ico 0 Real.pi := by
  have hlo := Int.floor_le ((θ i - θ (i + 1)) / Real.pi)
  have hhi := Int.lt_floor_add_one ((θ i - θ (i + 1)) / Real.pi)
  have hmul : ((θ i - θ (i + 1)) / Real.pi) * Real.pi = θ i - θ (i + 1) :=
    div_mul_cancel₀ _ Real.pi_ne_zero
  have hlo' := mul_le_mul_of_nonneg_right hlo Real.pi_pos.le
  have hhi' := mul_lt_mul_of_pos_right hhi Real.pi_pos
  unfold terminalWindowResidual terminalWindowWinding
  constructor <;> nlinarith

theorem terminalWindow_decomposition (θ : ℕ → ℝ) (i : ℕ) :
    θ i = θ (i + 1) + Real.pi * (terminalWindowWinding θ i : ℝ) +
      terminalWindowResidual θ i := by
  unfold terminalWindowResidual
  ring

theorem terminalWindowCount_winding_error (θ : ℕ → ℝ) (cut : ℝ) (i : ℕ) :
    terminalWindowCount θ cut i - terminalWindowWinding θ i =
      ⌈(θ (i + 1) - cut) / Real.pi + terminalWindowResidual θ i / Real.pi⌉ -
        ⌈(θ (i + 1) - cut) / Real.pi⌉ := by
  unfold terminalWindowCount
  rw [terminalWindow_decomposition θ i]
  exact ceil_angular_winding_residual _ _ _ _ Real.pi_ne_zero

theorem terminalWindowCount_error_zero_or_one (θ : ℕ → ℝ) (cut : ℝ) (i : ℕ) :
    terminalWindowCount θ cut i - terminalWindowWinding θ i = 0 ∨
      terminalWindowCount θ cut i - terminalWindowWinding θ i = 1 := by
  rw [terminalWindowCount_winding_error]
  exact ceil_residual_zero_or_one _ _
    (div_nonneg (terminalWindowResidual_mem θ i).1 Real.pi_pos.le)
    ((div_le_one Real.pi_pos).mpr (terminalWindowResidual_mem θ i).2.le)

/-- Every nonzero exact rounding discrepancy locates the cut within the residual arc. -/
theorem ceil_residual_cut_distance (θ cut r : ℝ) (hr0 : 0 ≤ r) (hrπ : r ≤ Real.pi)
    (herr : ⌈(θ - cut) / Real.pi + r / Real.pi⌉ - ⌈(θ - cut) / Real.pi⌉ ≠ 0) :
    projectiveDistance (phaseProjective θ) (phaseProjective cut) ≤ r := by
  have hr1 := (div_le_one Real.pi_pos).mpr hrπ
  have hrnonneg := div_nonneg hr0 Real.pi_pos.le
  have hone : ⌈(θ - cut) / Real.pi + r / Real.pi⌉ - ⌈(θ - cut) / Real.pi⌉ = 1 := by
    rcases ceil_residual_zero_or_one _ _ hrnonneg hr1 with hzero | hone
    · exact (herr hzero).elim
    · exact hone
  obtain ⟨z, hz0, hz1⟩ := (ceil_residual_eq_one_iff_cut _ _ hrnonneg hr1).mp hone
  have hz0' := (div_le_iff₀ Real.pi_pos).mp hz0
  have hz1' : (z : ℝ) * Real.pi < θ - cut + r := by
    apply (lt_div_iff₀ Real.pi_pos).mp
    simpa only [← add_div] using hz1
  have habs : |cut + (z : ℝ) * Real.pi - θ| ≤ r := by
    rw [abs_le]
    constructor <;> linarith
  rw [← phaseProjective_add_int cut z, projectiveDistance_phaseProjective]
  exact (Real.abs_sin_le_abs (x := cut + (z : ℝ) * Real.pi - θ)).trans habs

theorem terminalWindowCount_error_cut_distance (θ : ℕ → ℝ) (cut : ℝ) (i : ℕ)
    (herr : terminalWindowCount θ cut i ≠ terminalWindowWinding θ i) :
    projectiveDistance (phaseProjective (θ (i + 1))) (phaseProjective cut) ≤
      terminalWindowResidual θ i := by
  apply ceil_residual_cut_distance _ _ _ (terminalWindowResidual_mem θ i).1
    (terminalWindowResidual_mem θ i).2.le
  rw [← terminalWindowCount_winding_error]
  exact sub_ne_zero.mpr herr

theorem projectiveDistance_symmetry (p q : ProjectivePoint) :
    projectiveDistance p q = projectiveDistance q p := by
  obtain ⟨θ, rfl⟩ := phaseProjective_surjective p
  obtain ⟨φ, rfl⟩ := phaseProjective_surjective q
  rw [projectiveDistance_phaseProjective, projectiveDistance_phaseProjective]
  rw [show θ - φ = -(φ - θ) by ring, Real.sin_neg, abs_neg]

/-- Integer winding has no effect on the distance between adjacent directions. -/
theorem terminalWindow_step_distance (θ : ℕ → ℝ) (i : ℕ) :
    projectiveDistance (phaseProjective (θ i)) (phaseProjective (θ (i + 1))) ≤
      terminalWindowResidual θ i := by
  let r := terminalWindowResidual θ i
  let k := terminalWindowWinding θ i
  have hp : phaseProjective (θ i) = phaseProjective (θ (i + 1) + r) := by
    have hθ : θ i = (θ (i + 1) + r) + (k : ℝ) * Real.pi := by
      dsimp only [r, k]
      unfold terminalWindowResidual
      ring
    rw [hθ, phaseProjective_add_int]
  rw [hp, projectiveDistance_phaseProjective]
  have heq : θ (i + 1) - (θ (i + 1) + r) = -r := by ring
  rw [heq, Real.sin_neg, abs_neg]
  exact (Real.abs_sin_le_abs (x := r)).trans
    (by rw [abs_of_nonneg (terminalWindowResidual_mem θ i).1])

theorem projectiveDistance_chain_from_zero (p : ℕ → ProjectivePoint) (s : ℕ)
    (h : ℝ) (hstep : ∀ i < s, projectiveDistance (p i) (p (i + 1)) ≤ h) :
    ∀ i ≤ s, projectiveDistance (p 0) (p i) ≤ (i : ℝ) * h := by
  intro i hi
  induction i with
  | zero =>
    rw [(projectiveDistance_eq_zero_iff _ _).mpr rfl]
    simp
  | succ i ih =>
    calc
      _ ≤ projectiveDistance (p 0) (p i) + projectiveDistance (p i) (p (i + 1)) :=
        projectiveDistance_triangle (p 0) (p i) (p (i + 1))
      _ ≤ (i : ℝ) * h + h := add_le_add (ih (by omega)) (hstep i (by omega))
      _ = ((i + 1 : ℕ) : ℝ) * h := by push_cast; ring

/-- A finite-window error forces the exact anchor into a small cut neighborhood.
The harmless constant `2s+1` avoids any choice of orientation of the anchor index. -/
theorem terminalWindow_error_anchor_distance (θ : ℕ → ℝ) (cut : ℝ) (s κ : ℕ)
    (hκ : κ ≤ s) (h : ℝ) (hh : 0 ≤ h)
    (hres : ∀ i < s, terminalWindowResidual θ i ≤ h)
    (i : ℕ) (hi : i < s)
    (herr : terminalWindowCount θ cut i ≠ terminalWindowWinding θ i) :
    projectiveDistance (phaseProjective (θ κ)) (phaseProjective cut) ≤
      (2 * (s : ℝ) + 1) * h := by
  let p := fun j => phaseProjective (θ j)
  have hstep : ∀ j < s, projectiveDistance (p j) (p (j + 1)) ≤ h :=
    fun j hj => (terminalWindow_step_distance θ j).trans (hres j hj)
  have hκ0 := projectiveDistance_chain_from_zero p s h hstep κ hκ
  have hi0 := projectiveDistance_chain_from_zero p s h hstep (i + 1) (by omega)
  have hκreal : (κ : ℝ) ≤ s := by exact_mod_cast hκ
  have hireal : ((i + 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast (show i + 1 ≤ s by omega)
  have hcut := (terminalWindowCount_error_cut_distance θ cut i herr).trans (hres i hi)
  calc
    _ ≤ projectiveDistance (p κ) (p 0) + projectiveDistance (p 0) (phaseProjective cut) :=
      projectiveDistance_triangle (p κ) (p 0) (phaseProjective cut)
    _ ≤ projectiveDistance (p κ) (p 0) +
        (projectiveDistance (p 0) (p (i + 1)) +
          projectiveDistance (p (i + 1)) (phaseProjective cut)) :=
      add_le_add le_rfl (projectiveDistance_triangle (p 0) (p (i + 1))
        (phaseProjective cut))
    _ ≤ (κ : ℝ) * h + (((i + 1 : ℕ) : ℝ) * h + h) := by
      rw [projectiveDistance_symmetry (p κ) (p 0)]
      exact add_le_add hκ0 (add_le_add hi0 hcut)
    _ ≤ (2 * (s : ℝ) + 1) * h := by
      nlinarith [mul_le_mul_of_nonneg_right hκreal hh, mul_le_mul_of_nonneg_right hireal hh]

/-- Real shooting phases at a deterministic endpoint array. -/
def actualEndpointPhase (e : ℕ → ℕ → ℝ) (n : ℕ) (ω : PotentialSpace) : ℕ → ℝ :=
  fun i => shootingPhase (e n i) ω n

def actualWindowWinding (e : ℕ → ℕ → ℝ) (n i : ℕ) (ω : PotentialSpace) : ℤ :=
  terminalWindowWinding (actualEndpointPhase e n ω) i

def actualWindowResidual (e : ℕ → ℕ → ℝ) (n i : ℕ) (ω : PotentialSpace) : ℝ :=
  terminalWindowResidual (actualEndpointPhase e n ω) i

/-- The difference of actual finite Dirichlet nonstrict spectral counts. -/
def actualWindowSpectralCount (e : ℕ → ℕ → ℝ) (n i : ℕ) (ω : PotentialSpace) : ℤ :=
  (nonstrictSpectralCount n (fun j => ω j.val) (e n (i + 1)) : ℤ) -
    (nonstrictSpectralCount n (fun j => ω j.val) (e n i) : ℤ)

theorem actualEndpointPhase_gap (e : ℕ → ℕ → ℝ) (n i : ℕ) (ω : PotentialSpace) :
    actualEndpointPhase e n ω i - actualEndpointPhase e n ω (i + 1) =
      canonicalGapProcess (e n i) (e n (i + 1) - e n i) 0 0 n ω := by
  unfold actualEndpointPhase canonicalGapProcess
  rw [shootingPhase_eq_process, shootingPhase_eq_process]
  rw [show e n i + (e n (i + 1) - e n i) = e n (i + 1) by ring]

theorem actualWindowWinding_eq_canonicalGap_floor (e : ℕ → ℕ → ℝ)
    (n i : ℕ) (ω : PotentialSpace) :
    actualWindowWinding e n i ω =
      ⌊canonicalGapProcess (e n i) (e n (i + 1) - e n i) 0 0 n ω / Real.pi⌋ := by
  change ⌊(actualEndpointPhase e n ω i - actualEndpointPhase e n ω (i + 1)) / Real.pi⌋ = _
  rw [actualEndpointPhase_gap]

theorem actualWindowResidual_eq_canonicalGap_residual (e : ℕ → ℕ → ℝ)
    (n i : ℕ) (ω : PotentialSpace) :
    actualWindowResidual e n i ω =
      canonicalGapProcess (e n i) (e n (i + 1) - e n i) 0 0 n ω - Real.pi *
        (⌊canonicalGapProcess (e n i) (e n (i + 1) - e n i) 0 0 n ω / Real.pi⌋ : ℝ) := by
  change (actualEndpointPhase e n ω i - actualEndpointPhase e n ω (i + 1)) -
    Real.pi * (actualWindowWinding e n i ω : ℝ) = _
  rw [actualEndpointPhase_gap, actualWindowWinding_eq_canonicalGap_floor]

theorem actualWindowSpectralCount_eq_card (e : ℕ → ℕ → ℝ) (n i : ℕ)
    (ω : PotentialSpace) (horder : e n i ≤ e n (i + 1)) :
    actualWindowSpectralCount e n i ω =
      (dirichletEnergyWindowCount n (fun j => ω j.val) (e n i) (e n (i + 1)) : ℤ) :=
  (dirichletEnergyWindowCount_eq_nonstrict_difference n (fun j => ω j.val)
    (e n i) (e n (i + 1)) horder).symm

theorem actualWindowSpectralCount_eq_terminal (e : ℕ → ℕ → ℝ) (n i : ℕ)
    (ω : PotentialSpace) :
    actualWindowSpectralCount e n i ω =
      terminalWindowCount (actualEndpointPhase e n ω) (Real.pi / 2) i :=
  nonstrictSpectralWindow_eq_phase_ceil ω n (e n i) (e n (i + 1))

theorem measurable_actualEndpointPhase (e : ℕ → ℕ → ℝ) (n i : ℕ) :
    Measurable (fun ω => actualEndpointPhase e n ω i) := by
  change Measurable (fun ω => shootingPhase (e n i) ω n)
  simp_rw [shootingPhase_eq_process]
  exact canonicalPhaseProcess_measurable (e n i) 0 n

theorem measurable_actualWindowWinding (e : ℕ → ℕ → ℝ) (n i : ℕ) :
    Measurable (actualWindowWinding e n i) :=
  (((measurable_actualEndpointPhase e n i).sub
    (measurable_actualEndpointPhase e n (i + 1))).div_const Real.pi).floor

theorem measurable_actualWindowResidual (e : ℕ → ℕ → ℝ) (n i : ℕ) :
    Measurable (actualWindowResidual e n i) := by
  have hk : Measurable (fun ω => (actualWindowWinding e n i ω : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      (measurable_actualWindowWinding e n i)
  exact ((measurable_actualEndpointPhase e n i).sub
    (measurable_actualEndpointPhase e n (i + 1))).sub (hk.const_mul Real.pi)

theorem measurable_actualWindowSpectralCount (e : ℕ → ℕ → ℝ) (n i : ℕ) :
    Measurable (actualWindowSpectralCount e n i) := by
  have hleft := (((measurable_actualEndpointPhase e n i).sub_const (Real.pi / 2)).div_const
    Real.pi).ceil
  have hright := (((measurable_actualEndpointPhase e n (i + 1)).sub_const (Real.pi / 2)).div_const
    Real.pi).ceil
  convert hleft.sub hright using 1
  ext ω
  exact actualWindowSpectralCount_eq_terminal e n i ω

theorem measurableSet_actualWindow_rounding_success (e : ℕ → ℕ → ℝ) (n s : ℕ) :
    MeasurableSet {ω | ∀ i, i < s →
      actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < s) =>
    measurableSet_eq_fun (measurable_actualWindowSpectralCount e n i)
      (measurable_actualWindowWinding e n i)

/-- Individual actual residual convergence implies convergence of the finite maximum. -/
theorem actualWindow_residual_union_tendsto_zero (law : PotentialLaw)
    (e : ℕ → ℕ → ℝ) (s : ℕ)
    (hres : ∀ i < s, ∀ h : ℝ, 0 < h → Tendsto
      (fun n => iidMeasure law {ω | h < actualWindowResidual e n i ω}) atTop (𝓝 0))
    (h : ℝ) (hh : 0 < h) :
    Tendsto (fun n => iidMeasure law
      {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω}) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ i : Fin s,
      iidMeasure law {ω | h < actualWindowResidual e n i ω}) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset (Fin s)) (fun (i : Fin s) _ => hres i i.isLt h hh)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro n
  change iidMeasure law {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω} ≤
    ∑ i : Fin s, iidMeasure law {ω | h < actualWindowResidual e n i ω}
  have heq : {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω} =
      ⋃ i : Fin s, {ω | h < actualWindowResidual e n i ω} := by
    ext ω
    constructor
    · rintro ⟨i, hi, hω⟩
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hω⟩
    · intro hω
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
      exact ⟨i, i.isLt, hi⟩
  rw [heq]
  exact measure_iUnion_fintype_le _ _

end FixedCouplingPoisson.Furstenberg
