import FixedCouplingPoisson.SelectiveBlockCounts
import FixedCouplingPoisson.BernoulliConstantWindows
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! Selectively cut good constant slots in the actual iid model, integrate
their exact probabilities, and pass the positive density to the canonical
IDS. The single-site atom hypothesis is verified for both Bernoulli atoms
below; no positivity of a spectral count is assumed as a model input. -/
noncomputable section
namespace FixedCouplingPoisson
open Filter MeasureTheory Set Furstenberg
open scoped Topology

def constantBlockEvent (k L : ℕ) (c : ℝ) : Set PotentialSpace :=
  {ω | potentialBlock k L ω = fun _ => c}

theorem measurableSet_constantBlockEvent (k L : ℕ) (c : ℝ) :
    MeasurableSet (constantBlockEvent k L c) :=
  (measurable_potentialBlock k L) (measurableSet_singleton _)

def constantBlockIndicator (k L : ℕ) (c : ℝ) (ω : PotentialSpace) : ℝ :=
  (constantBlockEvent k L c).indicator (fun _ => 1) ω

theorem integrable_constantBlockIndicator (law : PotentialLaw) (k L : ℕ) (c : ℝ) :
    Integrable (constantBlockIndicator k L c) (iidMeasure law) :=
  (integrable_const 1).indicator (measurableSet_constantBlockEvent k L c)

theorem iidMeasure_constantBlockEvent (law : PotentialLaw) (k L : ℕ) (c : ℝ) :
    iidMeasure law (constantBlockEvent k L c) = (law.measure {c}) ^ L := by
  have hm := Measure.map_apply (μ := iidMeasure law) (measurable_potentialBlock k L)
    (measurableSet_singleton (fun _ : Fin L => c))
  rw [iidMeasure_block_map law k L] at hm
  change (iidMeasure law) (potentialBlock k L ⁻¹' {fun _ : Fin L => c}) = _
  rw [← hm]
  simp [finitePotentialMeasure, Measure.pi_singleton]

theorem integral_constantBlockIndicator (law : PotentialLaw) (k L : ℕ) (c : ℝ) :
    (∫ ω, constantBlockIndicator k L c ω ∂iidMeasure law) = (law.measure.real {c}) ^ L := by
  unfold constantBlockIndicator
  rw [integral_indicator_const 1 (measurableSet_constantBlockEvent k L c)]
  simp only [smul_eq_mul, mul_one, measureReal_def, iidMeasure_constantBlockEvent,
    ENNReal.toReal_pow]

/-- The actual number of good slots, as a finite sum of their indicators. -/
def constantSlotCount (q L : ℕ) (c : ℝ) (ω : PotentialSpace) : ℝ :=
  ∑ b ∈ Finset.range q, constantBlockIndicator (b * L) L c ω

theorem constantSlotCount_eq_card (q L : ℕ) (c : ℝ) (ω : PotentialSpace) :
    constantSlotCount q L c ω =
      ((Finset.range q).filter (fun b => potentialBlock (b * L) L ω = fun _ => c)).card := by
  classical
  simp [constantSlotCount, constantBlockIndicator, constantBlockEvent, Set.indicator_apply]

theorem constantSlotCount_windowCount_lower (E F : ℝ) (hEF : E ≤ F) (c : ℝ) (L : ℕ)
    (hconstant : 9 ≤ (nonstrictSpectralCount L (fun _ => c) F : ℝ) -
      (nonstrictSpectralCount L (fun _ => c) E : ℝ)) (q : ℕ) (ω : PotentialSpace) :
    constantSlotCount q L c ω ≤ iidWindowCount 0 (q * L) ω E F := by
  classical
  let s := (Finset.range q).filter (fun b => potentialBlock (b * L) L ω = fun _ => c)
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hmem (i : Fin s.card) : f i ∈ s := s.orderEmbOfFin_mem rfl i
  have hrange (i : Fin s.card) : f i < q :=
    Finset.mem_range.mp (Finset.mem_filter.mp (hmem i)).1
  rw [constantSlotCount_eq_card]
  apply selectedConstantBlocks_windowCount_lower E F hEF c L hconstant s.card 0 (q * L) ω
    (fun i => f i * L)
  · intro i; exact Nat.zero_le _
  · intro i
    simpa only [zero_add, Nat.succ_mul] using
      Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr (hrange i))
  · intro i j hij
    have hfij : f i < f j := f.strictMono hij
    simpa only [Nat.succ_mul] using
      Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr hfij)
  · intro i
    exact (Finset.mem_filter.mp (hmem i)).2

theorem integrable_constantSlotCount (law : PotentialLaw) (q L : ℕ) (c : ℝ) :
    Integrable (constantSlotCount q L c) (iidMeasure law) := by
  unfold constantSlotCount
  exact integrable_finsetSum _ (fun b _ => integrable_constantBlockIndicator law (b * L) L c)

theorem integral_constantSlotCount (law : PotentialLaw) (q L : ℕ) (c : ℝ) :
    (∫ ω, constantSlotCount q L c ω ∂iidMeasure law) = (q : ℝ) * (law.measure.real {c}) ^ L := by
  unfold constantSlotCount
  rw [integral_finsetSum _ (fun b _ => integrable_constantBlockIndicator law (b * L) L c)]
  simp [integral_constantBlockIndicator]

theorem integrable_iidWindowCount (law : PotentialLaw) (k n : ℕ) (E F : ℝ) :
    Integrable (fun ω => iidWindowCount k n ω E F) (iidMeasure law) :=
  (iidBlock_count_integrable law k n F).sub (iidBlock_count_integrable law k n E)

theorem integral_iidWindowCount (law : PotentialLaw) (k n : ℕ) (E F : ℝ) :
    (∫ ω, iidWindowCount k n ω E F ∂iidMeasure law) =
      meanSpectralCount law n F - meanSpectralCount law n E := by
  unfold iidWindowCount
  rw [integral_sub (iidBlock_count_integrable law k n F) (iidBlock_count_integrable law k n E),
    iidBlock_count_integral, iidBlock_count_integral]

theorem meanWindowCount_constantSlot_lower (law : PotentialLaw) (E F : ℝ) (hEF : E ≤ F)
    (c : ℝ) (L : ℕ)
    (hconstant : 9 ≤ (nonstrictSpectralCount L (fun _ => c) F : ℝ) -
      (nonstrictSpectralCount L (fun _ => c) E : ℝ)) (q : ℕ) :
    (q : ℝ) * (law.measure.real {c}) ^ L ≤
      meanSpectralCount law (q * L) F - meanSpectralCount law (q * L) E := by
  have hi := integral_mono (integrable_constantSlotCount law q L c)
    (integrable_iidWindowCount law 0 (q * L) E F)
    (constantSlotCount_windowCount_lower E F hEF c L hconstant q)
  rw [integral_constantSlotCount, integral_iidWindowCount] at hi
  exact hi

/-- The selectively isolated good blocks give the explicit positive-density
lower bound, without independence between the slot indicators. -/
theorem idsCandidate_increment_ge_constantBlock (law : PotentialLaw) (E F : ℝ)
    (hEF : E ≤ F) (c : ℝ) (L : ℕ) (hL : 0 < L)
    (hconstant : 9 ≤ (nonstrictSpectralCount L (fun _ => c) F : ℝ) -
      (nonstrictSpectralCount L (fun _ => c) E : ℝ)) :
    (law.measure.real {c}) ^ L / (L : ℝ) ≤ idsCandidate law F - idsCandidate law E := by
  have hlim := ((hasIDS_idsCandidate law F).sub (hasIDS_idsCandidate law E)).comp
    (tendsto_id.atTop_mul_const' hL)
  have hbound : ∀ᶠ q : ℕ in atTop,
      (law.measure.real {c}) ^ L / (L : ℝ) ≤
        normalizedMeanCount law F (q * L) - normalizedMeanCount law E (q * L) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
    have hh := meanWindowCount_constantSlot_lower law E F hEF c L hconstant q
    rw [normalizedMeanCount, normalizedMeanCount, ← sub_div, Nat.cast_mul]
    apply (le_div_iff₀ (mul_pos hqpos hLpos)).mpr
    calc
      (law.measure.real {c}) ^ L / (L : ℝ) * ((q : ℝ) * (L : ℝ)) =
          (q : ℝ) * (law.measure.real {c}) ^ L := by
        field_simp [ne_of_gt hLpos]
        <;> ring
      _ ≤ _ := hh
  exact ge_of_tendsto hlim hbound

/-- A positive atom gives a positive IDS increment in every interval meeting
its open constant-potential band. -/
theorem idsCandidate_increment_pos_of_atom (law : PotentialLaw) (c E F z : ℝ)
    (hmass : 0 < law.measure.real {c}) (hzband : z ∈ Ioo (c - 2) (c + 2))
    (hzwindow : z ∈ Ioo E F) : 0 < idsCandidate law F - idsCandidate law E := by
  have hEF : E ≤ F := le_of_lt (hzwindow.1.trans hzwindow.2)
  obtain ⟨L, hL, hwindow⟩ := constantChain_exists_windowCount_ge c E F z hzband hzwindow 9
  have hconstant : 9 ≤ (nonstrictSpectralCount L (fun _ => c) F : ℝ) -
      (nonstrictSpectralCount L (fun _ => c) E : ℝ) := by
    have he := dirichletEnergyWindowCount_eq_nonstrict_difference L (fun _ => c) E F hEF
    have hw : (9 : ℤ) ≤ dirichletEnergyWindowCount L (fun _ => c) E F := by exact_mod_cast hwindow
    rw [he] at hw
    exact_mod_cast hw
  have hpositive : 0 < (law.measure.real {c}) ^ L / (L : ℝ) :=
    div_pos (pow_pos hmass L) (Nat.cast_pos.mpr hL)
  exact hpositive.trans_le
    (idsCandidate_increment_ge_constantBlock law E F hEF c L hL hconstant)

end FixedCouplingPoisson
