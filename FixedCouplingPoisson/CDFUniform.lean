import FixedCouplingPoisson.CDFWeak
import FixedCouplingPoisson.InverseEnergyContinuity
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Joint CDF continuity is glued across the angular
cut in a continuous-function space. Currying back to the compact circle
then gives the actual uniform norm continuity of lift displacements. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable (ν : ℝ → ProbabilityMeasure ProjectivePoint) (hweak : Continuous ν)
  (hν : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)

def preDisplacementFamily (θ : ℝ) : C(ℝ, ℝ) where
  toFun E := Real.pi * projectiveCDF (ν E) θ - θ
  continuous_toFun :=
    (continuous_const.mul ((continuous_projectiveCDF_family ν hweak hν).comp
      (continuous_id.prodMk continuous_const))).sub continuous_const

theorem continuous_preDisplacementFamily : Continuous (preDisplacementFamily ν hweak hν) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_const.mul
    ((continuous_projectiveCDF_family ν hweak hν).comp continuous_swap)).sub continuous_fst

theorem preDisplacementFamily_endpoints :
    preDisplacementFamily ν hweak hν 0 = preDisplacementFamily ν hweak hν Real.pi := by
  ext E
  simp only [preDisplacementFamily, ContinuousMap.coe_mk, projectiveCDF_zero (ν E) (hν E),
    projectiveCDF_pi, mul_zero, sub_zero, mul_one, sub_self]

def circleDisplacementFamily : AddCircle Real.pi → C(ℝ, ℝ) :=
  AddCircle.liftIco Real.pi 0 (preDisplacementFamily ν hweak hν)

theorem continuous_circleDisplacementFamily : Continuous (circleDisplacementFamily ν hweak hν) :=
  AddCircle.liftIco_zero_continuous (preDisplacementFamily_endpoints ν hweak hν)
    (continuous_preDisplacementFamily ν hweak hν).continuousOn

theorem circleDisplacementFamily_apply (q : AddCircle Real.pi) (E : ℝ) :
    circleDisplacementFamily ν hweak hν q E = cdfDisplacement (ν E) q := rfl

include hweak hν in
theorem continuous_cdfDisplacement_family_joint :
    Continuous (fun z : ℝ × AddCircle Real.pi => cdfDisplacement (ν z.1) z.2) := by
  let G : C(AddCircle Real.pi, C(ℝ, ℝ)) :=
    ⟨circleDisplacementFamily ν hweak hν, continuous_circleDisplacementFamily ν hweak hν⟩
  have h := (ContinuousMap.continuous_uncurry_of_continuous G).comp continuous_swap
  simpa only [Function.comp_def, Function.uncurry, G, ContinuousMap.coe_mk,
    circleDisplacementFamily_apply, Prod.fst_swap, Prod.snd_swap] using h

def continuousDisplacementFamily (E : ℝ) : C(AddCircle Real.pi, ℝ) :=
  ⟨cdfDisplacement (ν E), continuous_cdfDisplacement (ν E) (hν E)⟩

include hweak in
theorem continuous_continuousDisplacementFamily :
    Continuous (continuousDisplacementFamily ν hν) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_cdfDisplacement_family_joint ν hweak hν)

include hweak in
theorem uniformContinuousOn_continuousDisplacementFamily {K : Set ℝ} (hK : IsCompact K) :
    UniformContinuousOn (continuousDisplacementFamily ν hν) K :=
  hK.uniformContinuousOn_of_continuous
    (continuous_continuousDisplacementFamily ν hweak hν).continuousOn

include hweak hν in
theorem continuous_stationaryCDFLift_family_joint :
    Continuous (fun z : ℝ × ℝ => stationaryCDFLift (ν z.1) z.2) := by
  have hmk := (AddCircle.continuous_mk' Real.pi).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have harg := (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ)).prodMk hmk
  have hcomp := (continuous_cdfDisplacement_family_joint ν hweak hν).comp harg
  have hsum := (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ)).add hcomp
  change Continuous (fun z : ℝ × ℝ => z.2 + cdfDisplacement (ν z.1)
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples Real.pi) z.2)) at hsum
  simpa only [QuotientAddGroup.mk'_apply, stationaryCDFLift] using hsum

theorem stationaryCDFLift_difference_le_displacementNorm (E E' θ : ℝ) :
    |stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E') θ| ≤
      ‖continuousDisplacementFamily ν hν E - continuousDisplacementFamily ν hν E'‖ := by
  have h := (continuousDisplacementFamily ν hν E - continuousDisplacementFamily ν hν E').norm_coe_le_norm
    (θ : AddCircle Real.pi)
  have heq : stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E') θ =
      cdfDisplacement (ν E) (θ : AddCircle Real.pi) -
        cdfDisplacement (ν E') (θ : AddCircle Real.pi) := by
    unfold stationaryCDFLift
    ring
  rw [heq]
  simpa only [ContinuousMap.coe_sub, Pi.sub_apply, continuousDisplacementFamily,
    ContinuousMap.coe_mk, Real.norm_eq_abs] using h

include hweak hν in
theorem stationaryCDFLift_energy_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ E' ∈ K, |E - E'| < d →
      ∀ θ, |stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E') θ| < ε := by
  obtain ⟨d, hd, hbound⟩ := Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_continuousDisplacementFamily ν hweak hν hK) ε hε
  refine ⟨d, hd, ?_⟩
  intro E hE E' hE' hdist θ
  have h := hbound E hE E' hE' (by simpa only [Real.dist_eq] using hdist)
  exact (stationaryCDFLift_difference_le_displacementNorm ν hν E E' θ).trans_lt
    (by simpa only [dist_eq_norm] using h)

include hweak hν in
/-- Periodicity reduces arbitrary real angles to one compact strip. This
uniform modulus allows flat CDF intervals and needs no inverse CDF. -/
theorem stationaryCDFLift_phase_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ θ φ : ℝ, |θ - φ| < d →
      |stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E) φ| < ε := by
  have hc : ContinuousOn (fun z : ℝ × ℝ => stationaryCDFLift (ν z.1) z.2)
      (K ×ˢ Icc (-1 : ℝ) (Real.pi + 1)) :=
    (continuous_stationaryCDFLift_family_joint ν hweak hν).continuousOn
  have hcompact := hK.prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) (Real.pi + 1)))
  have hu := hcompact.uniformContinuousOn_of_continuous hc
  obtain ⟨d, hd, hbound⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min d 1, lt_min hd (by norm_num), ?_⟩
  intro E hE θ φ hclose
  let k := cdfCell θ
  let r := cdfReduced θ
  let y := φ - (k : ℝ) * Real.pi
  have hr : r ∈ Ico 0 Real.pi := cdfReduced_mem θ
  have h1 : |θ - φ| < 1 := hclose.trans_le (min_le_right _ _)
  have hy : y ∈ Icc (-1) (Real.pi + 1) := by
    have hl := (abs_lt.mp h1).1
    have hh := (abs_lt.mp h1).2
    dsimp [y, r, cdfReduced, k] at *
    constructor <;> linarith [hr.1, hr.2]
  have hr' : r ∈ Icc (-1) (Real.pi + 1) :=
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hdiff : |r - y| = |θ - φ| := by
    congr 1
    dsimp [r, y, cdfReduced, k]
    ring
  have hdist : dist (E, r) (E, y) < d := by
    simp only [Prod.dist_eq, dist_self, Real.dist_eq]
    rw [max_eq_right (abs_nonneg (r - y)), hdiff]
    exact hclose.trans_le (min_le_left _ _)
  have hb := hbound (E, r) ⟨hE, hr'⟩ (E, y) ⟨hE, hy⟩ hdist
  have her : r + (k : ℝ) * Real.pi = θ := by dsimp [r, cdfReduced, k]; ring
  have hey : y + (k : ℝ) * Real.pi = φ := by dsimp [y]; ring
  have hθ := stationaryCDFLift_add_int (ν E) r k
  have hφ := stationaryCDFLift_add_int (ν E) y k
  rw [her] at hθ
  rw [hey] at hφ
  calc
    _ = |stationaryCDFLift (ν E) r - stationaryCDFLift (ν E) y| := by
      rw [hθ, hφ]
      congr 1
      ring
    _ < ε := by simpa only [Real.dist_eq] using hb

include hweak hν in
theorem stationaryCDFLift_period_gap_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ E' ∈ K, |E - E'| < d →
      ∀ θ φ : ℝ, ∀ k : ℤ, |θ - φ - k * Real.pi| < d →
        |stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E') φ - k * Real.pi| < ε := by
  obtain ⟨dE, hdE, henergy⟩ := stationaryCDFLift_energy_uniform ν hweak hν hK (half_pos hε)
  obtain ⟨dθ, hdθ, hphase⟩ := stationaryCDFLift_phase_uniform ν hweak hν hK (half_pos hε)
  refine ⟨min dE dθ, lt_min hdE hdθ, ?_⟩
  intro E hE E' hE' hEE' θ φ k hclose
  have hr : |(θ - k * Real.pi) - φ| < dθ := by
    have heq : (θ - k * Real.pi) - φ = θ - φ - k * Real.pi := by ring
    rw [heq]
    exact hclose.trans_le (min_le_right _ _)
  have hp := hphase E hE (θ - k * Real.pi) φ hr
  have he := henergy E hE E' hE' (hEE'.trans_le (min_le_left _ _)) φ
  have hperiod : stationaryCDFLift (ν E) θ =
      stationaryCDFLift (ν E) (θ - k * Real.pi) + k * Real.pi := by
    have h := stationaryCDFLift_add_int (ν E) (θ - k * Real.pi) k
    simpa only [sub_add_cancel] using h
  calc
    _ = |(stationaryCDFLift (ν E) (θ - k * Real.pi) - stationaryCDFLift (ν E) φ) +
        (stationaryCDFLift (ν E) φ - stationaryCDFLift (ν E') φ)| := by
      rw [hperiod]
      congr 1
      ring
    _ ≤ |stationaryCDFLift (ν E) (θ - k * Real.pi) - stationaryCDFLift (ν E) φ| +
        |stationaryCDFLift (ν E) φ - stationaryCDFLift (ν E') φ| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hp he
    _ = ε := by ring

include hweak hν in
theorem stationaryCDFLift_initial_gap_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ E' ∈ K, |E - E'| < d →
      ∀ θ φ : ℝ, |θ - φ| < d →
        |stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E') φ| < ε := by
  obtain ⟨d, hd, hb⟩ := stationaryCDFLift_period_gap_uniform ν hweak hν hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE E' hE' hEE' θ φ hclose
  have hc : |θ - φ - (0 : ℤ) * Real.pi| < d := by simpa only [Int.cast_zero, zero_mul, sub_zero] using hclose
  simpa only [Int.cast_zero, zero_mul, sub_zero] using hb E hE E' hE' hEE' θ φ 0 hc

/-- Actual inverse stationary CDF regularity, derived from the authorized
qualitative input rather than a further regularity interface. -/
theorem continuous_inverseCDF_displacement (law : PotentialLaw) (input : Input law) :
    Continuous (continuousDisplacementFamily
      (fun E => (input.atEnergy E).inverseMeasure)
      (fun E => (input.atEnergy E).inverse_null_singletons)) :=
  continuous_continuousDisplacementFamily _ (continuous_selected_inverseMeasure law input) _

end FixedCouplingPoisson.Furstenberg
