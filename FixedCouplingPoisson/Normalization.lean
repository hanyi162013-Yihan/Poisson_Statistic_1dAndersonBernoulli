import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.IntermediateValue

/-!
# Deterministic microscopic normalization

These results formalize only the deterministic normalization argument in the last
proof of the manuscript. The IDS may be any real function differentiable at the
chosen center. No spectral or probabilistic conclusion is assumed here.
-/

open Filter Topology

namespace FixedCouplingPoisson

/-- The physical endpoint used for the linear normalization. The value at
`n = 0` is harmless; all limiting claims use `n → ∞`. -/
noncomputable def linearEndpoint (E ρ x : ℝ) (n : ℕ) : ℝ := E + x / ((n : ℝ) * ρ)

@[simp] theorem linearEndpoint_zero (E ρ : ℝ) (n : ℕ) :
    linearEndpoint E ρ 0 n = E := by
  simp [linearEndpoint]

/-- Every fixed microscopic endpoint approaches its fixed center. -/
theorem linearEndpoint_tendsto (E ρ x : ℝ) :
    Tendsto (linearEndpoint E ρ x) atTop (𝓝 E) := by
  have h : Tendsto (fun n : ℕ ↦ x / ((n : ℝ) * ρ)) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div, zero_div] using
      (tendsto_const_div_atTop_nhds_zero_nat x).div_const ρ
  change Tendsto (fun n : ℕ ↦ E + x / ((n : ℝ) * ρ)) atTop (𝓝 E)
  simpa only [add_zero] using tendsto_const_nhds.add h

/-- Differentiability at a single point, with nonzero derivative, gives the
microscopic IDS rate. Positivity is needed only for ordering the endpoints. -/
theorem differentiable_linear_rate {N : ℝ → ℝ} {E ρ : ℝ}
    (hN : HasDerivAt N ρ E) (hρ : ρ ≠ 0) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (N (linearEndpoint E ρ x n) - N E))
      atTop (𝓝 x) := by
  by_cases hx : x = 0
  · subst x
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · have ht : Tendsto (fun n : ℕ ↦ x / ((n : ℝ) * ρ)) atTop (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [div_mul_eq_div_div, zero_div] using
          (tendsto_const_div_atTop_nhds_zero_nat x).div_const ρ
      · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          div_ne_zero hx (mul_ne_zero (by exact_mod_cast (ne_of_gt hn)) hρ)
    have hs := (hN.tendsto_slope_zero.comp ht).mul_const (x / ρ)
    have hlim : ρ * (x / ρ) = x := by field_simp [hρ]
    rw [hlim] at hs
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    simp only [Function.comp_apply, smul_eq_mul, linearEndpoint]
    field_simp [hρ, hx, hn0]

/-- Adjacent microscopic intervals have their expected limiting IDS widths. -/
theorem differentiable_adjacent_linear_rate {N : ℝ → ℝ} {E ρ : ℝ}
    (hN : HasDerivAt N ρ E) (hρ : ρ ≠ 0) (a b : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (N (linearEndpoint E ρ b n) - N (linearEndpoint E ρ a n)))
      atTop (𝓝 (b - a)) := by
  convert (differentiable_linear_rate hN hρ b).sub
    (differentiable_linear_rate hN hρ a) using 1
  funext n
  ring

/-- A positive derivative preserves the strict ordering of all positive-volume
physical endpoint arrays. -/
theorem linearEndpoint_strictMono {E ρ : ℝ} (hρ : 0 < ρ)
    {n : ℕ} (hn : 0 < n) : StrictMono (fun x ↦ linearEndpoint E ρ x n) := by
  intro a b hab
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  change E + a / ((n : ℝ) * ρ) < E + b / ((n : ℝ) * ρ)
  linarith [div_lt_div_of_pos_right hab (mul_pos hnR hρ)]

/-- Positive partition widths yield positive limiting IDS rates. -/
theorem differentiable_adjacent_linear_rate_positive {N : ℝ → ℝ} {E ρ a b : ℝ}
    (hN : HasDerivAt N ρ E) (hρ : 0 < ρ) (hab : a < b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (N (linearEndpoint E ρ b n) - N (linearEndpoint E ρ a n)))
      atTop (𝓝 (b - a)) ∧ 0 < b - a :=
  ⟨differentiable_adjacent_linear_rate hN (ne_of_gt hρ) a b, sub_pos.mpr hab⟩

/-- Algebraic IDS increment identity for an already existing unfolding endpoint
array. Existence of such endpoints is a separate local inverse problem. -/
theorem unfolded_adjacent_rate {N : ℝ → ℝ} {E a b ea eb : ℝ} {n : ℕ}
    (hn : n ≠ 0) (ha : N ea = N E + a / (n : ℝ))
    (hb : N eb = N E + b / (n : ℝ)) :
    (n : ℝ) * (N eb - N ea) = b - a := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [ha, hb]
  field_simp [hn0]
  ring

/-- Local strict increase identifies the zero unfolded endpoint exactly. -/
theorem unfolded_zero_anchor {N : ℝ → ℝ} {J : Set ℝ} {E e : ℝ}
    (hN : StrictMonoOn N J) (hE : E ∈ J) (he : e ∈ J)
    (hzero : N e = N E) : e = E :=
  hN.injOn he hE hzero

/-- A neighborhood contains a smaller closed interval with the center in its
interior. This supplies two strict IDS brackets for local unfolding. -/
theorem normalization_local_bracket {J : Set ℝ} {E : ℝ} (hJ : J ∈ 𝓝 E) :
    ∃ a b : ℝ, a < E ∧ E < b ∧ Set.Icc a b ⊆ J := by
  obtain ⟨a, b, hE, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hJ
  refine ⟨(a + E) / 2, (E + b) / 2, ?_, ?_, ?_⟩
  · linarith [hE.1]
  · linarith [hE.2]
  · intro y hy
    apply hsub
    constructor <;> linarith [hy.1, hy.2, hE.1, hE.2]

/-- Continuity and strict increase on a neighborhood give the uniquely defined
IDS-unfolding endpoints for every sufficiently large volume. -/
theorem unfolded_endpoint_eventually_exists_unique {N : ℝ → ℝ} {E : ℝ}
    {J : Set ℝ} (hJ : J ∈ 𝓝 E) (hcont : ContinuousOn N J)
    (hmono : StrictMonoOn N J) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∃! e : ℝ, e ∈ J ∧ N e = N E + x / (n : ℝ) := by
  obtain ⟨a, b, ha, hb, habJ⟩ := normalization_local_bracket hJ
  have hab : a ≤ b := le_trans ha.le hb.le
  have haJ : a ∈ J := habJ (Set.left_mem_Icc.mpr hab)
  have hbJ : b ∈ J := habJ (Set.right_mem_Icc.mpr hab)
  have hEJ : E ∈ J := mem_of_mem_nhds hJ
  have htarget : Tendsto (fun n : ℕ ↦ N E + x / (n : ℝ)) atTop (𝓝 (N E)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat x)
  have hbetween := htarget.eventually
    (Ioo_mem_nhds (hmono haJ hEJ ha) (hmono hEJ hbJ hb))
  filter_upwards [hbetween] with n hn
  obtain ⟨e, he, hNe⟩ := intermediate_value_Icc hab (hcont.mono habJ) ⟨hn.1.le, hn.2.le⟩
  refine ⟨e, ⟨habJ he, hNe⟩, ?_⟩
  intro y hy
  exact hmono.injOn hy.1 (habJ he) (hy.2.trans hNe.symm)

/-- Any eventually defined local unfolding endpoint array approaches the center.
Continuity of the IDS is only needed for endpoint existence, not for this
inverse-continuity argument. -/
theorem unfolded_endpoint_tendsto {N : ℝ → ℝ} {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hmono : StrictMonoOn N J) (x : ℝ) (e : ℕ → ℝ)
    (he : ∀ᶠ n : ℕ in atTop, e n ∈ J ∧ N (e n) = N E + x / (n : ℝ)) :
    Tendsto e atTop (𝓝 E) := by
  obtain ⟨l, r, hl, hr, hlrJ⟩ := normalization_local_bracket hJ
  have hEJ : E ∈ J := mem_of_mem_nhds hJ
  have htarget : Tendsto (fun n : ℕ ↦ N E + x / (n : ℝ)) atTop (𝓝 (N E)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat x)
  have hNe : Tendsto (fun n ↦ N (e n)) atTop (𝓝 (N E)) :=
    htarget.congr' (he.mono fun n hn ↦ hn.2.symm)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c, hmc, hcE⟩ := exists_between (max_lt ha hl)
    have hac : a < c := (le_max_left a l).trans_lt hmc
    have hlc : l < c := (le_max_right a l).trans_lt hmc
    have hcJ : c ∈ J := hlrJ ⟨hlc.le, (hcE.trans hr).le⟩
    have hlt := (tendsto_order.mp hNe).1 (N c) (hmono hcJ hEJ hcE)
    filter_upwards [he, hlt] with n hn hnlt
    exact hac.trans ((hmono.lt_iff_lt hcJ hn.1).mp hnlt)
  · intro b hb
    obtain ⟨c, hEc, hcm⟩ := exists_between (lt_min hb hr)
    have hcb : c < b := hcm.trans_le (min_le_left b r)
    have hcr : c < r := hcm.trans_le (min_le_right b r)
    have hcJ : c ∈ J := hlrJ ⟨(hl.trans hEc).le, hcr.le⟩
    have hlt := (tendsto_order.mp hNe).2 (N c) (hmono hEJ hcJ hEc)
    filter_upwards [he, hlt] with n hn hnlt
    exact ((hmono.lt_iff_lt hn.1 hcJ).mp hnlt).trans hcb

/-- Local strict increase orders the unique unfolded endpoint arrays. -/
theorem unfolded_endpoint_lt {N : ℝ → ℝ} {J : Set ℝ} {E a b ea eb : ℝ}
    {n : ℕ} (hmono : StrictMonoOn N J) (hea : ea ∈ J) (heb : eb ∈ J)
    (hn : 0 < n) (hab : a < b)
    (ha : N ea = N E + a / (n : ℝ)) (hb : N eb = N E + b / (n : ℝ)) :
    ea < eb := by
  apply (hmono.lt_iff_lt hea heb).mp
  rw [ha, hb]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith [div_lt_div_of_pos_right hab hnR]

/-- A globally monotone function that is strictly increasing locally at a cut
reflects the strict cut for every real argument, even arguments outside the
neighborhood. -/
theorem monotone_local_strict_cut {N : ℝ → ℝ} {J : Set ℝ} {a : ℝ}
    (hmono : Monotone N) (hstrict : StrictMonoOn N J) (ha : J ∈ 𝓝 a)
    (y : ℝ) : a < y ↔ N a < N y := by
  constructor
  · intro hay
    obtain ⟨l, r, har, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ha
    obtain ⟨c, hac, hcm⟩ := exists_between (lt_min hay har.2)
    have hcJ : c ∈ J := hsub ⟨har.1.trans hac, hcm.trans_le (min_le_right y r)⟩
    exact (hstrict (mem_of_mem_nhds ha) hcJ hac).trans_le
      (hmono (hcm.trans_le (min_le_left y r)).le)
  · intro hNy
    by_contra hay
    exact (not_lt_of_ge (hmono (le_of_not_gt hay))) hNy

/-- Unfolded interval membership is equivalent to physical interval membership
for every energy, including energies outside the local unfolding neighborhood.
This is the deterministic identity behind equality of the two spectral counts. -/
theorem unfolded_window_iff {N : ℝ → ℝ} {J : Set ℝ} {E a b ea eb y : ℝ}
    {n : ℕ} (hmono : Monotone N) (hstrict : StrictMonoOn N J)
    (hea : J ∈ 𝓝 ea) (heb : J ∈ 𝓝 eb) (hn : 0 < n)
    (ha : N ea = N E + a / (n : ℝ)) (hb : N eb = N E + b / (n : ℝ)) :
    (a < (n : ℝ) * (N y - N E) ∧ (n : ℝ) * (N y - N E) ≤ b) ↔
      (ea < y ∧ y ≤ eb) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hscaleA : (n : ℝ) * (N ea - N E) = a := by
    rw [ha]
    field_simp [hn0]
    <;> ring
  have hscaleB : (n : ℝ) * (N eb - N E) = b := by
    rw [hb]
    field_simp [hn0]
    <;> ring
  have hupper : N y ≤ N eb ↔ y ≤ eb := by
    simpa only [not_lt] using
      (not_congr (monotone_local_strict_cut hmono hstrict heb y)).symm
  rw [← hscaleA, ← hscaleB, mul_lt_mul_iff_right₀ hnR,
    mul_le_mul_iff_right₀ hnR, sub_lt_sub_iff_right, sub_le_sub_iff_right,
    ← monotone_local_strict_cut hmono hstrict hea y, hupper]

end FixedCouplingPoisson
