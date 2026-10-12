import FixedCouplingPoisson.IDSExistence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.LeftRightLim

/-! Continuity of the actual integrated density of states.

Finite-volume one-sided mean-count limits, the proved rank-cut approximation,
and simplicity of the Dirichlet spectrum exclude every IDS jump. -/

namespace FixedCouplingPoisson
open Filter MeasureTheory
open scoped Topology

theorem nonstrictSpectralCount_tendsto_right (n : ℕ) (v : Fin n → ℝ) (E : ℝ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds E)) (hge : ∀ k, E ≤ e k) :
    Tendsto (fun k => (nonstrictSpectralCount n v (e k) : ℝ)) atTop
      (nhds (nonstrictSpectralCount n v E : ℝ)) := by
  classical
  simp only [nonstrictSpectralCount_eq_sum]
  apply tendsto_finsetSum
  intro i _
  by_cases hi : dirichletEigenvalues n v i ≤ E
  · have hik : ∀ k, dirichletEigenvalues n v i ≤ e k := fun k => hi.trans (hge k)
    simpa only [hi, hik, if_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  · have hlt : E < dirichletEigenvalues n v i := lt_of_not_ge hi
    have hEv := he.eventually (gt_mem_nhds hlt)
    simp only [hi, if_false]
    apply tendsto_const_nhds.congr'
    exact hEv.mono (fun k hk => by simp only [not_le.mpr hk, if_false])

theorem nonstrictSpectralCount_tendsto_left (n : ℕ) (v : Fin n → ℝ) (E : ℝ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds E)) (hlt : ∀ k, e k < E) :
    Tendsto (fun k => (nonstrictSpectralCount n v (e k) : ℝ)) atTop
      (nhds (strictSpectralCount n v E : ℝ)) := by
  classical
  simp only [nonstrictSpectralCount_eq_sum, strictSpectralCount_eq_sum]
  apply tendsto_finsetSum
  intro i _
  by_cases hi : dirichletEigenvalues n v i < E
  · have hEv := he.eventually (lt_mem_nhds hi)
    simp only [hi, if_true]
    apply tendsto_const_nhds.congr'
    exact hEv.mono (fun k hk => by simp only [hk.le, if_true])
  · have hik : ∀ k, ¬dirichletEigenvalues n v i ≤ e k := fun k =>
      not_le.mpr ((hlt k).trans_le (le_of_not_gt hi))
    simpa only [hi, hik, if_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem meanSpectralCount_tendsto_right (law : PotentialLaw) (n : ℕ) (E : ℝ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds E)) (hge : ∀ k, E ≤ e k) :
    Tendsto (fun k => meanSpectralCount law n (e k)) atTop
      (nhds (meanSpectralCount law n E)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (n : ℝ))
    (fun k => (measurable_nonstrictSpectralCount_real n (e k)).aestronglyMeasurable)
    (integrable_const (n : ℝ))
  · intro k
    exact Filter.Eventually.of_forall (fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (nonstrictSpectralCount_real_bounds n v (e k)).1]
        using (nonstrictSpectralCount_real_bounds n v (e k)).2)
  · exact Filter.Eventually.of_forall (fun v =>
      nonstrictSpectralCount_tendsto_right n v E e he hge)

theorem meanSpectralCount_tendsto_left (law : PotentialLaw) (n : ℕ) (E : ℝ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds E)) (hlt : ∀ k, e k < E) :
    Tendsto (fun k => meanSpectralCount law n (e k)) atTop
      (nhds (∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (n : ℝ))
    (fun k => (measurable_nonstrictSpectralCount_real n (e k)).aestronglyMeasurable)
    (integrable_const (n : ℝ))
  · intro k
    exact Filter.Eventually.of_forall (fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (nonstrictSpectralCount_real_bounds n v (e k)).1]
        using (nonstrictSpectralCount_real_bounds n v (e k)).2)
  · exact Filter.Eventually.of_forall (fun v =>
      nonstrictSpectralCount_tendsto_left n v E e he hlt)

noncomputable def energyApproachRight (E : ℝ) (k : ℕ) : ℝ := E + 1 / ((k + 1 : ℕ) : ℝ)

noncomputable def energyApproachLeft (E : ℝ) (k : ℕ) : ℝ := E - 1 / ((k + 1 : ℕ) : ℝ)

theorem energyApproachRight_tendsto (E : ℝ) :
    Tendsto (energyApproachRight E) atTop (nhdsWithin E (Set.Ioi E)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun k : ℕ => E + 1 / ((k + 1 : ℕ) : ℝ)) atTop (nhds E)
    have h : Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) := by
      simpa only [Function.comp_def] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [add_zero] using (tendsto_const_nhds (x := E)).add h
  · exact Filter.Eventually.of_forall (fun k => by
      change E < E + 1 / ((k + 1 : ℕ) : ℝ)
      have hp : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      exact lt_add_of_pos_right E (div_pos zero_lt_one hp))

theorem energyApproachLeft_tendsto (E : ℝ) :
    Tendsto (energyApproachLeft E) atTop (nhdsWithin E (Set.Iio E)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun k : ℕ => E - 1 / ((k + 1 : ℕ) : ℝ)) atTop (nhds E)
    have h : Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) := by
      simpa only [Function.comp_def] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [sub_zero] using (tendsto_const_nhds (x := E)).sub h
  · exact Filter.Eventually.of_forall (fun k => by
      change E - 1 / ((k + 1 : ℕ) : ℝ) < E
      have hp : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      exact sub_lt_self E (div_pos zero_lt_one hp))

theorem idsCandidate_leftLimit_error (law : PotentialLaw) (E : ℝ) (n : ℕ) (hn : n ≠ 0) :
    |(∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n) / (n : ℝ) -
      Function.leftLim (idsCandidate law) E| ≤ 2 / (n : ℝ) := by
  have he := energyApproachLeft_tendsto E
  have hs : ∀ k, energyApproachLeft E k < E := fun k => by
    have hp : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact sub_lt_self E (div_pos zero_lt_one hp)
  have hm := (meanSpectralCount_tendsto_left law n E (energyApproachLeft E)
    (tendsto_nhds_of_tendsto_nhdsWithin he) hs).div_const (n : ℝ)
  have hN := ((monotone_idsCandidate law).tendsto_leftLim E).comp he
  have hd := (hm.sub hN).abs
  exact le_of_tendsto hd (Filter.Eventually.of_forall fun k =>
    normalizedMeanCount_error law (energyApproachLeft E k) n hn)

theorem idsCandidate_rightLimit_error (law : PotentialLaw) (E : ℝ) (n : ℕ) (hn : n ≠ 0) :
    |normalizedMeanCount law E n - Function.rightLim (idsCandidate law) E| ≤ 2 / (n : ℝ) := by
  have he := energyApproachRight_tendsto E
  have hs : ∀ k, E ≤ energyApproachRight E k := fun k => by
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (Nat.cast_nonneg _))
  have hm := (meanSpectralCount_tendsto_right law n E (energyApproachRight E)
    (tendsto_nhds_of_tendsto_nhdsWithin he) hs).div_const (n : ℝ)
  have hN := ((monotone_idsCandidate law).tendsto_rightLim E).comp he
  have hd := (hm.sub hN).abs
  exact le_of_tendsto hd (Filter.Eventually.of_forall fun k =>
    normalizedMeanCount_error law (energyApproachRight E k) n hn)

theorem idsCandidate_jump_le (law : PotentialLaw) (E : ℝ) (n : ℕ) (hn : n ≠ 0) :
    Function.rightLim (idsCandidate law) E - Function.leftLim (idsCandidate law) E ≤
      5 / (n : ℝ) := by
  have hl := abs_le.mp (idsCandidate_leftLimit_error law E n hn)
  have hr := abs_le.mp (idsCandidate_rightLimit_error law E n hn)
  have hb := (integral_spectralCount_endpoint_bounds n E (finitePotentialMeasure law n)).2
  change meanSpectralCount law n E ≤
    (∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n) + 1 at hb
  have hbd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  rw [add_div] at hbd
  change -(2 / (n : ℝ)) ≤ meanSpectralCount law n E / (n : ℝ) -
      Function.rightLim (idsCandidate law) E ∧
    meanSpectralCount law n E / (n : ℝ) - Function.rightLim (idsCandidate law) E ≤
      2 / (n : ℝ) at hr
  have hfive : (5 : ℝ) / (n : ℝ) = 2 / (n : ℝ) + 2 / (n : ℝ) + 1 / (n : ℝ) := by ring
  rw [hfive]
  linarith [hl.2, hr.1]

/-- Continuity is obtained directly from finite spectra and the rank cut;
there is no stationary projective-measure continuity premise. -/
theorem continuous_idsCandidate (law : PotentialLaw) : Continuous (idsCandidate law) := by
  apply continuous_iff_continuousAt.mpr
  intro E
  apply (monotone_idsCandidate law).continuousAt_iff_leftLim_eq_rightLim.mpr
  have hgap : ∀ k : ℕ,
      Function.rightLim (idsCandidate law) E - Function.leftLim (idsCandidate law) E ≤
        5 / ((k + 1 : ℕ) : ℝ) := fun k => idsCandidate_jump_le law E (k + 1) (Nat.succ_ne_zero k)
  have hz := (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hle : Function.rightLim (idsCandidate law) E - Function.leftLim (idsCandidate law) E ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hz (Filter.Eventually.of_forall hgap)
  have hge := (monotone_idsCandidate law).leftLim_le_rightLim (le_refl E)
  linarith

end FixedCouplingPoisson
