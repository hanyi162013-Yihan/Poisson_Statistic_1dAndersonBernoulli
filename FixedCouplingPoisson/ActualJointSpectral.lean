import FixedCouplingPoisson.ActualJointEventually
import FixedCouplingPoisson.WeakProbabilityTransfer

/-! Actual finite Dirichlet window vectors and the spectral rounding transfer. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem dirichletEnergyWindowCount_measurable (n : ℕ) (a b : ℝ) :
    Measurable (fun ω : PotentialSpace =>
      dirichletEnergyWindowCount n (fun j => ω j.val) a b) := by
  classical
  by_cases hab : a ≤ b
  · let e : ℕ → ℕ → ℝ := fun _ i => if i = 0 then a else b
    have heq : (fun ω : PotentialSpace =>
        dirichletEnergyWindowCount n (fun j => ω j.val) a b) =
        (fun ω => (actualWindowSpectralCount e n 0 ω).toNat) := by
      funext ω
      have h := actualWindowSpectralCount_eq_card e n 0 ω (by simpa [e] using hab)
      simpa only [e, if_pos rfl, Nat.zero_add, if_neg (by omega : (1 : ℕ) ≠ 0),
        Int.toNat_natCast] using (congrArg Int.toNat h).symm
    rw [heq]
    exact (measurable_of_countable Int.toNat).comp (measurable_actualWindowSpectralCount e n 0)
  · have heq : (fun ω : PotentialSpace =>
        dirichletEnergyWindowCount n (fun j => ω j.val) a b) = fun _ => 0 := by
      funext ω
      unfold dirichletEnergyWindowCount
      have hempty : Finset.univ.filter (fun j : Fin n =>
          a < dirichletEigenvalues n (fun j => ω j.val) j ∧
          dirichletEigenvalues n (fun j => ω j.val) j ≤ b) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hj h
        exact hab (h.1.le.trans h.2)
      rw [hempty, Finset.card_empty]
    rw [heq]
    exact measurable_const

def actualEnergyWindowCountVector (e : ℕ → ℕ → ℝ) (s n : ℕ)
    (ω : PotentialSpace) : Fin s → ℕ := fun i =>
  dirichletEnergyWindowCount n (fun j => ω j.val) (e n i.val) (e n (i.val + 1))

theorem actualEnergyWindowCountVector_measurable (e : ℕ → ℕ → ℝ) (s n : ℕ) :
    Measurable (actualEnergyWindowCountVector e s n) :=
  measurable_pi_lambda _ fun i => dirichletEnergyWindowCount_measurable n _ _

def actualEnergyWindowCountRealLaw (law : PotentialLaw)
    (e : ℕ → ℕ → ℝ) (s n : ℕ) : ProbabilityMeasure (Fin s → ℝ) :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    ((show Measurable (fun x : Fin s → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
      (actualEnergyWindowCountVector_measurable e s n)).aemeasurable

/-- The finite Dirichlet spectrum itself has the independent Poisson vector
limit. The fixed endpoint anchor makes the actual terminal rounding error
vanish; all residual estimates are discharged by the phase model. -/
theorem actualEnergyWindowCountRealLaw_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s : ℕ) (E : ℝ) (κ : ℕ) (hκ : κ ≤ s)
    (hanchor : ∀ n, e n κ = E)
    (hcompact : ∀ᶠ n in atTop, ∀ i, i ≤ s → e n i ∈ K)
    (horder : ∀ᶠ n in atTop, ∀ i, i < s → e n i ≤ e n (i + 1))
    (houter : ∀ᶠ n in atTop, e n 0 ≤ e n s)
    (hp : ∀ᶠ n in atTop, ∀ i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hpouter : ∀ᶠ n in atTop, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
    (helim : ∀ i, i ≤ s → Tendsto (fun n => e n i) atTop (𝓝 E))
    (w : Fin s → ℝ≥0) (W : ℝ) (hW : 0 ≤ W)
    (hscale : ∀ i : Fin s, Tendsto (fun n =>
      (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (n : ℝ))
      atTop (𝓝 (w i : ℝ)))
    (houterScale : Tendsto (fun n =>
      (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (n : ℝ)) atTop (𝓝 W)) :
    Tendsto (fun n => actualEnergyWindowCountRealLaw law e s n)
      atTop (𝓝 (poissonRealProduct w)) := by
  let X : ℕ → PotentialSpace → Fin s → ℝ := fun n ω i =>
    (actualEnergyWindowCountVector e s n ω i : ℝ)
  let Y : ℕ → PotentialSpace → Fin s → ℝ := fun n ω i =>
    (canonicalColoredCountVector (e n) s n ω i : ℝ)
  have hX (n : ℕ) : Measurable (X n) :=
    (show Measurable (fun x : Fin s → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
      (actualEnergyWindowCountVector_measurable e s n)
  have hY (n : ℕ) : Measurable (Y n) :=
    (show Measurable (fun x : Fin s → ℕ => fun i => (x i : ℝ)) from by fun_prop).comp
      (canonicalColoredCountVector_measurable (e n) s n)
  have htime (i : ℕ) (hi : i < s) : Tendsto (fun n =>
      (idsCandidate law (e n (i + 1)) - idsCandidate law (e n i)) * (n : ℝ))
      atTop (𝓝 ((fun i : Fin s => (w i : ℝ)) ⟨i, hi⟩)) := hscale ⟨i, hi⟩
  have hround := actualWindow_rounding_success_from_IDS_scales_eventually law input E hK
    e s κ hκ hanchor hcompact horder hp
    (fun i hi => by simpa only [sub_self] using
      (helim (i + 1) (by omega)).sub (helim i hi.le))
    (fun i => if h : i < s then (w ⟨i, h⟩ : ℝ) else 0)
    (fun i hi => by simpa only [dif_pos hi] using htime i hi)
  have hgood : Tendsto (fun n => iidMeasure law {ω | X n ω = Y n ω})
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hround tendsto_const_nhds
    · filter_upwards [horder] with n hn
      apply measure_mono
      intro ω hω
      funext i
      have hc := actualWindowSpectralCount_eq_card e n i.val ω (hn i.val i.isLt)
      rw [hω i.val i.isLt, actualWindowWinding_eq_canonicalCrossingCount] at hc
      have hnat := congrArg Int.toNat hc
      simpa only [X, Y, actualEnergyWindowCountVector, canonicalColoredCountVector,
        canonicalNaturalCrossingCount, Int.toNat_natCast] using
          (congrArg (fun k : ℕ => (k : ℝ)) hnat).symm
    · exact Eventually.of_forall fun n => prob_le_one
  have hgoodReal : Tendsto (fun n => (iidMeasure law).real {ω | X n ω = Y n ω})
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hgood
  exact probabilityMeasure_map_tendsto_of_eq_probability_tendsto_one
    (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace) hX hY hgoodReal
    (canonicalColoredCountRealLaw_tendsto_poisson_eventually law input hK e s E
      hcompact horder houter hp hpouter helim w W hW hscale houterScale)

end FixedCouplingPoisson.Furstenberg
