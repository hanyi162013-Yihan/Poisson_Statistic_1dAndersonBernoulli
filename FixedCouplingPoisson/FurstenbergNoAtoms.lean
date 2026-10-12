import FixedCouplingPoisson.ProjectiveTopology
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Atom-free stationary probabilities for the actual transfer action

This module uses no `Furstenberg.Input`. A positive atom of a finite measure
gives a finite nonempty set of atoms of maximal mass. Stationarity forces
that set to be invariant under almost every transfer. Nonconstancy of the
single-site law supplies two distinct transfers in this full-measure set,
contradicting the already proved explicit shear argument.

No support or topological irreducibility assumption is added. Boundedness of
the single-site law and positivity of the logarithmic mean are not used.
-/

noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set
open scoped ENNReal

namespace AtomArgument

/-- A finite measure has only finitely many atoms above a positive threshold. -/
theorem finite_large_atoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    {c : ℝ≥0∞} (hc : 0 < c) : {x : α | c ≤ μ {x}}.Finite := by
  by_contra h
  have htop : μ {x : α | c ≤ μ {x}} = ∞ :=
    Set.Infinite.meas_eq_top h ⟨c, hc.ne', fun _ hx => hx⟩
  exact measure_ne_top μ _ htop

/-- Once there is any positive atom, the largest atomic mass is attained.
The proof maximizes on one finite positive superlevel set, rather than
introducing a supremum or a countable enumeration of all atoms. -/
theorem exists_maximal_atom {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (hatom : ∃ p : α, 0 < μ {p}) :
    ∃ p : α, 0 < μ {p} ∧ ∀ q : α, μ {q} ≤ μ {p} := by
  obtain ⟨p, hp⟩ := hatom
  let S : Set α := {q : α | μ {p} ≤ μ {q}}
  have hS : S.Finite := finite_large_atoms μ hp
  have hne : S.Nonempty := ⟨p, by change μ {p} ≤ μ {p}; exact le_rfl⟩
  obtain ⟨q, hq, hmax⟩ := Set.exists_max_image S (fun x => μ {x}) hS hne
  refine ⟨q, hp.trans_le hq, ?_⟩
  intro x
  by_cases hx : x ∈ S
  · exact hmax x hx
  · exact (lt_of_not_ge hx).le.trans hq

/-- The equal-mass maximal-atom set is finite. -/
theorem finite_maximal_atoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (p : α) (hp : 0 < μ {p}) : {q : α | μ {q} = μ {p}}.Finite := by
  exact (finite_large_atoms μ hp).subset (fun _ hq => hq.ge)

/-- Every almost-everywhere property for a nonconstant single-site law
holds at two distinct potential values. This avoids passing from a.e.
invariance to support invariance. -/
theorem exists_two_potentials (law : PotentialLaw) {P : ℝ → Prop}
    (hP : ∀ᵐ v ∂law.measure, P v) :
    ∃ a b : ℝ, P a ∧ P b ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := hP.exists
  have hb : ∃ b : ℝ, P b ∧ b ≠ a := by
    by_contra hb
    have heq : (fun v : ℝ => v) =ᵐ[law.measure] (fun _ => a) := by
      filter_upwards [hP] with v hv
      by_contra hva
      exact hb ⟨v, hv, hva⟩
    apply law.nonconstant a
    calc
      law.measure = law.measure.map (fun v : ℝ => v) := Measure.map_id'.symm
      _ = law.measure.map (fun _ : ℝ => a) := Measure.map_congr heq
      _ = Measure.dirac a := by simp
  obtain ⟨b, hb, hba⟩ := hb
  exact ⟨a, b, ha, hb, hba.symm⟩

/-- The other order of the actual projective inverse identity. -/
theorem forward_inverse (E v : ℝ) (p : ProjectivePoint) :
    transferProjective E v (transferInverseProjective E v p) = p := by
  rw [← Projectivization.mk_rep p, transferInverseProjective_mk, transferProjective_mk]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simp only [one_smul, Matrix.mulVec_mulVec, transfer_mul_transferInv, Matrix.one_mulVec]

theorem inverse_injective (E v : ℝ) :
    Function.Injective (transferInverseProjective E v) := by
  intro p q h
  have h' := congrArg (transferProjective E v) h
  simpa only [forward_inverse] using h'

/-- A fiber of the actual transfer action is exactly the singleton
containing the actual inverse image. -/
theorem forward_singleton_fiber (E v : ℝ) (p : ProjectivePoint) :
    (fun q : ProjectivePoint => transferProjective E v q) ⁻¹' {p} =
      {transferInverseProjective E v p} := by
  ext q
  change transferProjective E v q = p ↔ q = transferInverseProjective E v p
  constructor
  · intro h
    have h' := congrArg (transferInverseProjective E v) h
    simpa only [transferInverseProjective_transfer] using h'
  · rintro rfl
    exact forward_inverse E v p

/-- Measurability of inverse-image atomic mass follows from product
sections of the measurable transfer fiber. -/
theorem measurable_inverse_atom_mass (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (p : ProjectivePoint) :
    Measurable (fun v : ℝ => (ν : Measure ProjectivePoint)
      {transferInverseProjective E v p}) := by
  have hs : MeasurableSet ((forwardStep E) ⁻¹' {p}) :=
    measurable_forwardStep E (measurableSet_singleton p)
  have hm := measurable_measure_prodMk_left (ν := (ν : Measure ProjectivePoint)) hs
  have heq : (fun v : ℝ => (ν : Measure ProjectivePoint)
        (Prod.mk v ⁻¹' ((forwardStep E) ⁻¹' {p}))) =
      (fun v : ℝ => (ν : Measure ProjectivePoint)
        {transferInverseProjective E v p}) := by
    funext v
    change (ν : Measure ProjectivePoint)
        ((fun q : ProjectivePoint => transferProjective E v q) ⁻¹' {p}) = _
    rw [forward_singleton_fiber]
  rw [heq] at hm
  exact hm

/-- Singleton stationarity, with the genuine inverse transfer appearing
inside the integral over the genuine single-site law. -/
theorem forwardStationary_singleton (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (p : ProjectivePoint) :
    (ν : Measure ProjectivePoint) {p} =
      ∫⁻ v : ℝ, (ν : Measure ProjectivePoint)
        {transferInverseProjective E v p} ∂law.measure := by
  have hmap := congrArg (fun η : ProbabilityMeasure ProjectivePoint =>
    (η : Measure ProjectivePoint)) hν
  change (law.measure.prod (ν : Measure ProjectivePoint)).map (forwardStep E) =
    (ν : Measure ProjectivePoint) at hmap
  calc
    (ν : Measure ProjectivePoint) {p} =
        ((law.measure.prod (ν : Measure ProjectivePoint)).map (forwardStep E)) {p} :=
      congrArg (fun μ : Measure ProjectivePoint => μ {p}) hmap.symm
    _ = (law.measure.prod (ν : Measure ProjectivePoint)) ((forwardStep E) ⁻¹' {p}) :=
      Measure.map_apply (measurable_forwardStep E) (measurableSet_singleton p)
    _ = ∫⁻ v : ℝ, (ν : Measure ProjectivePoint)
        (Prod.mk v ⁻¹' ((forwardStep E) ⁻¹' {p})) ∂law.measure :=
      Measure.prod_apply (measurable_forwardStep E (measurableSet_singleton p))
    _ = _ := by
      apply lintegral_congr
      intro v
      change (ν : Measure ProjectivePoint)
          ((fun q : ProjectivePoint => transferProjective E v q) ⁻¹' {p}) = _
      rw [forward_singleton_fiber]

/-- At a maximal atom, stationarity and the upper bound force equality
almost everywhere in the single-site variable. -/
theorem ae_inverse_maximal_atom (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (p : ProjectivePoint)
    (hmax : ∀ q : ProjectivePoint, (ν : Measure ProjectivePoint) {q} ≤
      (ν : Measure ProjectivePoint) {p}) :
    ∀ᵐ v ∂law.measure,
      (ν : Measure ProjectivePoint) {transferInverseProjective E v p} =
        (ν : Measure ProjectivePoint) {p} := by
  have hstationary := forwardStationary_singleton law E ν hν p
  apply ae_eq_of_ae_le_of_lintegral_le
    (Filter.Eventually.of_forall fun v => hmax (transferInverseProjective E v p))
    (by rw [← hstationary]; exact measure_ne_top (ν : Measure ProjectivePoint) _)
    measurable_const.aemeasurable
  rw [lintegral_const, measure_univ, mul_one, ← hstationary]

/-- Inverse invariance of a finite set under a bijection also gives
forward invariance. Only the finite set is inverted here. -/
theorem forward_invariant_of_inverse_invariant (E v : ℝ)
    (S : Set ProjectivePoint) (hS : S.Finite)
    (hInv : ∀ p ∈ S, transferInverseProjective E v p ∈ S) :
    ∀ p ∈ S, transferProjective E v p ∈ S := by
  have hSurj : Set.SurjOn (transferInverseProjective E v) S S :=
    ((hS.injOn_iff_bijOn_of_mapsTo hInv).mp (inverse_injective E v).injOn).surjOn
  intro p hp
  obtain ⟨q, hq, hqp⟩ := hSurj hp
  rw [← hqp, forward_inverse]
  exact hq

end AtomArgument

/-- Every forward-stationary probability for the actual nonconstant
Schrödinger transfer law is atom-free. No external Furstenberg input is used. -/
theorem forwardStationary_null_singletons (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (p : ProjectivePoint) : (ν : Measure ProjectivePoint) {p} = 0 := by
  by_contra hp
  have hatom : ∃ q : ProjectivePoint, 0 < (ν : Measure ProjectivePoint) {q} :=
    ⟨p, bot_lt_iff_ne_bot.mpr hp⟩
  obtain ⟨q, hq, hmax⟩ := AtomArgument.exists_maximal_atom
    (ν : Measure ProjectivePoint) hatom
  let S : Set ProjectivePoint :=
    {r : ProjectivePoint | (ν : Measure ProjectivePoint) {r} =
      (ν : Measure ProjectivePoint) {q}}
  have hS : S.Finite := AtomArgument.finite_maximal_atoms
    (ν : Measure ProjectivePoint) q hq
  have hne : S.Nonempty := ⟨q, rfl⟩
  have hInv : ∀ᵐ v ∂law.measure, ∀ r ∈ S, transferInverseProjective E v r ∈ S := by
    apply (ae_ball_iff hS.countable).mpr
    intro r hr
    have hmaxr : ∀ t : ProjectivePoint,
        (ν : Measure ProjectivePoint) {t} ≤ (ν : Measure ProjectivePoint) {r} := by
      intro t
      change (ν : Measure ProjectivePoint) {r} = (ν : Measure ProjectivePoint) {q} at hr
      rw [hr]
      exact hmax t
    filter_upwards [AtomArgument.ae_inverse_maximal_atom law E ν hν r hmaxr] with v hv
    exact hv.trans hr
  have hForward : ∀ᵐ v ∂law.measure, ∀ r ∈ S, transferProjective E v r ∈ S :=
    hInv.mono fun v hv => AtomArgument.forward_invariant_of_inverse_invariant E v S hS hv
  obtain ⟨a, b, ha, hb, hab⟩ := AtomArgument.exists_two_potentials law hForward
  exact no_finite_invariant_set_two_transfers E a b hab S hS hne ha hb

end FixedCouplingPoisson.Furstenberg
