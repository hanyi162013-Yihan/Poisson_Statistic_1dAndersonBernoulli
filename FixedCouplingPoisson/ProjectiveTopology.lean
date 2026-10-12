import FixedCouplingPoisson.FurstenbergInterface
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Ordinary topology of the actual real projective line

The topology is the explicit nonzero-vector quotient from
`FurstenbergInterface`. Hausdorff separation follows from the genuine
Euclidean determinant distance. Compactness follows from a continuous
surjection of the ordinary sup-norm sphere; that sphere is used only for
topology and does not replace the Euclidean cocycle. The quotient map is open,
which transfers second countability from the nonzero-vector space.

These results use no external Furstenberg input.
-/

noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix
open scoped Topology

theorem continuous_projectiveDistance_right (q : ProjectivePoint) :
    Continuous (fun p : ProjectivePoint => projectiveDistance p q) := by
  apply projectivize_isQuotientMap.continuous_iff.mpr
  have heq : (fun u : NonzeroVector => projectiveDistance (projectivize u) q) =
      (fun u : NonzeroVector => determinantDistance u q.rep) := by
    funext u
    conv_lhs => rw [← Projectivization.mk_rep q]
    exact projectiveDistance_mk u q.rep u.2 q.rep_nonzero
  change Continuous (fun u : NonzeroVector => projectiveDistance (projectivize u) q)
  rw [heq]
  have h0 : Continuous (fun u : NonzeroVector => (u : Vector2) 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun u : NonzeroVector => (u : Vector2) 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  have hw : Continuous (fun u : NonzeroVector => wedge u q.rep) :=
    (h0.mul continuous_const).sub (h1.mul continuous_const)
  exact hw.abs.div
    ((continuous_euclideanNorm.comp continuous_subtype_val).mul continuous_const)
    (fun u => (mul_pos (euclideanNorm_pos u u.2)
      (euclideanNorm_pos q.rep q.rep_nonzero)).ne')

/-- Hausdorff separation is proved for the quotient, not postulated. -/
instance projectiveT2 : T2Space ProjectivePoint := by
  let f : ProjectivePoint → ProjectivePoint → ℝ := fun p q => projectiveDistance p q
  have hf : Continuous f := continuous_pi fun q => continuous_projectiveDistance_right q
  have hi : Function.Injective f := by
    intro p q h
    have he := congrFun h q
    exact (projectiveDistance_eq_zero_iff p q).mp
      (he.trans ((projectiveDistance_eq_zero_iff q q).mpr rfl))
  exact T2Space.of_injective_continuous hi hf

/-- The ordinary sup-norm sphere is used solely as a compact topological
parameter space. The cocycle throughout this file remains Euclidean. -/
abbrev TopologicalUnitSphere := Metric.sphere (0 : Vector2) 1

def sphereToNonzero (u : TopologicalUnitSphere) : NonzeroVector :=
  ⟨u, by
    have hn : ‖(u : Vector2)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.2
    intro hz
    exact zero_ne_one (by simpa only [hz, norm_zero] using hn)⟩

def sphereToProjective (u : TopologicalUnitSphere) : ProjectivePoint :=
  projectivize (sphereToNonzero u)

theorem continuous_sphereToProjective : Continuous sphereToProjective :=
  continuous_projectivize.comp (continuous_subtype_val.subtype_mk fun u => (sphereToNonzero u).2)

theorem sphereToProjective_surjective : Function.Surjective sphereToProjective := by
  intro p
  have hn : 0 < ‖p.rep‖ := norm_pos_iff.mpr p.rep_nonzero
  let u : Vector2 := ‖p.rep‖⁻¹ • p.rep
  have hu : ‖u‖ = 1 := by
    change ‖‖p.rep‖⁻¹ • p.rep‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  let s : TopologicalUnitSphere := ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩
  refine ⟨s, ?_⟩
  change Projectivization.mk ℝ u (sphereToNonzero s).2 = p
  rw [← Projectivization.mk_rep p]
  exact (Projectivization.mk_eq_mk_iff' ℝ u p.rep _ _).mpr ⟨‖p.rep‖⁻¹, rfl⟩

instance projectiveCompactSpace : CompactSpace ProjectivePoint :=
  sphereToProjective_surjective.compactSpace continuous_sphereToProjective


/-- Unit scalings act continuously on the nonzero-vector parameter space. -/
def scaleNonzero (a : ℝˣ) (u : NonzeroVector) : NonzeroVector :=
  ⟨(a : ℝ) • (u : Vector2), smul_ne_zero (Units.ne_zero a) u.2⟩

theorem continuous_scaleNonzero (a : ℝˣ) : Continuous (scaleNonzero a) := by
  have hv : Continuous (fun u : NonzeroVector => (u : Vector2)) := continuous_subtype_val
  have h : Continuous (fun u : NonzeroVector => (a : ℝ) • (u : Vector2)) :=
    hv.const_smul (a : ℝ)
  exact h.subtype_mk fun u => (scaleNonzero a u).2

theorem isOpenMap_projectivize : IsOpenMap projectivize := by
  intro U hU
  apply projectivize_isQuotientMap.isCoinducing.isOpen_preimage.mp
  have hs : projectivize ⁻¹' (projectivize '' U) =
      ⋃ a : ℝˣ, scaleNonzero a ⁻¹' U := by
    ext u
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨v, hv, he⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ (v : Vector2) (u : Vector2) v.2 u.2).mp he
      refine ⟨a, ?_⟩
      have heq : scaleNonzero a u = v := by
        apply Subtype.ext
        change (a : ℝ) • (u : Vector2) = (v : Vector2)
        simpa only [Units.smul_def] using ha
      simpa only [heq] using hv
    · rintro ⟨a, ha⟩
      refine ⟨scaleNonzero a u, ha, ?_⟩
      exact (Projectivization.mk_eq_mk_iff ℝ
        (scaleNonzero a u : Vector2) (u : Vector2) (scaleNonzero a u).2 u.2).mpr ⟨a, rfl⟩
  rw [hs]
  exact isOpen_iUnion fun a => hU.preimage (continuous_scaleNonzero a)

instance projectiveSecondCountable : SecondCountableTopology ProjectivePoint :=
  projectivize_isQuotientMap.secondCountableTopology isOpenMap_projectivize

end FixedCouplingPoisson.Furstenberg
