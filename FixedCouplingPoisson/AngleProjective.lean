import FixedCouplingPoisson.CanonicalPhase
import FixedCouplingPoisson.FurstenbergInterface
import FixedCouplingPoisson.ProjectiveTopology
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Homeomorph.Lemmas

/-!
Concrete angle/projective identification for the inverse-stationary CDF.
The actual angular unit vector descends to a homeomorphism between the
angle circle modulo pi and the real projective line. No Furstenberg input
is used for this deterministic identification.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open Real Set
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

def phaseProjective (θ : ℝ) : ProjectivePoint :=
  Projectivization.mk ℝ (angleVector θ) (angleVector_ne_zero θ)

theorem continuous_angleVector : Continuous angleVector := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Real.continuous_cos
  · exact Real.continuous_sin

theorem continuous_phaseProjective : Continuous phaseProjective :=
  continuous_projectivize.comp (continuous_angleVector.subtype_mk angleVector_ne_zero)

theorem wedge_angleVector (θ φ : ℝ) :
    wedge (angleVector θ) (angleVector φ) = Real.sin (φ - θ) := by
  simp only [wedge, angleVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sin_sub]
  ring

theorem phaseProjective_eq_iff (θ φ : ℝ) :
    phaseProjective θ = phaseProjective φ ↔ Real.sin (φ - θ) = 0 := by
  unfold phaseProjective
  rw [← wedge_eq_zero_iff_projective_eq, wedge_angleVector]

theorem phaseProjective_add_int (θ : ℝ) (k : ℤ) :
    phaseProjective (θ + k * Real.pi) = phaseProjective θ := by
  apply (wedge_eq_zero_iff_projective_eq _ _ _ _).mp
  rw [angleVector_add_int, wedge_smul_left, wedge_self, mul_zero]

def complexOfVector (u : Vector2) : ℂ := ⟨u 0, u 1⟩

theorem complexOfVector_ne_zero (u : Vector2) (hu : u ≠ 0) :
    complexOfVector u ≠ 0 := by
  intro h
  apply hu
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem norm_complexOfVector (u : Vector2) :
    ‖complexOfVector u‖ = euclideanNorm u := by
  simp only [complexOfVector, Complex.norm_def, Complex.normSq_mk, euclideanNorm,
    euclideanNormSq, pow_two]

theorem vector_eq_norm_smul_angle (u : Vector2) :
    u = euclideanNorm u • angleVector (complexOfVector u).arg := by
  ext i
  fin_cases i
  · change u 0 = euclideanNorm u * Real.cos (complexOfVector u).arg
    have h := (Complex.norm_mul_cos_arg (complexOfVector u)).symm
    rw [norm_complexOfVector] at h
    exact h
  · change u 1 = euclideanNorm u * Real.sin (complexOfVector u).arg
    have h := (Complex.norm_mul_sin_arg (complexOfVector u)).symm
    rw [norm_complexOfVector] at h
    exact h

theorem phaseProjective_surjective : Function.Surjective phaseProjective := by
  intro x
  induction x using Projectivization.ind with
  | h u hu =>
    refine ⟨(complexOfVector u).arg, ?_⟩
    apply (wedge_eq_zero_iff_projective_eq _ _ _ _).mp
    calc
      _ = wedge (angleVector (complexOfVector u).arg)
          (euclideanNorm u • angleVector (complexOfVector u).arg) :=
        congrArg (wedge (angleVector (complexOfVector u).arg)) (vector_eq_norm_smul_angle u)
      _ = 0 := by rw [wedge_smul_right, wedge_self, mul_zero]

def angleCircleProjective : AddCircle Real.pi → ProjectivePoint :=
  AddCircle.liftIco Real.pi 0 phaseProjective

theorem continuous_angleCircleProjective : Continuous angleCircleProjective := by
  apply AddCircle.liftIco_zero_continuous
  · simpa using (phaseProjective_add_int 0 1).symm
  · exact continuous_phaseProjective.continuousOn

theorem angleCircleProjective_coe (θ : ℝ) :
    angleCircleProjective (θ : AddCircle Real.pi) = phaseProjective θ := by
  let α := (AddCircle.equivIco Real.pi 0 (θ : AddCircle Real.pi) : ℝ)
  have hα : (α : AddCircle Real.pi) = θ := AddCircle.coe_equivIco
  have hm : α - θ ∈ AddSubgroup.zmultiples Real.pi :=
    QuotientAddGroup.eq_iff_sub_mem.mp hα
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  have hαθ : α = θ + (k : ℝ) * Real.pi := by
    rw [zsmul_eq_mul] at hk
    linarith
  change phaseProjective α = phaseProjective θ
  rw [hαθ, phaseProjective_add_int]

theorem angleCircleProjective_injective : Function.Injective angleCircleProjective := by
  intro x y hxy
  let α := AddCircle.equivIco Real.pi 0 x
  let β := AddCircle.equivIco Real.pi 0 y
  have ha : (α : ℝ) ∈ Ico 0 Real.pi := by simpa using α.2
  have hb : (β : ℝ) ∈ Ico 0 Real.pi := by simpa using β.2
  have hsin : Real.sin ((β : ℝ) - (α : ℝ)) = 0 :=
    (phaseProjective_eq_iff _ _).mp hxy
  have hab : (β : ℝ) - (α : ℝ) = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [ha.2, hb.1])
      (by linarith [hb.2, ha.1])).mp hsin
  apply (AddCircle.equivIco Real.pi 0).injective
  exact Subtype.ext (by linarith)

theorem angleCircleProjective_surjective : Function.Surjective angleCircleProjective := by
  intro x
  obtain ⟨θ, hθ⟩ := phaseProjective_surjective x
  exact ⟨θ, (angleCircleProjective_coe θ).trans hθ⟩

/-- The actual angle modulo π identifies the real projective line. -/
def angleProjectiveHomeomorph : AddCircle Real.pi ≃ₜ ProjectivePoint :=
  (Equiv.ofBijective angleCircleProjective
    ⟨angleCircleProjective_injective, angleCircleProjective_surjective⟩).toHomeomorphOfContinuousClosed
      continuous_angleCircleProjective continuous_angleCircleProjective.isClosedMap

@[simp] theorem angleProjectiveHomeomorph_coe (θ : ℝ) :
    angleProjectiveHomeomorph (θ : AddCircle Real.pi) = phaseProjective θ :=
  angleCircleProjective_coe θ

theorem phaseProjective_eq_iff_coe (θ φ : ℝ) :
    phaseProjective θ = phaseProjective φ ↔
      (θ : AddCircle Real.pi) = (φ : AddCircle Real.pi) := by
  rw [← angleProjectiveHomeomorph_coe, ← angleProjectiveHomeomorph_coe]
  exact angleProjectiveHomeomorph.injective.eq_iff

end FixedCouplingPoisson.Furstenberg
