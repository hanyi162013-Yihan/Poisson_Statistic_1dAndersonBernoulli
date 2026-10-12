import FixedCouplingPoisson.Transfer
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Euclidean determinant distance on the real projective line

`Vector2` is a function type, whose default norm must not be used here: that
norm is the supremum norm. The explicit square root of the sum of the two
coordinate squares below is the Euclidean norm used by the manuscript.
-/

namespace FixedCouplingPoisson

open Matrix

/-- The genuine Euclidean squared norm, explicitly in coordinates. -/
def euclideanNormSq (u : Vector2) : ℝ := (u 0) ^ 2 + (u 1) ^ 2

/-- The genuine Euclidean norm, rather than the function type's supremum norm. -/
noncomputable def euclideanNorm (u : Vector2) : ℝ := Real.sqrt (euclideanNormSq u)

/-- Determinant distance on nonzero vector representatives. -/
noncomputable def determinantDistance (u v : Vector2) : ℝ :=
  |wedge u v| / (euclideanNorm u * euclideanNorm v)

@[simp] theorem euclideanNormSq_nonneg (u : Vector2) : 0 ≤ euclideanNormSq u :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem euclideanNormSq_eq_zero_iff (u : Vector2) : euclideanNormSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h0 : u 0 = 0 := by
      have hs : (u 0) ^ 2 = 0 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h |>.1
      exact sq_eq_zero_iff.mp hs
    have h1 : u 1 = 0 := by
      have hs : (u 1) ^ 2 = 0 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h |>.2
      exact sq_eq_zero_iff.mp hs
    ext i
    fin_cases i <;> simp [h0, h1]
  · intro h; simp [euclideanNormSq, h]

theorem euclideanNormSq_pos (u : Vector2) (hu : u ≠ 0) : 0 < euclideanNormSq u :=
  lt_of_le_of_ne (euclideanNormSq_nonneg u) (Ne.symm ((euclideanNormSq_eq_zero_iff u).not.mpr hu))

@[simp] theorem euclideanNorm_nonneg (u : Vector2) : 0 ≤ euclideanNorm u := Real.sqrt_nonneg _

theorem euclideanNorm_pos (u : Vector2) (hu : u ≠ 0) : 0 < euclideanNorm u :=
  Real.sqrt_pos.mpr (euclideanNormSq_pos u hu)

@[simp] theorem euclideanNorm_sq (u : Vector2) : euclideanNorm u ^ 2 = euclideanNormSq u :=
  Real.sq_sqrt (euclideanNormSq_nonneg u)

@[simp] theorem euclideanNormSq_smul (a : ℝ) (u : Vector2) :
    euclideanNormSq (a • u) = a ^ 2 * euclideanNormSq u := by
  simp only [euclideanNormSq, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem euclideanNorm_smul (a : ℝ) (u : Vector2) :
    euclideanNorm (a • u) = |a| * euclideanNorm u := by
  simp only [euclideanNorm, euclideanNormSq_smul, Real.sqrt_mul (sq_nonneg a),
    Real.sqrt_sq_eq_abs]

/-- Covariance of the two-column determinant under every real 2×2 matrix. -/
theorem wedge_mulVec (A : Matrix2) (u v : Vector2) :
    wedge (A *ᵥ u) (A *ᵥ v) = A.det * wedge u v := by
  simp [wedge, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

@[simp] theorem wedge_smul_left (a : ℝ) (u v : Vector2) :
    wedge (a • u) v = a * wedge u v := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem wedge_smul_right (a : ℝ) (u v : Vector2) :
    wedge u (a • v) = a * wedge u v := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem wedge_self (u : Vector2) : wedge u u = 0 := by unfold wedge; ring

/-- The perpendicular vector detects the Euclidean squared norm via a wedge. -/
theorem wedge_perpendicular (u : Vector2) :
    wedge u (![-u 1, u 0] : Vector2) = euclideanNormSq u := by
  simp [wedge, euclideanNormSq]
  ring

/-- A matrix of determinant one never sends a nonzero vector to zero. -/
theorem sl2_mulVec_ne_zero (A : Matrix2) (hA : A.det = 1) (u : Vector2) (hu : u ≠ 0) :
    A *ᵥ u ≠ 0 := by
  intro hzero
  have h := wedge_mulVec A u (![-u 1, u 0] : Vector2)
  rw [hzero, hA, one_mul, wedge_perpendicular] at h
  have hs : euclideanNormSq u = 0 := by simpa [wedge] using h.symm
  exact hu ((euclideanNormSq_eq_zero_iff u).mp hs)

/-- Rescaling either nonzero representative leaves the distance unchanged. -/
theorem determinantDistance_smul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (u v : Vector2) :
    determinantDistance (a • u) (b • v) = determinantDistance u v := by
  simp only [determinantDistance, wedge_smul_left, wedge_smul_right, abs_mul,
    euclideanNorm_smul]
  have ha' : |a| ≠ 0 := abs_ne_zero.mpr ha
  have hb' : |b| ≠ 0 := abs_ne_zero.mpr hb
  calc
    |b| * (|a| * |wedge u v|) /
        (|a| * euclideanNorm u * (|b| * euclideanNorm v)) =
        (|a| * |b|) * |wedge u v| /
          ((|a| * |b|) * (euclideanNorm u * euclideanNorm v)) := by ring
    _ = |wedge u v| / (euclideanNorm u * euclideanNorm v) :=
      mul_div_mul_left _ _ (mul_ne_zero ha' hb')

/-- The undivided SL₂ identity for Euclidean unit representatives. -/
theorem sl2_determinantDistance (A : Matrix2) (hA : A.det = 1) (u v : Vector2)
    (hu : euclideanNorm u = 1) (hv : euclideanNorm v = 1) :
    determinantDistance (A *ᵥ u) (A *ᵥ v) =
      determinantDistance u v / (euclideanNorm (A *ᵥ u) * euclideanNorm (A *ᵥ v)) := by
  simp only [determinantDistance, wedge_mulVec, hA, one_mul, hu, hv, one_mul, div_one]

/-- Distinct representative lines have strictly positive determinant distance. -/
theorem determinantDistance_pos (u v : Vector2) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : wedge u v ≠ 0) : 0 < determinantDistance u v :=
  div_pos (abs_pos.mpr h) (mul_pos (euclideanNorm_pos u hu) (euclideanNorm_pos v hv))

/-- The ratio form stated in the manuscript, with all nonzero-division
conditions explicit. -/
theorem sl2_determinantDistance_ratio (A : Matrix2) (hA : A.det = 1) (u v : Vector2)
    (hu : euclideanNorm u = 1) (hv : euclideanNorm v = 1) (hw : wedge u v ≠ 0) :
    determinantDistance (A *ᵥ u) (A *ᵥ v) / determinantDistance u v =
      1 / (euclideanNorm (A *ᵥ u) * euclideanNorm (A *ᵥ v)) := by
  have hd : determinantDistance u v ≠ 0 := by
    simp [determinantDistance, hu, hv, hw]
  rw [sl2_determinantDistance A hA u v hu hv]
  rw [div_div_cancel_left' hd, one_div]

abbrev ProjectivePoint := Projectivization ℝ Vector2

/-- A genuine function on mathlib's real projective line. -/
noncomputable def projectiveDistance (p q : ProjectivePoint) : ℝ :=
  determinantDistance p.rep q.rep

/-- The representative definition descends to projective classes because of
proved scalar invariance. -/
theorem projectiveDistance_mk (u v : Vector2) (hu : u ≠ 0) (hv : v ≠ 0) :
    projectiveDistance (Projectivization.mk ℝ u hu) (Projectivization.mk ℝ v hv) =
      determinantDistance u v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ u hu
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  unfold projectiveDistance
  rw [← ha, ← hb]
  simpa only [Units.smul_def] using
    determinantDistance_smul (a : ℝ) (b : ℝ) (Units.ne_zero a) (Units.ne_zero b) u v

/-- Zero wedge is exactly equality of the represented real projective points. -/
theorem wedge_eq_zero_iff_projective_eq (u v : Vector2) (hu : u ≠ 0) (hv : v ≠ 0) :
    wedge u v = 0 ↔ Projectivization.mk ℝ u hu = Projectivization.mk ℝ v hv := by
  constructor
  · intro h
    apply Eq.symm
    apply (Projectivization.mk_eq_mk_iff' ℝ v u hv hu).mpr
    by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := by
        intro hz
        apply hu
        ext i
        fin_cases i <;> simp [h0, hz]
      have hv0 : v 0 = 0 := by
        have hh : u 1 * v 0 = 0 := by simpa [wedge, h0] using h
        exact (mul_eq_zero.mp hh).resolve_left h1
      refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, h0, hv0, h1]
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul, h0]
      · change (v 0 / u 0) * u 1 = v 1
        have hcross : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp h
        field_simp [h0]
        simpa [mul_comm] using hcross.symm
  · intro h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ u v hu hv).mp h
    rw [← ha, wedge_smul_left, wedge_self, mul_zero]

/-- The representative distance vanishes precisely on a single line. -/
theorem determinantDistance_eq_zero_iff (u v : Vector2) (hu : u ≠ 0) (hv : v ≠ 0) :
    determinantDistance u v = 0 ↔ wedge u v = 0 := by
  have hnu : euclideanNorm u ≠ 0 := ne_of_gt (euclideanNorm_pos u hu)
  have hnv : euclideanNorm v ≠ 0 := ne_of_gt (euclideanNorm_pos v hv)
  simp [determinantDistance, div_eq_zero_iff, hnu, hnv]

/-- The actual projective function separates points. -/
theorem projectiveDistance_eq_zero_iff (p q : ProjectivePoint) :
    projectiveDistance p q = 0 ↔ p = q := by
  unfold projectiveDistance
  rw [determinantDistance_eq_zero_iff _ _ p.rep_nonzero q.rep_nonzero,
    wedge_eq_zero_iff_projective_eq _ _ p.rep_nonzero q.rep_nonzero,
    Projectivization.mk_rep, Projectivization.mk_rep]

/-- The explicit shear is injective on the underlying vector space. -/
theorem shear_mulVec_injective (t : ℝ) :
    Function.Injective (fun u : Vector2 => shear t *ᵥ u) := by
  intro u v h
  have hh := congrArg (fun w => shear (-t) *ᵥ w) h
  simpa only [Matrix.mulVec_mulVec, shear_mul, neg_add_cancel, shear_zero,
    Matrix.one_mulVec] using hh

theorem shear_mulVec_ne_zero (t : ℝ) (u : Vector2) (hu : u ≠ 0) : shear t *ᵥ u ≠ 0 := by
  intro h
  apply hu
  apply shear_mulVec_injective t
  simpa using h

/-- The actual projective action of the explicit shear matrix. -/
noncomputable def shearProjective (t : ℝ) : ProjectivePoint → ProjectivePoint :=
  Projectivization.map (shear t).mulVecLin (shear_mulVec_injective t)

theorem shearProjective_mk (t : ℝ) (u : Vector2) (hu : u ≠ 0) :
    shearProjective t (Projectivization.mk ℝ u hu) =
      Projectivization.mk ℝ (shear t *ᵥ u) (shear_mulVec_ne_zero t u hu) := rfl

/-- The point reached by the nth shear power. -/
noncomputable def shearOrbitPoint (t : ℝ) (u : Vector2) (hu : u ≠ 0) (n : ℕ) : ProjectivePoint :=
  Projectivization.mk ℝ (shear ((n : ℝ) * t) *ᵥ u)
    (shear_mulVec_ne_zero ((n : ℝ) * t) u hu)

@[simp] theorem shearOrbitPoint_zero (t : ℝ) (u : Vector2) (hu : u ≠ 0) :
    shearOrbitPoint t u hu 0 = Projectivization.mk ℝ u hu := by
  simp [shearOrbitPoint]

theorem shearOrbitPoint_succ (t : ℝ) (u : Vector2) (hu : u ≠ 0) (n : ℕ) :
    shearProjective t (shearOrbitPoint t u hu n) = shearOrbitPoint t u hu (n + 1) := by
  rw [shearOrbitPoint, shearProjective_mk, shearOrbitPoint]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simp only [one_smul, Matrix.mulVec_mulVec, shear_mul]
  congr 2
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- A nonhorizontal point has an infinite shear orbit, now in mathlib's
actual projective space rather than only at the level of vector algebra. -/
theorem shearOrbitPoint_injective (t : ℝ) (ht : t ≠ 0) (u : Vector2) (hu : u ≠ 0)
    (hu1 : u 1 ≠ 0) : Function.Injective (shearOrbitPoint t u hu) := by
  intro m n h
  by_contra hmn
  have hm : shear t ^ m *ᵥ u ≠ 0 := by
    rw [shear_pow]
    exact shear_mulVec_ne_zero _ u hu
  have hn : shear t ^ n *ᵥ u ≠ 0 := by
    rw [shear_pow]
    exact shear_mulVec_ne_zero _ u hu
  have hw : wedge (shear t ^ m *ᵥ u) (shear t ^ n *ᵥ u) = 0 := by
    apply (wedge_eq_zero_iff_projective_eq _ _ hm hn).mpr
    simpa only [shear_pow, shearOrbitPoint] using h
  exact shear_iterates_not_collinear t ht u hu1 m n hmn hw

/-- Every point of a finite shear-invariant set lies on the horizontal axis. -/
theorem finite_shear_invariant_rep_second_zero (t : ℝ) (ht : t ≠ 0)
    (S : Set ProjectivePoint) (hS : S.Finite)
    (hInv : ∀ p ∈ S, shearProjective t p ∈ S) (p : ProjectivePoint) (hp : p ∈ S) :
    p.rep 1 = 0 := by
  by_contra hp1
  let orbit := shearOrbitPoint t p.rep p.rep_nonzero
  have horbit : ∀ n : ℕ, orbit n ∈ S := by
    intro n
    induction n with
    | zero => simpa [orbit] using hp
    | succ n ih =>
      rw [show orbit (n + 1) = shearProjective t (orbit n) from
        (shearOrbitPoint_succ t p.rep p.rep_nonzero n).symm]
      exact hInv _ ih
  have hfinite : (Set.range orbit).Finite := hS.subset (by
    rintro q ⟨n, rfl⟩
    exact horbit n)
  exact Set.infinite_range_of_injective (shearOrbitPoint_injective t ht p.rep
    p.rep_nonzero hp1) hfinite

theorem horizontalVector_ne_zero : (![1, 0] : Vector2) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- The horizontal projective point singled out by a nontrivial shear. -/
noncomputable def horizontalProjective : ProjectivePoint :=
  Projectivization.mk ℝ (![1, 0] : Vector2) horizontalVector_ne_zero

theorem projective_eq_horizontal_of_rep_second_zero (p : ProjectivePoint)
    (hp : p.rep 1 = 0) : p = horizontalProjective := by
  calc
    p = Projectivization.mk ℝ p.rep p.rep_nonzero := (Projectivization.mk_rep p).symm
    _ = horizontalProjective := by
      apply (wedge_eq_zero_iff_projective_eq _ _ p.rep_nonzero horizontalVector_ne_zero).mp
      simp [wedge, hp]

/-- The explicit transfer matrix is injective, using its proved inverse. -/
theorem transfer_mulVec_injective (E a : ℝ) :
    Function.Injective (fun u : Vector2 => transfer E a *ᵥ u) := by
  intro u v h
  have hh := congrArg (fun w => transferInv E a *ᵥ w) h
  simpa only [Matrix.mulVec_mulVec, transferInv_mul_transfer, Matrix.one_mulVec] using hh

/-- The actual one-step forward action on the real projective line. -/
noncomputable def transferProjective (E a : ℝ) : ProjectivePoint → ProjectivePoint :=
  Projectivization.map (transfer E a).mulVecLin (transfer_mulVec_injective E a)

theorem transferProjective_mk (E a : ℝ) (u : Vector2) (hu : u ≠ 0) :
    transferProjective E a (Projectivization.mk ℝ u hu) =
      Projectivization.mk ℝ (transfer E a *ᵥ u)
        (sl2_mulVec_ne_zero (transfer E a) (transfer_det E a) u hu) := rfl

/-- A nontrivial shear and one Schrödinger transfer matrix admit no nonempty
finite invariant set. This proves the explicit finite-set contradiction. -/
theorem no_finite_invariant_set_shear_transfer (E a t : ℝ) (ht : t ≠ 0)
    (S : Set ProjectivePoint) (hS : S.Finite) (hne : S.Nonempty)
    (hShear : ∀ p ∈ S, shearProjective t p ∈ S)
    (hTransfer : ∀ p ∈ S, transferProjective E a p ∈ S) : False := by
  have hhorizontal : ∀ p ∈ S, p = horizontalProjective := by
    intro p hp
    exact projective_eq_horizontal_of_rep_second_zero p
      (finite_shear_invariant_rep_second_zero t ht S hS hShear p hp)
  obtain ⟨p, hp⟩ := hne
  have hh : horizontalProjective ∈ S := by simpa [hhorizontal p hp] using hp
  have hfix := hhorizontal _ (hTransfer _ hh)
  have hw : wedge (![1, 0] : Vector2) (transfer E a *ᵥ ![1, 0]) = 0 := by
    apply (wedge_eq_zero_iff_projective_eq _ _ horizontalVector_ne_zero
      (sl2_mulVec_ne_zero (transfer E a) (transfer_det E a) _ horizontalVector_ne_zero)).mpr
    simpa only [horizontalProjective, transferProjective_mk] using hfix.symm
  rw [transfer_horizontal_not_collinear] at hw
  exact one_ne_zero hw

/-- Injectivity also holds on the actual projective line. -/
theorem transferProjective_injective (E a : ℝ) : Function.Injective (transferProjective E a) :=
  Projectivization.map_injective (transfer E a).mulVecLin (transfer_mulVec_injective E a)

/-- The explicit inverse matrix is injective on vectors. -/
theorem transferInv_mulVec_injective (E a : ℝ) :
    Function.Injective (fun u : Vector2 => transferInv E a *ᵥ u) := by
  intro u v h
  have hh := congrArg (fun w => transfer E a *ᵥ w) h
  simpa only [Matrix.mulVec_mulVec, transfer_mul_transferInv, Matrix.one_mulVec] using hh

theorem transferInv_mulVec_ne_zero (E a : ℝ) (u : Vector2) (hu : u ≠ 0) :
    transferInv E a *ᵥ u ≠ 0 := by
  intro h
  apply hu
  apply transferInv_mulVec_injective E a
  simpa using h

/-- The inverse one-step projective action; no time reversal is involved. -/
noncomputable def transferInverseProjective (E a : ℝ) : ProjectivePoint → ProjectivePoint :=
  Projectivization.map (transferInv E a).mulVecLin (transferInv_mulVec_injective E a)

theorem transferInverseProjective_mk (E a : ℝ) (u : Vector2) (hu : u ≠ 0) :
    transferInverseProjective E a (Projectivization.mk ℝ u hu) =
      Projectivization.mk ℝ (transferInv E a *ᵥ u) (transferInv_mulVec_ne_zero E a u hu) := rfl

theorem transferInverseProjective_transfer (E a : ℝ) (p : ProjectivePoint) :
    transferInverseProjective E a (transferProjective E a p) = p := by
  rw [← Projectivization.mk_rep p, transferProjective_mk, transferInverseProjective_mk]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simp only [one_smul, Matrix.mulVec_mulVec, transferInv_mul_transfer, Matrix.one_mulVec]

/-- The support-generated shear identity holds on the projective space itself. -/
theorem transferProjective_inverse_eq_shear (E a b : ℝ) (p : ProjectivePoint) :
    transferProjective E a (transferInverseProjective E b p) = shearProjective (b - a) p := by
  rw [← Projectivization.mk_rep p, transferInverseProjective_mk, transferProjective_mk,
    shearProjective_mk]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simp only [one_smul, Matrix.mulVec_mulVec, transfer_mul_inverse_eq_shear]

/-- Two distinct potential values already rule out every finite nonempty
forward-invariant projective set. Finite-set bijectivity supplies the inverse
step, and the actual shear orbit contradiction proves strong irreducibility. -/
theorem no_finite_invariant_set_two_transfers (E a b : ℝ) (hab : a ≠ b)
    (S : Set ProjectivePoint) (hS : S.Finite) (hne : S.Nonempty)
    (hForwardA : ∀ p ∈ S, transferProjective E a p ∈ S)
    (hForwardB : ∀ p ∈ S, transferProjective E b p ∈ S) : False := by
  have hSurj : Set.SurjOn (transferProjective E b) S S :=
    ((hS.injOn_iff_bijOn_of_mapsTo hForwardB).mp
      (transferProjective_injective E b).injOn).surjOn
  have hInverseB : ∀ p ∈ S, transferInverseProjective E b p ∈ S := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := hSurj hp
    rw [← hqp, transferInverseProjective_transfer]
    exact hq
  apply no_finite_invariant_set_shear_transfer E a (b - a) (sub_ne_zero.mpr hab.symm)
    S hS hne _ hForwardA
  intro p hp
  rw [← transferProjective_inverse_eq_shear E a b p]
  exact hForwardA _ (hInverseB p hp)

end FixedCouplingPoisson
