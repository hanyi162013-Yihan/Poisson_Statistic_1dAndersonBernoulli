import FixedCouplingPoisson.CompactSubsemigroupGroup
import FixedCouplingPoisson.Transfer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Real

/-! Actual two-value Schrödinger generators cannot lie in a compact
submonoid of SL₂(ℝ). Draft: compilation is deferred. -/
noncomputable section
namespace FixedCouplingPoisson
open Matrix Set

abbrev RealSL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

def schrodingerTransferSL2 (E v : ℝ) : RealSL2 :=
  ⟨transfer E v, transfer_det E v⟩

def upperShearSL2 (t : ℝ) : RealSL2 :=
  ⟨shear t, by simp [shear, Matrix.det_fin_two]⟩

@[simp] theorem schrodingerTransferSL2_coe (E v : ℝ) :
    (schrodingerTransferSL2 E v : Matrix2) = transfer E v := rfl

@[simp] theorem upperShearSL2_coe (t : ℝ) :
    (upperShearSL2 t : Matrix2) = shear t := rfl

theorem schrodingerTransferSL2_inv_coe (E v : ℝ) :
    ((schrodingerTransferSL2 E v)⁻¹ : RealSL2).val = transferInv E v := by
  have hmul : transfer E v * ((schrodingerTransferSL2 E v)⁻¹ : RealSL2).val = 1 := by
    simpa only [SpecialLinearGroup.coe_mul, schrodingerTransferSL2_coe,
      SpecialLinearGroup.coe_one] using congrArg
        (fun A : RealSL2 => (A : Matrix2)) (mul_inv_cancel (schrodingerTransferSL2 E v))
  calc
    _ = (transferInv E v * transfer E v) *
        ((schrodingerTransferSL2 E v)⁻¹ : RealSL2).val := by simp
    _ = transferInv E v * (transfer E v *
        ((schrodingerTransferSL2 E v)⁻¹ : RealSL2).val) := mul_assoc _ _ _
    _ = transferInv E v := by rw [hmul, mul_one]

theorem schrodingerTransferSL2_mul_inv (E a b : ℝ) :
    schrodingerTransferSL2 E a * (schrodingerTransferSL2 E b)⁻¹ =
      upperShearSL2 (b - a) := by
  apply Subtype.ext
  change transfer E a * ((schrodingerTransferSL2 E b)⁻¹ : RealSL2).val = shear (b - a)
  rw [schrodingerTransferSL2_inv_coe, transfer_mul_inverse_eq_shear]

/-- This is a statement about the actual two matrices, with no assumed
random-product conclusion or noncompactness interface. -/
theorem no_compact_submonoid_two_schrodinger_transfers (E a b : ℝ) (hab : a ≠ b)
    (S : Submonoid RealSL2) (hS : IsCompact (S : Set RealSL2))
    (ha : schrodingerTransferSL2 E a ∈ S) (hb : schrodingerTransferSL2 E b ∈ S) :
    False := by
  have hshear : upperShearSL2 (b - a) ∈ S := by
    rw [← schrodingerTransferSL2_mul_inv E a b]
    exact S.mul_mem ha (inverse_mem_of_compact_submonoid S hS hb)
  have hcont : Continuous (fun A : RealSL2 => |A 0 1|) := by
    exact ((continuous_apply (1 : Fin 2)).comp
      (SpecialLinearGroup.continuous_apply id continuous_id (0 : Fin 2))).abs
  obtain ⟨B, hB⟩ := (hS.image hcont).bddAbove
  obtain ⟨n, hn⟩ := shear_powers_entry_unbounded (b - a) (sub_ne_zero.mpr hab.symm) B
  have hle : |(shear (b - a) ^ n) 0 1| ≤ B := by
    exact hB ⟨upperShearSL2 (b - a) ^ n, S.pow_mem hshear n, rfl⟩
  exact (not_lt_of_ge hle) hn

theorem not_isCompact_generated_schrodinger_submonoid (E a b : ℝ) (hab : a ≠ b) :
    ¬IsCompact (closure
      (Submonoid.closure {schrodingerTransferSL2 E a, schrodingerTransferSL2 E b} : Set RealSL2)) := by
  intro hcompact
  let S := (Submonoid.closure
    {schrodingerTransferSL2 E a, schrodingerTransferSL2 E b}).topologicalClosure
  apply no_compact_submonoid_two_schrodinger_transfers E a b hab S hcompact
  · apply Submonoid.le_topologicalClosure
    exact Submonoid.subset_closure (by simp)
  · apply Submonoid.le_topologicalClosure
    exact Submonoid.subset_closure (by simp)

end FixedCouplingPoisson
