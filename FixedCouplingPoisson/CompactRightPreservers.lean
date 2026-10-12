import FixedCouplingPoisson.CompactSubsemigroupGroup
import Mathlib.Topology.Homeomorph.Lemmas

/-! Right multiplication preserving a nonempty compact set gives a compact
submonoid of the actual ambient topological group. Compilation is deferred. -/
noncomputable section
namespace FixedCouplingPoisson
open Set

section Group
variable {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]
    [IsTopologicalGroup G]

/-- All right multipliers preserving a set. -/
def rightPreserverSubmonoid (K : Set G) : Submonoid G where
  carrier := {g | ∀ a ∈ K, a * g ∈ K}
  one_mem' := by
    intro a ha
    simpa only [mul_one] using ha
  mul_mem' := by
    intro g h hg hh a ha
    rw [← mul_assoc]
    exact hh _ (hg _ ha)

@[simp] theorem mem_rightPreserverSubmonoid (K : Set G) (g : G) :
    g ∈ rightPreserverSubmonoid K ↔ ∀ a ∈ K, a * g ∈ K := Iff.rfl

theorem isClosed_rightPreserverSubmonoid {K : Set G} (hK : IsClosed K) :
    IsClosed (rightPreserverSubmonoid K : Set G) := by
  have heq : (rightPreserverSubmonoid K : Set G) =
      ⋂ a : K, {g : G | (a : G) * g ∈ K} := by
    ext g
    simp only [mem_rightPreserverSubmonoid, mem_iInter, mem_setOf_eq]
    constructor
    · intro hg a
      exact hg a a.property
    · intro hg a ha
      exact hg ⟨a, ha⟩
  rw [heq]
  exact isClosed_iInter fun a =>
    hK.preimage (continuous_const.mul continuous_id)

/-- Fixing one point of the preserved compact set bounds every multiplier;
the preservation property is closed, so the whole submonoid is compact. -/
theorem isCompact_rightPreserverSubmonoid {K : Set G}
    (hK : IsCompact K) (hne : K.Nonempty) :
    IsCompact (rightPreserverSubmonoid K : Set G) := by
  obtain ⟨a, ha⟩ := hne
  have hcompact : IsCompact ((fun g : G => a * g) ⁻¹' K) :=
    (Homeomorph.mulLeft a).isCompact_preimage.mpr hK
  apply hcompact.of_isClosed_subset (isClosed_rightPreserverSubmonoid hK.isClosed)
  intro g hg
  exact hg a ha

end Group
end FixedCouplingPoisson
