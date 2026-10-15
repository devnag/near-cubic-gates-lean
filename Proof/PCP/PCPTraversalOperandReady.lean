import Proof.PCP.PCPTraversalResumeRight

/-! Physical copies/constant prints used by both internal pair sites. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_copy_path (j k : Fin 39) (slot : Fin 3 → Fin 128)
    (hi : Function.Injective slot) (hp : call j=focused slot PCPFieldMoves.readyMachine)
    (hn : ∀ q scanned,next j q scanned=some k)
    (bits : List Bool) (cap : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 2*bits.length+1≤cap)
    (ht : ∀ i,ambient (slot i)=
      (![ZeroPadding.pad cap (frame bits),List.replicate cap false,List.replicate cap false] : Fin 3 → List Bool) i)
    (hh : ∀ i,heads (slot i)=0) :
    Path j k (4*bits.length+5) heads ambient heads (install slot ambient (resultLocal cap bits)) := by
  obtain ⟨r,hr,hrh,hrt,_⟩ := (padded_field_ready bits cap hc).focus_at slot hi heads ambient ht hh
  exact packed_path j k (focused slot PCPFieldMoves.readyMachine) hp (4*bits.length+4)
    heads ambient _ ⟨r,hr,hrh,hrt⟩ hn

theorem WorkBound.fieldCopied {cap : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (slot : Fin 3 → Fin 128) (bits : List Bool)
    (hc : 2*bits.length+1≤cap) :
    WorkBound cap (RecoveryRootRound.install slot ambient (resultLocal cap bits)) := by
  apply hb.install slot
  intro i _ _
  fin_cases i
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl hc
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl hc
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

theorem literal_print_path (j k : Fin 39) (slot : Fin 2 → Fin 128)
    (hi : Function.Injective slot) (bits : List Bool)
    (hp : call j=focused slot (HierarchyFixedWord.machine bits))
    (hn : ∀ q scanned,next j q scanned=some k)
    (cap : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : bits.length≤cap) (ht : ∀ i,ambient (slot i)=List.replicate cap false)
    (hh : ∀ i,heads (slot i)=0) :
    Path j k (2*bits.length+3) heads ambient heads
      (install slot ambient ![ZeroPadding.pad cap bits,List.replicate cap false]) := by
  obtain ⟨r,hr,hrh,hrt,_⟩ := (padded_printer_ready bits cap hc).focus_at slot hi heads ambient ht hh
  exact packed_path j k (focused slot (HierarchyFixedWord.machine bits)) hp (2*bits.length+2)
    heads ambient _ ⟨r,hr,hrh,hrt⟩ hn

end NearCubicWires.RepairOrdinary.PCPTraversal
