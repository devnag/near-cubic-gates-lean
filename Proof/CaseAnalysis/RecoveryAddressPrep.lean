import Proof.CaseAnalysis.RecoveryAddressReset

/-! Save the actual constant output, advance its graph counter, and restore
the same shared first-field index and value0 before the address expression. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressPrep
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryChildSelection
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 4→Fin 10:=![4,9,7,8]
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def handoff:=TapeEmbedding.machine 1 RecoveryBoundedSelectorHandoff.machine
noncomputable def machine:=Composition.machine clear handoff
def data (acc index C : ℕ) (flag : Bool) : Fin 10→List Bool:=
  ![List.replicate acc true,List.replicate C false,List.replicate index true,
    List.replicate C false,ZeroPadding.pad C (List.replicate index true),ZeroPadding.pad C [true],
    List.replicate C false,List.replicate C true,List.replicate (C+1) false,ZeroPadding.pad C [flag]]
def middle (acc index C : ℕ) : Fin 10→List Bool:=
  Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedSelectorHandoff.data acc 0 index 1 C 0) (fun _=>List.replicate C false)
def output (acc index C : ℕ) : Fin 10→List Bool:=
  Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedSelectorHandoff.data acc 0 index 1 C 5) (fun _=>List.replicate C false)

theorem clear_ready (acc index C : ℕ) (flag : Bool) (hi : index ≤ C) (hC : 1 ≤ C) :
    ReadyRun clear (2*C+4) (data acc index C flag) (middle acc index C) := by
  let backing : Fin 2→List Bool:=![ZeroPadding.pad C (List.replicate index true),ZeroPadding.pad C [flag]]
  have hb : ∀ j,(backing j).length ≤ C := by
    intro j
    fin_cases j
    · change (ZeroPadding.pad C (List.replicate index true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      omega
    · change (ZeroPadding.pad C [flag]).length ≤ C
      rw [ZeroPadding.pad_length,List.length_singleton]
      omega
  have h:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus clearSlots (by decide)
    (data acc index C flag) (by intro j;fin_cases j <;> rfl)
  have he : install clearSlots (data acc index C flag)
      (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=middle acc index C := by
    apply HierarchyWidth.install_eq clearSlots (by decide)
    · intro j;fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  rw [he] at h
  exact h

theorem handoff_ready (acc index C : ℕ) (ha : acc+1 ≤ C) (hi : index+1 ≤ C) :
    ReadyRun handoff (2*C+4*acc+4*index+24) (middle acc index C) (output acc index C) := by
  have h:=RecoveryBoundedSelectorHandoff.handoff_ready acc 0 index 1 C ha (by omega) hi (by omega)
  exact h.embed (fun _ : Fin 1=>List.replicate C false)

theorem prepare_ready (acc index C : ℕ) (flag : Bool) (ha : acc+1 ≤ C) (hi : index+1 ≤ C) :
    ReadyRun machine (4*C+4*acc+4*index+29) (data acc index C flag) (output acc index C) := by
  have h:=HierarchyMultiplyEntry.join_exact clear handoff _ _ _ _ _
    (clear_ready acc index C flag (by omega) (by omega)) (handoff_ready acc index C ha hi)
  have he : (2*C+4)+1+(2*C+4*acc+4*index+24)=4*C+4*acc+4*index+29 := by omega
  simpa only [machine,he] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressPrep
