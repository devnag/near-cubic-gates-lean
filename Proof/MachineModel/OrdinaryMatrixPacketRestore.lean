import Proof.MachineModel.OrdinaryMatrixPacketRequestCopy
import Proof.MachineModel.OrdinaryMatrixPacketWorkClear

/-! One physical erase and original-request restoration. The exact final
array is exposed for the following reusable packet call. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketRestore
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) (E : ℕ) := MatrixPacketWorkClear.tapes a E+2
noncomputable def copySlots (a : WilliamsAlgorithm) (E : ℕ) : Fin 4 → Fin (tapes a E) :=
  ![(MatrixPacketWorkClear.original a E).castAdd 2,
    (MatrixPacketWorkClear.work a E ⟨0,by unfold MatrixPacketWorkClear.count; omega⟩).castAdd 2,
    (0 : Fin 2).natAdd (MatrixPacketWorkClear.tapes a E),(1 : Fin 2).natAdd (MatrixPacketWorkClear.tapes a E)]

theorem copySlots_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (copySlots a E) := by
  have hw:=MatrixPacketWorkClear.work_bound a E ⟨0,by unfold MatrixPacketWorkClear.count; omega⟩
  have hv (j : Fin 4) : (copySlots a E j).val=(![MatrixPacketCapacityNative.tapes a E+1,0,
      MatrixPacketWorkClear.tapes a E,MatrixPacketWorkClear.tapes a E+1] : Fin 4 → ℕ) j := by
    fin_cases j <;> rfl
  intro i j he
  have eq := congrArg Fin.val he
  rw [hv,hv] at eq
  unfold MatrixPacketWorkClear.tapes MatrixPacketCapacityNative.tapes at eq
  fin_cases i <;> fin_cases j <;> norm_num at eq <;> rfl

theorem source_outside (a : WilliamsAlgorithm) (E : ℕ) :
    ∀ j,MatrixPacketWorkClear.slots a E j≠MatrixPacketWorkClear.original a E := by
  intro j hj
  rw [MatrixPacketWorkClear.slots_cases] at hj
  split_ifs at hj
  · have h:=MatrixPacketWorkClear.work_bound a E ⟨j.val,by assumption⟩
    have hv:=congrArg Fin.val hj
    change (MatrixPacketWorkClear.work a E ⟨j.val,by assumption⟩).val=MatrixPacketCapacityNative.tapes a E+1 at hv
    unfold MatrixPacketCapacityNative.tapes at hv
    omega
  · have h:=(MatrixPacketCapacityNative.outputTape a E).isLt
    have hv:=congrArg Fin.val hj
    change (MatrixPacketCapacityNative.outputTape a E).val=MatrixPacketCapacityNative.tapes a E+1 at hv
    omega
  · have hv:=congrArg Fin.val hj
    change MatrixPacketCapacityNative.tapes a E=MatrixPacketCapacityNative.tapes a E+1 at hv
    omega

def extras (left right : ℕ) : Fin 2 → List Bool := ![List.replicate left false,List.replicate right false]
noncomputable def first (a : WilliamsAlgorithm) (E : ℕ) := TapeEmbedding.machine 2 (MatrixPacketWorkClear.machine a E)
noncomputable def last (a : WilliamsAlgorithm) (E : ℕ) := RecoveryFocus.machine (copySlots a E) RecoveryRootRound.copyMachine
noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) := Composition.machine (first a E) (last a E)
def budget (bits : List Bool) (cap : ℕ) := (2*cap+4)+1+(8*bits.length+8)
noncomputable def input (a : WilliamsAlgorithm) (E left right : ℕ)
    (heads : Fin (MatrixPacketWorkClear.tapes a E) → ℕ) (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool) :=
  Composition.leftConfig 6 (TapeEmbedding.config (fun _ : Fin 2 => 0) (extras left right)
    (RecoveryCalls.restarted (MatrixPacketWorkClear.machine a E) heads ambient))
noncomputable def cleared (a : WilliamsAlgorithm) (E cap log : ℕ) (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool) :=
  install (MatrixPacketWorkClear.slots a E) ambient
    (MatrixPacketWorkClear.eraseData cap (max log (cap+1)) (fun _ : Fin (MatrixPacketWorkClear.count a) => List.replicate cap false))
noncomputable def output (a : WilliamsAlgorithm) (E cap log left right : ℕ) (bits : List Bool)
    (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool) :=
  install (copySlots a E) (Fin.addCases (motive := fun _ => List Bool) (cleared a E cap log ambient) (extras left right))
    (MatrixPacketRequestCopy.output bits cap left right)

theorem restore_run (a : WilliamsAlgorithm) (E cap log left right : ℕ) (bits : List Bool)
    (heads : Fin (MatrixPacketWorkClear.tapes a E) → ℕ) (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool)
    (hd : ambient (MatrixPacketWorkClear.capTape a E)=List.replicate cap true)
    (hl : ambient (MatrixPacketWorkClear.logTape a E)=List.replicate log false)
    (hb : ∀ j,(ambient (MatrixPacketWorkClear.work a E j)).length≤cap)
    (hh : ∀ j,heads (MatrixPacketWorkClear.slots a E j)=0)
    (hs : ambient (MatrixPacketWorkClear.original a E)=frame bits)
    (hsh : heads (MatrixPacketWorkClear.original a E)=0) : ∃ actual,
    runFrom (machine a E) (budget bits cap) (input a E left right heads ambient)=some actual ∧
    actual.final.tapes=output a E cap log left right bits ambient ∧
    actual.final.heads=Fin.addCases heads (fun _ : Fin 2 => 0) ∧ actual.steps=budget bits cap := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := MatrixPacketWorkClear.clear_run a E cap log heads ambient hd hl hb hh
  have he := TapeEmbedding.run_embed (MatrixPacketWorkClear.machine a E) (fun _ : Fin 2 => 0)
    (extras left right) _ _ base hbase
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extras left right) base
  have sourceT : base.final.tapes (MatrixPacketWorkClear.original a E)=frame bits := by
    rw [bt]
    exact (install_other _ _ _ _ (source_outside a E)).trans hs
  have destT : base.final.tapes (MatrixPacketWorkClear.work a E ⟨0,by unfold MatrixPacketWorkClear.count; omega⟩)=List.replicate cap false := by
    have h:=install_slot (MatrixPacketWorkClear.slots a E) (MatrixPacketWorkClear.slots_injective a E) ambient
      (MatrixPacketWorkClear.eraseData cap (max log (cap+1)) (fun _ : Fin (MatrixPacketWorkClear.count a) => List.replicate cap false))
      (((⟨0,by unfold MatrixPacketWorkClear.count; omega⟩ : Fin (MatrixPacketWorkClear.count a)).castAdd 1).castAdd 1)
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_left] at h
    exact (congrFun bt _).trans h
  have destH : heads (MatrixPacketWorkClear.work a E ⟨0,by unfold MatrixPacketWorkClear.count; omega⟩)=0 := by
    have h:=hh (((⟨0,by unfold MatrixPacketWorkClear.count; omega⟩ : Fin (MatrixPacketWorkClear.count a)).castAdd 1).castAdd 1)
    simpa only [MatrixPacketWorkClear.slots,Fin.addCases_left] using h
  have oldT (i : Fin (MatrixPacketWorkClear.tapes a E)) : prepared.final.tapes (i.castAdd 2)=base.final.tapes i := by
    change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
      base.final.tapes (extras left right)) (i.castAdd 2)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin (MatrixPacketWorkClear.tapes a E)) : prepared.final.heads (i.castAdd 2)=heads i := by
    change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd 2)=_
    rw [Fin.addCases_left,bh]
  have freshT (i : Fin 2) : prepared.final.tapes (i.natAdd (MatrixPacketWorkClear.tapes a E))=extras left right i := by
    change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
      base.final.tapes (extras left right)) (i.natAdd (MatrixPacketWorkClear.tapes a E))=_
    rw [Fin.addCases_right]
  have freshH (i : Fin 2) : prepared.final.heads (i.natAdd (MatrixPacketWorkClear.tapes a E))=0 := by
    change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.natAdd (MatrixPacketWorkClear.tapes a E))=_
    rw [Fin.addCases_right]
  have hc := MatrixPacketRequestCopy.copy_ready bits cap left right
  obtain ⟨copied,hcopy,copyH,copyT,copyS⟩ := HierarchyBinary.focused_run (copySlots a E) (copySlots_injective a E)
    _ _ _ hc prepared.final.heads prepared.final.tapes
    (by intro j; fin_cases j
        · exact (oldH _).trans hsh
        · exact (oldH _).trans destH
        · exact freshH 0
        · exact freshH 1)
    (by intro j; fin_cases j
        · exact (oldT _).trans sourceT
        · exact (oldT _).trans destT
        · exact freshT 0
        · exact freshT 1)
  change runFrom (last a E) (8*bits.length+8)
    (Composition.restart prepared.final (last a E).start)=some copied at hcopy
  have joined := Composition.run_join (first a E) (last a E) _ _ _ prepared copied he hcopy
  refine ⟨Composition.joinedReceipt prepared copied,joined,?_,?_,?_⟩
  · change copied.final.tapes=output a E cap log left right bits ambient
    rw [copyT]
    unfold output
    congr 1
    change Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
      base.final.tapes (extras left right)=
      Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
        (cleared a E cap log ambient) (extras left right)
    rw [bt]
    rfl
  · change copied.final.heads=Fin.addCases heads (fun _ : Fin 2 => 0)
    rw [copyH]
    change Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => ℕ)
      base.final.heads (fun _ : Fin 2 => 0)=_
    rw [bh]
  · change base.steps+1+copied.steps=budget bits cap
    rw [bs,copyS]
    rfl

end NearCubicWires.RepairOrdinary.MatrixPacketRestore
