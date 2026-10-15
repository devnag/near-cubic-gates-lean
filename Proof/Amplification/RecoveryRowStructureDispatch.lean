import Proof.Amplification.RecoveryRowStructureChildrenSemantics

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def structureStates {t s : Nat} (_ : Machine t s) : Nat := s
noncomputable def structureSizes : Fin 4→Nat :=
  ![structureStates (onBase frontMachine),structureStates (onBase zeroMachine),
    structureStates (onBase oneMachine),structureStates childrenMachine]
noncomputable def structurePrograms : (j : Fin 4)→Machine 68 (structureSizes j)
  | ⟨0,_⟩=>onBase frontMachine
  | ⟨1,_⟩=>onBase zeroMachine
  | ⟨2,_⟩=>onBase oneMachine
  | ⟨3,_⟩=>childrenMachine
  | ⟨n+4,h⟩=>False.elim (by omega)
def structureNext (j : Fin 4) (_ : Fin (structureSizes j)) (scanned : Fin 68→Bool) : Option (Fin 4) :=
  if j.val=0 then if scanned 50 then if scanned 43 then some 1 else if scanned 44 then some 2 else some 3 else none
  else none
noncomputable def structureMachine := RecoveryCalls.machine structureSizes structurePrograms 0 structureNext
noncomputable def structureCfg (x : Children) (j : Fin 4) :=
  x.cfg (RecoveryCalls.code structureSizes j (structurePrograms j).start)
noncomputable def structureStop (x : Children) := RecoveryCalls.stopped structureSizes x.heads x.tapes

def structureFront (x : Children) : Children := {x with base:=frontOutput x.base}
def structureZero (x : Children) : Children := {structureFront x with base:=zeroOutput (frontOutput x.base)}
def structureOne (x : Children) : Children := {structureFront x with base:=oneOutput (frontOutput x.base) (pairWord x.base)}
def structureOutput (x : Children) (bits : List Bool) : Children :=
  if (frontOutput x.base).valid then
    if (frontOutput x.base).flags 0 then structureZero x
    else if (frontOutput x.base).flags 1 then structureOne x
    else childrenOutput (structureFront x) (pairWord x.base) bits
  else structureFront x

def structureTime (x : Children) := frontTime x.base+1+
  max (zeroTime (frontOutput x.base))
    (max (oneTime (frontOutput x.base) (pairWord x.base)) (childrenTime (structureFront x) (pairWord x.base)))+1

theorem withBase_valid (x : Children) (out : Data) (word bits : List Bool) (hx : x.Valid word bits)
    (hout : out.Valid word) (hb : out.state.bits=x.base.state.bits) :
    ({x with base:=out} : Children).Valid word bits := by
  refine ⟨hout,?_,hx.2.2.1,hx.2.2.2.1,?_,hx.2.2.2.2.2⟩
  · change RecoveryRowLookupTable.Inv out.state.bits.length ⟨x.bank,bits⟩
    rw [hb]
    exact hx.2.1
  · change 2*out.state.bits.length+1≤x.copyCapacity
    rw [hb]
    exact hx.2.2.2.2.1

theorem structureFront_valid (x : Children) (word bits : List Bool) (hx : x.Valid word bits)
    (hw : x.base.code.length=x.base.state.bits.length) : (structureFront x).Valid word bits :=
  withBase_valid x (frontOutput x.base) word bits hx (front_output_valid x.base word hx.1 hw) (front_retained x.base).2.2.2.1

theorem structure_call (j l : Fin 4) (x out : Children) (fuel : Nat)
    (r : ExecutionReceipt 68 (structureSizes j))
    (hr : runFrom (structurePrograms j) fuel (x.cfg (structurePrograms j).start)=some r)
    (hf : r.final=out.cfg r.final.control)
    (hn : structureNext j r.final.control r.final.scanned=some l) :
    ∃ n≤fuel+1,Timed structureMachine n (structureCfg x j) (structureCfg out l) := by
  obtain ⟨n,hb,h⟩ := call_receipt structureSizes structurePrograms 0 structureNext j l fuel _ r hr hn
  rw [hf] at h
  exact ⟨n,hb,h⟩

theorem structure_stop (j : Fin 4) (x out : Children) (fuel : Nat)
    (r : ExecutionReceipt 68 (structureSizes j))
    (hr : runFrom (structurePrograms j) fuel (x.cfg (structurePrograms j).start)=some r)
    (hf : r.final=out.cfg r.final.control)
    (hn : structureNext j r.final.control r.final.scanned=none) :
    ∃ n≤fuel+1,Timed structureMachine n (structureCfg x j) (structureStop out) := by
  obtain ⟨n,hb,h⟩ := stop_receipt structureSizes structurePrograms 0 structureNext j fuel _ r hr hn
  rw [hf] at h
  exact ⟨n,hb,h⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
