import Proof.Amplification.RecoveryRowStructureChildrenCounts

/-! Fixed ordinary call graph for a paired structural row: second unpair,
left key copy and lookup, left-count save, right key copy and lookup, then
the retained count relation. Missing either child physically rejects. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def childStates {t s : Nat} (_ : Machine t s) : Nat := s
noncomputable def childrenSizes : Fin 8→Nat :=
  ![childStates (onBase decodeMachine),6,childStates bankMachine,6,6,childStates bankMachine,
    childStates childrenCountMachine,2]
noncomputable def childrenPrograms : (j : Fin 8)→Machine 68 (childrenSizes j)
  | ⟨0,_⟩=>onBase decodeMachine
  | ⟨1,_⟩=>keyCopyMachine true
  | ⟨2,_⟩=>bankMachine
  | ⟨3,_⟩=>saveCountMachine
  | ⟨4,_⟩=>keyCopyMachine false
  | ⟨5,_⟩=>bankMachine
  | ⟨6,_⟩=>childrenCountMachine
  | ⟨7,_⟩=>onBase (validMachine false)
  | ⟨n+8,h⟩=>False.elim (by omega)
def childrenNext (j : Fin 8) (_ : Fin (childrenSizes j)) (scanned : Fin 68→Bool) : Option (Fin 8) :=
  if j.val=0 then some 1 else if j.val=1 then some 2 else
  if j.val=2 then if scanned 61 then some 3 else some 7 else
  if j.val=3 then some 4 else if j.val=4 then some 5 else
  if j.val=5 then if scanned 61 then some 6 else some 7 else none
noncomputable def childrenMachine := RecoveryCalls.machine childrenSizes childrenPrograms 0 childrenNext
noncomputable def childrenCfg (x : Children) (j : Fin 8) :=
  x.cfg (RecoveryCalls.code childrenSizes j (childrenPrograms j).start)
noncomputable def childrenStop (x : Children) := RecoveryCalls.stopped childrenSizes x.heads x.tapes

theorem children_call (j l : Fin 8) (x out : Children) (fuel : Nat)
    (r : ExecutionReceipt 68 (childrenSizes j))
    (hr : runFrom (childrenPrograms j) fuel (x.cfg (childrenPrograms j).start)=some r)
    (hf : r.final=out.cfg r.final.control)
    (hn : childrenNext j r.final.control r.final.scanned=some l) :
    ∃ n≤fuel+1,Timed childrenMachine n (childrenCfg x j) (childrenCfg out l) := by
  obtain ⟨n,hb,h⟩ := call_receipt childrenSizes childrenPrograms 0 childrenNext j l fuel _ r hr hn
  rw [hf] at h
  exact ⟨n,hb,h⟩

theorem children_stop (j : Fin 8) (x out : Children) (fuel : Nat)
    (r : ExecutionReceipt 68 (childrenSizes j))
    (hr : runFrom (childrenPrograms j) fuel (x.cfg (childrenPrograms j).start)=some r)
    (hf : r.final=out.cfg r.final.control)
    (hn : childrenNext j r.final.control r.final.scanned=none) :
    ∃ n≤fuel+1,Timed childrenMachine n (childrenCfg x j) (childrenStop out) := by
  obtain ⟨n,hb,h⟩ := stop_receipt childrenSizes childrenPrograms 0 childrenNext j fuel _ r hr hn
  rw [hf] at h
  exact ⟨n,hb,h⟩

def childrenRejected (x : Children) : Children := {x with base:=setValid x.base false}

theorem children_reject_tail (x : Children) :
    ∃ n≤2,Timed childrenMachine n (childrenCfg x 7) (childrenStop (childrenRejected x)) := by
  obtain ⟨base,hr0,hf0,_⟩ := valid_run x.base x.copyCapacity false
  obtain ⟨r,hr,hf,_⟩ := base_run (validMachine false) x (setValid x.base false) 1 base hr0 (by rw [hf0]; rfl)
  exact children_stop 7 x (childrenRejected x) 1 r hr hf (by rfl)

theorem children_count_tail (x : Children) (word bits : List Bool) (hx : x.Valid word bits)
    (hp : x.base.count.length=x.base.state.bits.length) (hl : x.base.code.length=x.base.state.bits.length) :
    ∃ n≤4*x.base.count.length+5,Timed childrenMachine n (childrenCfg x 6) (childrenStop (childrenCounted x)) := by
  obtain ⟨r,hr,hf,_,_⟩ := children_count_run x word bits hx hp hl
  exact children_stop 6 x (childrenCounted x) (4*x.base.count.length+4) r hr hf (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
