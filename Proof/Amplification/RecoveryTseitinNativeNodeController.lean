import Proof.Amplification.RecoveryTseitinNativeKernelBank
import Proof.Amplification.RecoveryTseitinNativeNodeRun
import Proof.PCP.PCPPNativeTag

/-! One fixed finite controller dispatches the actual native node tag and
constant value to the original six Tseitin clause plans. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagSlots (value : Bool) : Fin 1→Fin 1335 := fun _=>if value then 1082 else 1072
noncomputable def tagProgram (value : Bool) := RecoveryFocus.machine (tagSlots value) PCPPNativeTag.machine
noncomputable def nodeProgram (k : Fin 6) := RecoveryFocus.machine (kernelSlots (decide (k=2)))
  (RecoveryTseitinNode.machine (RecoveryTseitinNode.plans k))
private def stateCount {s : Nat} (_ : Machine 1335 s) := s
noncomputable def sizes : Fin 8→Nat := ![10,10,stateCount (nodeProgram 0),stateCount (nodeProgram 1),
  stateCount (nodeProgram 2),stateCount (nodeProgram 3),stateCount (nodeProgram 4),stateCount (nodeProgram 5)]
noncomputable def programs : (j : Fin 8)→Machine 1335 (sizes j)
  | ⟨0,_⟩=>tagProgram false
  | ⟨1,_⟩=>tagProgram true
  | ⟨2,_⟩=>nodeProgram 0
  | ⟨3,_⟩=>nodeProgram 1
  | ⟨4,_⟩=>nodeProgram 2
  | ⟨5,_⟩=>nodeProgram 3
  | ⟨6,_⟩=>nodeProgram 4
  | ⟨7,_⟩=>nodeProgram 5
  | ⟨j+8,hj⟩=>False.elim (by omega)
def next (j : Fin 8) (q : Fin (sizes j)) (_ : Fin 1335→Bool) : Option (Fin 8) :=
  if j=0 then
    if q.val=5 then some 1 else if q.val=6 then some 4 else if q.val=7 then some 5
    else if q.val=8 then some 6 else if q.val=9 then some 7 else none
  else if j=1 then if q.val=5 then some 2 else if q.val=6 then some 3 else none
  else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (j : Fin 8) (head : Fin 1335→Nat) (data : Fin 1335→List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (RecoveryCalls.restarted (programs j) head data)

theorem parsed_next (tag : Fin 5) (q : Fin (sizes 0)) (bits : Fin 1335→Bool)
    (hq : q.val=tag.val+5) : next 0 q bits=some (![1,4,5,6,7] tag) := by
  fin_cases tag <;> simp [next,hq]
theorem const_next (b : Bool) (q : Fin (sizes 1)) (bits : Fin 1335→Bool)
    (hq : q.val=b.toNat+5) : next 1 q bits=some (if b then 3 else 2) := by
  cases b <;> simp [next,hq]

theorem call_run (j l : Fin 8) (fuel : Nat) (head : Fin 1335→Nat) (data : Fin 1335→List Bool)
    (r : ExecutionReceipt 1335 (sizes j))
    (hr : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) head data)=some r)
    (hn : next j r.final.control r.final.scanned=some l) :
    Timed machine (r.steps+1) (boundary j head data) (boundary l r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩:=prefix_of_run (programs j) fuel _ r hr
  have body:=RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have ret:=RecoveryCalls.return_step sizes programs 0 next j l r.final hh hn
  exact body.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret)

theorem stop_run (j : Fin 8) (fuel : Nat) (head : Fin 1335→Nat) (data : Fin 1335→List Bool)
    (r : ExecutionReceipt 1335 (sizes j))
    (hr : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) head data)=some r)
    (hn : next j r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (boundary j head data) (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩:=prefix_of_run (programs j) fuel _ r hr
  have body:=RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have ret:=RecoveryCalls.stop_step sizes programs 0 next j r.final hh hn
  exact body.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret)

end NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
