import Proof.CaseAnalysis.RowsOriginalSwitch
import Proof.Rows.CycleHeadMove

/-! A fixed finite dispatch tree reads its branch bits from tape. Every bit
read, cursor advance and branch return is charged to the ordinary machine. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkBinaryDispatch
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.CloseoutWitness

def states (s : Nat) : Nat→Nat
  | 0=>s
  | n+1=>Fintype.card (RecoveryCalls.Control (HeaderSwitch.sizes 1 (2+states s n) (2+states s n)))

def advance {t : Nat} (port : Fin t):=CycleHeadMove.machine (fun i=>if i=port then .right else .stay)
def advanced {t : Nat} (port : Fin t) (H : Fin t→Nat) (n : Nat):=
  Function.update H port (H port+n)

noncomputable def machine {t s : Nat} (p : List Bool→Machine t s) (port : Fin t) :
    (n : Nat)→List Bool→Machine t (states s n)
  | 0,pre=>p pre
  | n+1,pre=>CloseoutRowsOriginalSwitch.machine
      (Composition.machine (advance port) (machine p port n (pre++[true])))
      (Composition.machine (advance port) (machine p port n (pre++[false]))) port

theorem advance_run {t : Nat} (port : Fin t) (H : Fin t→Nat) (A : Fin t→List Bool) :
    Step (advance port) 1 H A (advanced port H 1) A := by
  apply (CycleHeadMove.run _ H A).congr ?_ rfl
  funext i
  by_cases hi:i=port
  · subst i;simp [advanced,HeadMove.apply]
  · simp [advanced,hi,HeadMove.apply]

theorem advanced_zero {t : Nat} (port : Fin t) (H : Fin t→Nat) : advanced port H 0=H := by
  funext i;by_cases hi:i=port <;>simp [advanced,hi]

theorem advanced_add {t : Nat} (port : Fin t) (H : Fin t→Nat) (a b : Nat) :
    advanced port (advanced port H a) b=advanced port H (a+b) := by
  funext i;by_cases hi:i=port <;>simp [advanced,hi,Nat.add_assoc]

theorem run {t s fuel : Nat} (p : List Bool→Machine t s) (port : Fin t)
    (bits codePrefix pre tail : List Bool) (H G : Fin t→Nat) (A B : Fin t→List Bool)
    (ha : A port=pre++bits++tail) (hh : H port=pre.length)
    (worker : Step (p (codePrefix++bits)) fuel (advanced port H bits.length) A G B) :
    Step (machine p port bits.length codePrefix) (fuel+4*bits.length) H A G B := by
  induction bits generalizing codePrefix pre H with
  | nil=>simpa only [List.append_nil,List.length_nil,Nat.mul_zero,Nat.add_zero,machine,states,advanced_zero] using worker
  | cons b bits ih=>
    have hb:readTapeBit (A port) (H port)=b:=by
      rw [ha,hh]
      simpa only [List.cons_append,List.append_assoc] using Streaming.read_append pre (bits++tail) b
    have htail:Step (p ((codePrefix++[b])++bits)) fuel
        (advanced port (advanced port H 1) bits.length) A G B := by
      rw [advanced_add]
      simpa only [List.singleton_append,List.append_assoc,List.length_cons,Nat.add_comm] using worker
    have stepTail:=ih (codePrefix++[b]) (pre++[b]) (advanced port H 1)
      (by simpa only [List.singleton_append,List.append_assoc,List.cons_append,List.nil_append] using ha)
      (by simp [advanced,hh]) htail
    have branch:Step (Composition.machine (advance port)
        (machine p port bits.length (codePrefix++[b]))) (fuel+4*bits.length+2) H A G B := by
      have h:=(advance_run port H A).seq stepTail
      convert h using 1;omega
    cases b with
    | false=>
      have h:=CloseoutRowsOriginalSwitch.false_run
        (Composition.machine (advance port) (machine p port bits.length (codePrefix++[true]))) _ port branch hb
      simpa [machine,states,Nat.mul_add,Nat.add_assoc] using h
    | true=>
      have h:=CloseoutRowsOriginalSwitch.true_run _
        (Composition.machine (advance port) (machine p port bits.length (codePrefix++[false]))) port branch hb
      simpa [machine,states,Nat.mul_add,Nat.add_assoc] using h

end Theorem25Completion.WalkBinaryDispatch
