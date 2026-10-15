import Proof.CaseAnalysis.HierarchyClockInput
import Proof.Amplification.RecoveryCaseOneEntryPair

/-! The genuine refuter answer produces the original hierarchy request.
Direct use of the checked two-field builder avoids constructing and parsing
the four-field external Case1 wrapper inside the common recovery program. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyRequest
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (k : Nat):=CloseoutHierarchyClock.Input.tapes (k+2)+4
def old (k : Nat) (i : Fin (CloseoutHierarchyClock.Input.tapes (k+2))) : Fin (tapes k):=i.castAdd 4
def fresh (k : Nat) (i : Fin 4) : Fin (tapes k):=i.natAdd (CloseoutHierarchyClock.Input.tapes (k+2))
def slots (k : Nat) : Fin 6→Fin (tapes k):=
  ![old k (CloseoutHierarchyClock.Input.old (k+2) (HierarchyFromInput.field (k+2) 2)),old k (CloseoutHierarchyClock.Input.fresh (k+2) 1),
    fresh k 0,fresh k 1,fresh k 2,fresh k 3]
def input (k : Nat) (bits : List Bool) : Fin (tapes k)→List Bool:=
  Fin.addCases (CloseoutHierarchyClock.Input.input (k+2) bits) (fun _ : Fin 4=>[])
theorem old_injective (k : Nat) : Function.Injective (old k):=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes k)=>i.val) h)
theorem old_fresh (k : Nat) (i : Fin (CloseoutHierarchyClock.Input.tapes (k+2))) (j : Fin 4) : old k i≠fresh k j:=by
  intro h
  have hv:=congrArg Fin.val h
  have hi:=i.isLt
  change i.val=CloseoutHierarchyClock.Input.tapes (k+2)+j.val at hv
  omega
theorem slots_injective (k : Nat) : Function.Injective (slots k):=by
  intro a b h
  have hv:=congrArg Fin.val h
  have hl:=HierarchyFromInput.tapes_lower (k+2)
  fin_cases a <;> fin_cases b <;>
    simp [slots,old,fresh,CloseoutHierarchyClock.Input.old,CloseoutHierarchyClock.Input.fresh,CloseoutHierarchyClock.Input.tapes,HierarchyFromInput.field] at hv ⊢ <;> omega

def first (k C : Nat):=RecoveryFocus.machine (old k) (CloseoutHierarchyClock.Input.machine (k+2) C (by omega))
def last (k : Nat):=RecoveryFocus.machine (slots k) RecoveryCaseOneEntryPair.machine
def machine (k C : Nat):=Composition.machine (first k C) (last k)
def budget (k C : Nat) (bits : List Bool):=
  CloseoutHierarchyClock.Input.budget (k+2) C bits+1+RecoveryCaseOneEntryPair.budget bits (C*(bits.length^(k+2)+1)).bits

theorem request_run {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (bits : List Bool) :
    ∃ out,ClockJoin.ReadyRun (machine k H.coefficient) (budget k H.coefficient bits)
      (input k bits) out ∧ out (fresh k 0)=frame bits++frame (H.time bits.length).bits:=by
  obtain ⟨clock,hclock,hbits,htime⟩:=CloseoutHierarchyClock.Input.hierarchy_run H bits
  have ha:=hclock.focus (old k) (old_injective k) (input k bits) (fun i=>Fin.addCases_left i)
  let a:=install (old k) (input k bits) clock
  have af (j : Fin 4) : a (fresh k j)=[]:=
    (install_other _ _ _ _ (fun i=>old_fresh k i j)).trans (Fin.addCases_right j)
  have hin (j : Fin 6) : a (slots k j)=RecoveryCaseOneEntryPair.input bits (H.time bits.length).bits j:=by
    fin_cases j
    · change install (old k) _ _ (old k (CloseoutHierarchyClock.Input.old (k+2) (HierarchyFromInput.field (k+2) 2)))=_
      rw [install_slot _ (old_injective k)]
      exact hbits
    · change install (old k) _ _ (old k (CloseoutHierarchyClock.Input.fresh (k+2) 1))=_
      rw [install_slot _ (old_injective k)]
      exact htime
    · exact af 0
    · exact af 1
    · exact af 2
    · exact af 3
  obtain ⟨paired,hp,hword⟩:=RecoveryCaseOneEntryPair.ready bits (H.time bits.length).bits
  have hb:=hp.focus (slots k) (slots_injective k) a hin
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ ha hb,?_⟩
  change install (slots k) _ _ (slots k 2)=_
  rw [install_slot _ (slots_injective k)]
  exact hword

end
end NearCubicWires.RepairSource.CloseoutHierarchyRequest
