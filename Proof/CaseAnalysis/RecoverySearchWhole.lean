import Proof.CaseAnalysis.RecoverySearchCase
import Proof.CaseAnalysis.RecoverySearchTail

/-! One framed request drives the original case query and the original
total canonical-prefix search. Both branches pay the same complete run. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearch
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caseSlots (i : Fin 389) : Fin 778 := i.castAdd 389
theorem case_injective : Function.Injective caseSlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 778=>i.val) h)
def ports := RecoveryBoundedSearchTail.ports
noncomputable def pieces (C : Nat) : Fin 2→Piece 778
  | 0 => focused (RecoveryBoundedSearchCase.coldProgram C) caseSlots
  | 1 => RecoveryBoundedSearchTail.piece C
def next (C : Nat) (j : Fin 2) (_ : Fin (pieces C j).states)
    (_ : Fin 778→Bool) : Option (Fin 2) := if j=0 then some 1 else none
noncomputable abbrev program (C : Nat) := ports.program (graph (pieces C) 0 (next C))
def input (payload total : Nat) (i : Fin 778) : List Bool :=
  if i.val=0 then frame (RecoveryPrefixMeasure.request payload total) else []
def budget (C payload total : Nat) := RecoveryBoundedSearchCase.coldBudget C payload total+
  RecoveryPrefixCold.budget C payload total+2

theorem ready (C payload total : Nat) (hC : 1073741824 ≤ C) :
    ∃ cost ≤ budget C payload total,∃ out : Fin 778→List Bool,
      Ready correctedSat (program C) cost (input payload total) out ∧
      readTapeBit (out 357) 0=correctedSat (RecoveryQuery.code true payload 0 0) ∧
      out 775=frame (RecoveryPrefixBody.search true payload total []) := by
  classical
  obtain ⟨c0,hc0,caseOut,hcase,flag,request,query⟩:=
    RecoveryBoundedSearchCase.cold_ready C payload total hC
  have h0:=hcase.focus ports caseSlots case_injective rfl (input payload total) (fun _=>rfl)
  let middle:=install caseSlots (input payload total) caseOut
  have hm0 : middle 0=frame (RecoveryPrefixMeasure.request payload total) :=
    (install_slot caseSlots case_injective _ _ 0).trans request
  have hmq : middle 344=List.replicate (RecoveryPrefixColdPrepare.capacity C payload total) false :=
    (install_slot caseSlots case_injective _ _ 344).trans query
  have hmf : middle 357=caseOut 357 := install_slot caseSlots case_injective _ _ 357
  have fresh : ∀ i : Fin 389,i.val≠0 → i.val≠344 → middle (RecoveryBoundedSearchTail.slots i)=[] := by
    intro i hz hq
    change install caseSlots (input payload total) caseOut (RecoveryBoundedSearchTail.slots i)=[]
    rw [install_other caseSlots _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 778=>k.val) he
      have hj:=j.isLt
      dsimp [caseSlots,RecoveryBoundedSearchTail.slots] at hv
      rw [if_neg hz,if_neg hq] at hv
      omega)]
    have hi : (RecoveryBoundedSearchTail.slots i).val≠0 := by
      dsimp [RecoveryBoundedSearchTail.slots]
      rw [if_neg hz,if_neg hq]
      omega
    exact if_neg hi
  obtain ⟨c1,hc1,out,h1,description,keep⟩:=RecoveryBoundedSearchTail.ready C payload total
    (RecoveryPrefixColdPrepare.capacity C payload total) hC middle hm0 hmq fresh
  have hp0:=Ready.call ports (pieces C) 0 (next C) 0 1 h0 (by intro q;rfl)
  have hp1:=Ready.stop ports (pieces C) 0 (next C) 1 h1 (by intro q;rfl)
  have whole:=trans hp0 hp1
  have start : controlConfig (RecoveryCalls.code (fun j=>(pieces C j).states) 0)
      (initialConfiguration (pieces C 0).machine (input payload total))=
      initialConfiguration (program C).base.machine (input payload total) := rfl
  rw [start] at whole
  refine ⟨(c0+1)+(c1+1),?_,out,?_,?_,description⟩
  · dsimp only [budget]
    omega
  · refine ⟨_,whole,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · rw [keep,hmf]
    exact flag

end NearCubicWires.RepairSource.RecoveryBoundedSearch
