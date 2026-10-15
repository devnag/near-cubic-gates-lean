import Proof.CaseAnalysis.RecoverySearchBudget

/-! The literal CNF payload and raw description length drive the complete
case decision and canonical search. Every other local tape starts empty. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def requestSlots (i : Fin 12) : Fin 790:=i.castAdd 778
def searchSlots (i : Fin 778) : Fin 790:=
  ⟨if i.val=0 then 10 else 12+i.val,by have hi:=i.isLt;split_ifs <;> omega⟩
theorem request_injective : Function.Injective requestSlots:=by
  intro a b h;exact Fin.ext (congrArg (fun i : Fin 790=>i.val) h)
theorem search_injective : Function.Injective searchSlots:=by
  intro a b h
  apply Fin.ext
  have hv:=congrArg (fun i : Fin 790=>i.val) h
  dsimp only [searchSlots] at hv
  split_ifs at hv <;> omega
def ports : Ports 790:=⟨by decide,787,by decide,356,by decide⟩
noncomputable def request:=RecoveryFocus.machine requestSlots RecoveryBoundedSearchRequest.machine
noncomputable def pieces (C : Nat) : Fin 2→Piece 790
  | 0=>ordinary request
  | 1=>focused (RecoveryBoundedSearch.program C) searchSlots
def next (C : Nat) (j : Fin 2) (_ : Fin (pieces C j).states)
    (_ : Fin 790→Bool) : Option (Fin 2):=if j=0 then some 1 else none
noncomputable abbrev program (C : Nat):=ports.program (graph (pieces C) 0 (next C))
def input (payload total B : Nat) (i : Fin 790) : List Bool:=
  if i.val=0 then RepairOrdinary.frame payload.bits else if i.val=1 then ZeroPadding.pad B (List.replicate total true) else []

theorem ready (C payload total B : Nat) (hC : 1073741824 ≤ C) :
    ∃ cost ≤ RecoveryBoundedSearch.fullBudget C payload total,∃ out : Fin 790→List Bool,
      Ready correctedSat (program C) cost (input payload total B) out ∧
      readTapeBit (out 369) 0=correctedSat (RecoveryQuery.code true payload 0 0) ∧
      out 787=frame (RecoveryPrefixBody.search true payload total []) ∧
      out 1=ZeroPadding.pad B (List.replicate total true) := by
  classical
  obtain ⟨requestOut,hr,hrequest,harity⟩:=RecoveryBoundedSearchRequest.ready payload total B
  have hlocal:=hr.focus requestSlots request_injective (input payload total B) (by
    intro i
    simp only [input,requestSlots,Fin.val_castAdd,RecoveryBoundedSearchRequest.input,
      show (i=0 ↔ i.val=0) from Fin.ext_iff,show (i=1 ↔ i.val=1) from Fin.ext_iff]
    rfl)
  obtain ⟨c0,hc0,h0⟩:=RecoveryPrefixCold.ordinary_ready (o:=correctedSat) ports request _ _ hlocal
  let middle:=install requestSlots (input payload total B) requestOut
  have searchInput : ∀ i : Fin 778,middle (searchSlots i)=RecoveryBoundedSearch.input payload total i := by
    intro i
    by_cases hz : i.val=0
    · have he : i=0:=Fin.ext hz
      subst i
      change install requestSlots (input payload total B) requestOut (requestSlots 10)=_
      rw [install_slot _ request_injective]
      exact hrequest
    · change install requestSlots (input payload total B) requestOut (searchSlots i)=_
      rw [install_other requestSlots _ _ _ (by
        intro j he
        have hv:=congrArg (fun k : Fin 790=>k.val) he
        have hj:=j.isLt
        change j.val=(if i.val=0 then 10 else 12+i.val) at hv
        rw [if_neg hz] at hv
        omega)]
      simp [input,searchSlots,RecoveryBoundedSearch.input,hz,show 12+i.val≠1 by omega]
  obtain ⟨c1,hc1,searchOut,hs,hflag,hdescription⟩:=RecoveryBoundedSearch.ready C payload total hC
  have h1:=hs.focus ports searchSlots search_injective rfl middle searchInput
  have hp0:=Ready.call ports (pieces C) 0 (next C) 0 1 h0 (by intro q;rfl)
  have hp1:=Ready.stop ports (pieces C) 0 (next C) 1 h1 (by intro q;rfl)
  have whole:=trans hp0 hp1
  have start : controlConfig (RecoveryCalls.code (fun j=>(pieces C j).states) 0)
      (initialConfiguration (pieces C 0).machine (input payload total B))=
      initialConfiguration (program C).base.machine (input payload total B) := rfl
  rw [start] at whole
  refine ⟨(c0+1)+(c1+1),?_,install searchSlots middle searchOut,?_,?_,?_,?_⟩
  · dsimp only [RecoveryBoundedSearch.fullBudget]
    omega
  · refine ⟨_,whole,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · change readTapeBit (install searchSlots middle searchOut (searchSlots 357)) 0=_
    rw [install_slot _ search_injective]
    exact hflag
  · change install searchSlots middle searchOut (searchSlots 775)=_
    rw [install_slot _ search_injective]
    exact hdescription
  · rw [install_other searchSlots _ _ (1 : Fin 790) (by
      intro j he
      have hv:=congrArg (fun i : Fin 790=>i.val) he
      change (if j.val=0 then 10 else 12+j.val)=1 at hv
      split_ifs at hv <;> omega)]
    exact (install_slot requestSlots request_injective _ _ 1).trans harity

end NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
