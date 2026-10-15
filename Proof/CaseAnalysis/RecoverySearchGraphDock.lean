import Proof.CaseAnalysis.RecoverySearchFocus

/-! The completed search aliases the actual graph payload and arity, with
fresh private work. Every other graph/source tape and cursor is retained. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchGraphDock
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
open RecoveryBoundedSearchExecution RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (u : Nat) (i : Fin 790) : Fin (1664+u+790):=
  ⟨if i.val=0 then 1657 else if i.val=1 then 144 else 1664+u+i.val,
    by have hi:=i.isLt;split_ifs <;> omega⟩
def old (u : Nat) (i : Fin (1664+u)) : Fin (1664+u+790):=i.castAdd 790
def payloadPort (u : Nat) : Fin (1664+u):=(1657 : Fin 1664).castAdd u
def arityPort (u : Nat) : Fin (1664+u):=(144 : Fin 1664).castAdd u
def ports (u : Nat) : Ports (1664+u+790):=
  ⟨by omega,(787 : Fin 790).natAdd (1664+u),by simp,
    (356 : Fin 790).natAdd (1664+u),by simp⟩
noncomputable abbrev program (u : Nat):=(ports u).program
  (focused (RecoveryBoundedSearchExecution.program 1073741824) (slots u))

theorem injective (u : Nat) : Function.Injective (slots u):=by
  intro a b h
  apply Fin.ext
  have hv:=congrArg (fun i : Fin (1664+u+790)=>i.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> omega

theorem fresh_slot (u : Nat) (i : Fin 790) (h0 : i.val≠0) (h1 : i.val≠1) :
    slots u i=i.natAdd (1664+u):=by
  apply Fin.ext
  simp [slots,h0,h1,Nat.add_comm]

theorem run (u payload total B : Nat) (H : Fin (1664+u)→Nat) (A : Fin (1664+u)→List Bool)
    (hp : A (payloadPort u)=frame payload.bits)
    (ha : A (arityPort u)=ZeroPadding.pad B (List.replicate total true))
    (hhp : H (payloadPort u)=0) (hha : H (arityPort u)=0) :
    ∃ cost ≤ 1099511627776*(RecoveryPrefixCold.radius payload total)^3,∃ final,
      OrdinaryOracleTrace correctedSat (program u) cost
        ⟨(program u).base.machine.start,
          Fin.addCases (m:=1664+u) (n:=790) H (fun _=>0),
          Fin.addCases (m:=1664+u) (n:=790) A (fun _=>[])⟩ final ∧
      (program u).base.machine.halted final.control=true ∧
      final.heads=Fin.addCases (m:=1664+u) (n:=790) H (fun _=>0) ∧
      readTapeBit (final.tapes ((369 : Fin 790).natAdd (1664+u))) 0=
        correctedSat (RecoveryQuery.code true payload 0 0) ∧
      final.tapes ((787 : Fin 790).natAdd (1664+u))=
        frame (RecoveryPrefixBody.search true payload total []) ∧
      (∀ i : Fin (1664+u),i≠payloadPort u → i≠arityPort u →
        final.tapes (old u i)=A i) := by
  classical
  obtain ⟨cost,hcost,out,hr,hflag,hdesc,_⟩:=RecoveryBoundedSearchExecution.ready 1073741824
    payload total B (Nat.le_refl _)
  have hpj : ∀ i : Fin 790,
      (Fin.addCases (m:=1664+u) (n:=790) (motive:=fun _=>List Bool) A (fun _=>[])) (slots u i)=
        RecoveryBoundedSearchExecution.input payload total B i := by
    intro i
    by_cases hz : i.val=0
    · have he : i=0:=Fin.ext hz
      subst i
      rw [show slots u 0=(payloadPort u).castAdd 790 from rfl,Fin.addCases_left]
      exact hp
    · by_cases ho : i.val=1
      · have he : i=1:=Fin.ext ho
        subst i
        rw [show slots u 1=(arityPort u).castAdd 790 from rfl,Fin.addCases_left]
        exact ha
      · rw [fresh_slot u i hz ho,Fin.addCases_right]
        simp [RecoveryBoundedSearchExecution.input,hz,ho]
  have hpheads : ∀ i : Fin 790,
      (Fin.addCases (m:=1664+u) (n:=790) (motive:=fun _=>Nat) H (fun _=>0)) (slots u i)=0 := by
    intro i
    by_cases hz : i.val=0
    · have he : i=0:=Fin.ext hz
      subst i
      rw [show slots u 0=(payloadPort u).castAdd 790 from rfl,Fin.addCases_left]
      exact hhp
    · by_cases ho : i.val=1
      · have he : i=1:=Fin.ext ho
        subst i
        rw [show slots u 1=(arityPort u).castAdd 790 from rfl,Fin.addCases_left]
        exact hha
      · rw [fresh_slot u i hz ho,Fin.addCases_right]
  obtain ⟨final,trace,halt,heads,tapes⟩:=focus_ready hr (ports u) (slots u) (injective u) rfl
    (Fin.addCases (m:=1664+u) (n:=790) H (fun _=>0))
    (Fin.addCases (m:=1664+u) (n:=790) A (fun _=>[])) hpheads hpj
  refine ⟨cost,hcost.trans (RecoveryBoundedSearch.full_budget_bound payload total),final,
    trace,halt,heads,?_,?_,?_⟩
  · rw [tapes]
    change readTapeBit (install (slots u) _ out (slots u 369)) 0=_
    rw [install_slot _ (injective u)]
    exact hflag
  · rw [tapes]
    change install (slots u) _ out (slots u 787)=_
    rw [install_slot _ (injective u)]
    exact hdesc
  · intro i hi hj
    rw [tapes,install_other (slots u) _ _ (old u i) (by
      intro j he
      have hv:=congrArg (fun z : Fin (1664+u+790)=>z.val) he
      have hil:=i.isLt
      change (if j.val=0 then 1657 else if j.val=1 then 144 else 1664+u+j.val)=i.val at hv
      split_ifs at hv
      · exact hi (Fin.ext hv.symm)
      · exact hj (Fin.ext hv.symm)
      · omega)]
    exact Fin.addCases_left i

end NearCubicWires.RepairSource.RecoveryBoundedSearchGraphDock
