import Proof.Amplification.RecoveryRowTableReturnKernel

/-! Physical Boolean return for the complete table loop. Empty tables
explicitly write true; failed scans explicitly write false. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setResult (x : Cursor) (bit : Bool) : Cursor :=
  {x with data:={x.data with base:=setValid x.data.base bit}}
noncomputable def tableCfg {s : Nat} (x : Cursor) (total : Nat) (q : Fin s) : Configuration 69 s :=
  ⟨q,Fin.addCases (m:=68) (n:=1) (motive:=fun _=>Nat) x.data.heads (fun _=>1),
    Fin.addCases (m:=68) (n:=1) (motive:=fun _=>List Bool) x.data.tapes (fun _=>CompareMachine.word total)⟩

theorem setResult_tapes (x : Cursor) (total : Nat) (bit : Bool) :
    (tableCfg (setResult x bit) total (0 : Fin 1)).tapes=
      Function.update (tableCfg x total (0 : Fin 1)).tapes 50 [bit] := by
  have hc : (setResult x bit).data.tapes=Function.update x.data.tapes 50 [bit] := by
    change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
      (cfg (setValid x.data.base bit) x.data.copyCapacity (0 : Fin 1)).tapes
      (RecoveryRowLookupTable.readyTapes x.data.bank x.data.total x.data.lookupCapacity)=_
    rw [cfg_valid,bank_update_left]
    rfl
  unfold tableCfg
  rw [hc,bank_update_left]
  rfl

theorem setResult_inv (width limit : Nat) (word bits : List Bool) (P : Nat→Bool) (x : Cursor)
    (hx : Inv width limit word bits P x) (bit : Bool) : Inv width limit word bits P (setResult x bit) :=
  ⟨hx.ready,hx.sameWidth,hx.priorLength,hx.parsed,hx.checked,hx.leaves,hx.predicate,hx.source,
    hx.sourcePos,hx.bounded,hx.capacity⟩

noncomputable def phaseAnswer (q : Fin (Fintype.card (RepeatMachine.Control bodySize))) : Bool :=
  decide (q=RepeatMachine.phaseCode bodySize 3)
noncomputable def returnMachine := RecoveryRowTableReturn.machine machine phaseAnswer
def returnBudget (width limit total : Nat) := total*(tableRowBudget width limit+3)+6

theorem phase_four_ne_three : RepeatMachine.phaseCode bodySize 4≠RepeatMachine.phaseCode bodySize 3 := by
  intro h
  have he := (RepeatMachine.code bodySize).injective h
  have hf : (4 : Fin 5)=3 := Sum.inr.inj he
  contradiction

theorem table_return_run (width limit total : Nat) (word bits : List Bool) (P : Nat→Bool)
    (x : Cursor) (hx : Inv width limit word bits P x) (hbound : x.data.total+total ≤ limit) :
    ∃ r,runFrom returnMachine (returnBudget width limit total) (tableCfg x total returnMachine.start)=some r ∧
      r.steps ≤ returnBudget width limit total ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[tableCheck width P total x.prior x.input] ∧
      (tableCheck width P total x.prior x.input=true → ∃ out : Cursor,
        r.final=tableCfg out total r.final.control ∧ Inv width limit word bits P out ∧
        out.data.total=x.data.total+total) := by
  obtain ⟨first,hr0,_,hphase,hh0,⟨old,ht0⟩,hout0⟩ := table_run width limit total word bits P x hx hbound
  obtain ⟨r,hr,hb,hf⟩ := RecoveryRowTableReturn.return_run machine phaseAnswer
    (total*(tableRowBudget width limit+3)+3) _ first hr0 old hh0 ht0
  have hbit : phaseAnswer first.final.control=tableCheck width P total x.prior x.input := by
    unfold phaseAnswer
    rw [hphase]
    cases tableCheck width P total x.prior x.input
    · simp only [Bool.false_eq_true,if_false,phase_four_ne_three,decide_false]
    · simp only [if_true,decide_true]
  refine ⟨r,hr,hb,?_,?_,?_⟩
  · rw [hf]; exact hh0
  · rw [hf]
    change Function.update first.final.tapes 50 [phaseAnswer first.final.control] 50=_
    simp only [Function.update_self,hbit]
  · intro ha
    obtain ⟨out,hout,hvalid,htotal⟩ := hout0 ha
    refine ⟨setResult out true,?_,setResult_inv width limit word bits P out hvalid true,htotal⟩
    apply configuration_ext
    · rfl
    · rw [hf,hout]; rfl
    · rw [hf]
      change Function.update first.final.tapes 50 [phaseAnswer first.final.control]=_
      rw [hbit,ha]
      rw [hout]
      exact (setResult_tapes out total true).symm

end NearCubicWires.RepairOrdinary.RecoveryRowTable
