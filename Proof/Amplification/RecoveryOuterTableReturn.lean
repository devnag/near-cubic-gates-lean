import Proof.Amplification.RecoveryOuterTableReturnReusable

/-! Physical Boolean return for the complete table loop. Empty tables
explicitly write true; failed scans explicitly write false. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure RecoveryOuterLeaf
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
open RecoveryRowTable (tableCheck)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setResult (x : Cursor) (bit : Bool) : Cursor :=
  {x with data:=RecoveryOuterLeaf.setResult x.data bit}
noncomputable def tableCfg {s : Nat} (x : Cursor) (total : Nat) (q : Fin s) : Configuration 85 s :=
  ⟨q,Fin.addCases (m:=84) (n:=1) (motive:=fun _=>Nat) x.data.heads (fun _=>1),
    Fin.addCases (m:=84) (n:=1) (motive:=fun _=>List Bool) x.data.tapes (fun _=>CompareMachine.word total)⟩

theorem setResult_tapes (x : Cursor) (total : Nat) (bit : Bool) :
    (tableCfg (setResult x bit) total (0 : Fin 1)).tapes=
      Function.update (tableCfg x total (0 : Fin 1)).tapes 50 [bit] := by
  have hc := RecoveryOuterLeaf.setResult_tapes x.data bit
  change Fin.addCases (m:=84) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryOuterLeaf.setResult x.data bit).tapes (fun _=>CompareMachine.word total)=_
  rw [hc,bank_update_left]
  rfl

theorem setResult_inv (width limit : Nat) (word outerBits innerBits : List Bool)
    (innerRows : List Row) (innerRest : List Bool) (x : Cursor)
    (hx : Inv width limit word outerBits innerBits innerRows innerRest x) (bit : Bool) :
    Inv width limit word outerBits innerBits innerRows innerRest (setResult x bit) :=
  ⟨hx.ready,hx.sameWidth,hx.priorLength,hx.parsed,hx.checked,hx.leaves,hx.innerParsed,hx.innerBound,hx.source,
    hx.sourcePos,hx.bounded,hx.capacity⟩

noncomputable def phaseAnswer (q : Fin (Fintype.card (RepeatMachine.Control bodySize))) : Bool :=
  decide (q=RepeatMachine.phaseCode bodySize 3)
noncomputable def returnMachine := RecoveryOuterTableReturn.machine machine phaseAnswer
def returnBudget (width limit total : Nat) := total*(tableBudget width limit+3)+3+3

theorem phase_four_ne_three : RepeatMachine.phaseCode bodySize 4≠RepeatMachine.phaseCode bodySize 3 := by
  intro h
  have he := (RepeatMachine.code bodySize).injective h
  have hf : (4 : Fin 5)=3 := Sum.inr.inj he
  contradiction

theorem return_endpoint {s t : Nat} (before : Configuration 85 s) (after : Configuration 85 t)
    (out : Cursor) (total : Nat) (bit : Bool)
    (hb : before.heads=(tableCfg out total (0 : Fin 1)).heads)
    (hbT : before.tapes=(tableCfg out total (0 : Fin 1)).tapes) (hh : after.heads=before.heads)
    (ht : after.tapes=Function.update before.tapes 50 [bit]) :
    after=tableCfg (setResult out bit) total after.control := by
  apply configuration_ext
  · rfl
  · rw [hh,hb]; rfl
  · rw [ht,hbT]
    exact (setResult_tapes out total bit).symm

theorem table_run_boundary (width limit total : Nat) (word outerBits innerBits : List Bool)
    (innerRows : List Row) (innerRest : List Bool) (x : Cursor)
    (hx : Inv width limit word outerBits innerBits innerRows innerRest x) (hbound : x.data.outer.total+total ≤ limit) :
    ∃ r,runFrom machine (total*(tableBudget width limit+3)+3) (tableCfg x total machine.start)=some r ∧
      r.final.control=RepeatMachine.phaseCode bodySize (if tableCheck width (predicate innerRows) total x.prior x.input then 3 else 4) ∧
      r.final.heads 50=0 ∧ (∃ bit,r.final.tapes 50=[bit]) ∧
      (tableCheck width (predicate innerRows) total x.prior x.input=true → ∃ out : Cursor,
        r.final=tableCfg out total r.final.control ∧ Inv width limit word outerBits innerBits innerRows innerRest out ∧
        out.data.outer.total=x.data.outer.total+total) := by
  obtain ⟨r,hr,_,hc,hh,ht,hout⟩ := table_run width limit total word outerBits innerBits innerRows innerRest x hx hbound
  refine ⟨r,hr,hc,hh,ht,?_⟩
  intro ha
  obtain ⟨out,hf,hv,hj⟩ := hout ha
  refine ⟨out,?_,hv,hj⟩
  apply configuration_ext
  · rfl
  · rw [hf]; rfl
  · rw [hf]; rfl

theorem table_return_run (width limit total : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x) (hbound : x.data.outer.total+total ≤ limit) :
    ∃ r,runFrom returnMachine (returnBudget width limit total) (tableCfg x total returnMachine.start)=some r ∧
      r.steps ≤ returnBudget width limit total ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[tableCheck width (predicate innerRows) total x.prior x.input] ∧
      (tableCheck width (predicate innerRows) total x.prior x.input=true → ∃ out : Cursor,
        r.final=tableCfg out total r.final.control ∧ Inv width limit word outerBits innerBits innerRows innerRest out ∧
        out.data.outer.total=x.data.outer.total+total) := by
  obtain ⟨first,hr0,hphase,hh0,⟨old,ht0⟩,hout0⟩ := table_run_boundary width limit total word outerBits innerBits innerRows innerRest x hx hbound
  have hbit : phaseAnswer first.final.control=tableCheck width (predicate innerRows) total x.prior x.input := by
    unfold phaseAnswer
    rw [hphase]
    cases tableCheck width (predicate innerRows) total x.prior x.input
    · simp only [Bool.false_eq_true,if_false,phase_four_ne_three,decide_false]
    · simp only [if_true,decide_true]
  have h := RecoveryOuterTableReturn.reusable_run machine phaseAnswer
    (total*(tableBudget width limit+3)+3) _ first hr0 old
    (tableCheck width (predicate innerRows) total x.prior x.input) hh0 ht0 hbit
    (fun out : Cursor=>(tableCfg out total (0 : Fin 1)).heads)
    (fun out : Cursor=>(tableCfg out total (0 : Fin 1)).tapes)
    (fun out=>setResult out true)
    (fun out=>Inv width limit word outerBits innerBits innerRows innerRest out ∧ out.data.outer.total=x.data.outer.total+total)
    (fun _=>rfl) (fun out=>setResult_tapes out total true)
    (fun out ho=>⟨setResult_inv width limit word outerBits innerBits innerRows innerRest out ho.1 true,ho.2⟩)
    (by
      intro ha
      obtain ⟨out,hf,hv,hj⟩ := hout0 ha
      exact ⟨out,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hv,hj⟩)
  exact h

end NearCubicWires.RepairOrdinary.RecoveryOuterTable
