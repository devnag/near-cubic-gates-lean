import Proof.Amplification.RecoveryAssignment

/-! Explicit retained layout for reuse of the same assignment machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryValuationStream RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cfg_heads {s : Nat} (d : Data) (count cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (q : Fin s) :
    (cfg d count cap binaryCount committed guard q).heads=
      ![d.pos,0,1,0,0,0,0,0,1,1,0,0,0,0] := by
  funext i; fin_cases i <;> rfl

theorem cfg_tapes {s : Nat} (d : Data) (count cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (q : Fin s) :
    (cfg d count cap binaryCount committed guard q).tapes=
      ![d.source,d.row,CompareMachine.word (d.width+1),frame d.index,[d.found],[d.value],
        List.replicate d.capacity false,[d.valid],CompareMachine.word count,CompareMachine.word cap,
        frame binaryCount,frame committed,[guard],List.replicate d.capacity false] := by
  funext i; fin_cases i <;> rfl

def selectedData (d : Data) (out : RecoveryPrefixAssignment.Data) : Data :=
  {d with index:=out.index,found:=out.flag,value:=out.result}

noncomputable def selectorResult (out : RecoveryPrefixAssignment.Data) :=
  out.cfg (RecoveryCalls.controlCode RecoveryPrefixAssignment.sizes none)

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem selector_result_heads (d : Data) (out : RecoveryPrefixAssignment.Data) (count cap : Nat)
    (binaryCount committed : List Bool) (j : Fin 8) :
    (selectorResult out).heads j=
      (cfg (selectedData d out) count cap binaryCount committed out.guard
        (RecoveryCalls.controlCode RecoveryPrefixAssignment.sizes none)).heads (selectorSlots j) := by
  rw [cfg_heads]
  fin_cases j <;> rfl

theorem selector_result_tapes (d : Data) (out : RecoveryPrefixAssignment.Data) (count cap : Nat)
    (binaryCount committed : List Bool) (hcount : out.count=binaryCount)
    (hcommitted : out.committed=committed) (hcapacity : out.capacity=d.capacity) (j : Fin 8) :
    (selectorResult out).tapes j=
      (cfg (selectedData d out) count cap binaryCount committed out.guard
        (RecoveryCalls.controlCode RecoveryPrefixAssignment.sizes none)).tapes (selectorSlots j) := by
  rw [cfg_tapes]
  fin_cases j <;> simp [selectorResult,RecoveryPrefixAssignment.Data.cfg,selectedData,selectorSlots,hcount,hcommitted,hcapacity]

private theorem unchanged_fourteen (a b c d e f g h i j k l m n d' e' f' m' : List Bool) (x : Fin 14)
    (h3 : x≠3) (h4 : x≠4) (h5 : x≠5) (h12 : x≠12) :
    ![a,b,c,d,e,f,g,h,i,j,k,l,m,n] x=![a,b,c,d',e',f',g,h,i,j,k,l,m',n] x := by
  have he : ![a,b,c,d',e',f',g,h,i,j,k,l,m',n]=
      Function.update (Function.update (Function.update (Function.update
        ![a,b,c,d,e,f,g,h,i,j,k,l,m,n] ((0 : Fin 11).succ.succ.succ) d')
        ((0 : Fin 10).succ.succ.succ.succ) e')
        ((0 : Fin 9).succ.succ.succ.succ.succ) f')
        ((0 : Fin 2).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) m' := by
    simp only [Matrix.vecCons,← Fin.cons_update,Fin.update_cons_zero]
  rw [he]
  simp [h3,h4,h5,h12]

theorem selector_outside_tapes (d : Data) (out : RecoveryPrefixAssignment.Data) (count cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (i : Fin 14) (hi : ∀ j,selectorSlots j≠i) :
    (cfg d count cap binaryCount committed guard selectorMachine.start).tapes i=
      (cfg (selectedData d out) count cap binaryCount committed out.guard
        (RecoveryCalls.controlCode RecoveryPrefixAssignment.sizes none)).tapes i := by
  rw [cfg_tapes,cfg_tapes]
  exact unchanged_fourteen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
    (Ne.symm (hi 1)) (Ne.symm (hi 5)) (Ne.symm (hi 6)) (Ne.symm (hi 2))

theorem selector_output (d : Data) (out : RecoveryPrefixAssignment.Data) (count cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (hcount : out.count=binaryCount)
    (hcommitted : out.committed=committed) (hcapacity : out.capacity=d.capacity) :
    RecoveryFocus.config selectorSlots
      (cfg d count cap binaryCount committed guard selectorMachine.start).heads
      (cfg d count cap binaryCount committed guard selectorMachine.start).tapes (selectorResult out)=
      cfg (selectedData d out) count cap binaryCount committed out.guard
        (RecoveryCalls.controlCode RecoveryPrefixAssignment.sizes none) := by
  exact focus_configuration selectorSlots selectorSlots_injective _ _ _ _ rfl
    (selector_result_heads d out count cap binaryCount committed)
    (selector_result_tapes d out count cap binaryCount committed hcount hcommitted hcapacity)
    (by intro i _; rfl) (selector_outside_tapes d out count cap binaryCount committed guard)

end NearCubicWires.RepairOrdinary.RecoveryAssignment
