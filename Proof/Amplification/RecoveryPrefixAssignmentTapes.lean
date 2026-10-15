import Proof.Amplification.RecoveryCertificateTableFirst

/-! Physical retained-tape calls for the committed-prefix assignment rule.
The fallback bit is the output of the executed shared-table lookup. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  count : List Bool
  index : List Bool
  committed : List Bool
  guard : Bool
  flag : Bool
  result : Bool
  capacity : Nat

def Data.cfg {s : Nat} (d : Data) (q : Fin s) : Configuration 8 s :=
  ⟨q,fun _=>0,![frame d.count,frame d.index,[d.guard],List.replicate d.capacity false,
    frame d.committed,[d.flag],[d.result],List.replicate d.capacity false]⟩
def Data.compared (d : Data) : Data := {d with guard:=decide (value d.count≤value d.index)}
def Data.picked (d : Data) (index : List Bool) (flag : Bool) : Data :=
  {d with index:=index,flag:=flag,result:=(value d.committed).testBit (value d.index)}
def compareMachine := TapeEmbedding.machine 4 RecoveryPrefixCompare.machine
def bitSlots : Fin 6→Fin 8 := ![1,5,3,4,6,7]
theorem bitSlots_injective : Function.Injective bitSlots := by decide
noncomputable def bitMachine := RecoveryFocus.machine bitSlots RecoveryCommittedBit.machine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem compare_run (d : Data) (hw : d.count.length=d.index.length)
    (hc : 2*d.count.length+3≤d.capacity) :
    ∃ r,runFrom compareMachine (4*d.count.length+8) (d.cfg compareMachine.start)=some r ∧
      r.final=d.compared.cfg r.final.control ∧ r.steps=4*d.count.length+8 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryPrefixCompare.compare_ready d.count d.index d.guard d.capacity hw
  let extra : Fin 4→List Bool := ![frame d.committed,[d.flag],[d.result],List.replicate d.capacity false]
  have hrun := TapeEmbedding.run_embed RecoveryPrefixCompare.machine (fun _ : Fin 4=>0) extra _ _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 4=>0) extra
      (initialConfiguration RecoveryPrefixCompare.machine
        ![frame d.count,frame d.index,[d.guard],List.replicate d.capacity false])=d.cfg compareMachine.start := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4=>0) extra base,hrun,?_,hs⟩
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,Data.cfg,Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,Data.cfg,Fin.addCases,ht,extra,Data.compared,Nat.max_eq_left hc]

theorem bit_input (d : Data) :
    RecoveryFocus.config bitSlots (d.cfg bitMachine.start).heads (d.cfg bitMachine.start).tapes
      (initialConfiguration RecoveryCommittedBit.machine
        ![frame d.index,[d.flag],List.replicate d.capacity false,frame d.committed,[d.result],List.replicate d.capacity false])=
      d.cfg bitMachine.start := by
  apply focus_configuration bitSlots bitSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

def bitResult (d : Data) (index : List Bool) (flag : Bool)
    (q : Fin (Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2)) : Configuration 6 (Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2) :=
  ⟨q,fun _=>0,
    ![frame index,[flag],List.replicate d.capacity false,frame d.committed,
      [(value d.committed).testBit (value d.index)],List.replicate d.capacity false]⟩

theorem bit_result_heads (d : Data) (index : List Bool) (flag : Bool)
    (q : Fin (Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2)) (j : Fin 6) :
    (bitResult d index flag q).heads j=((d.picked index flag).cfg q).heads (bitSlots j) := by
  fin_cases j <;> rfl

theorem bit_result_tapes (d : Data) (index : List Bool) (flag : Bool)
    (q : Fin (Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2)) (j : Fin 6) :
    (bitResult d index flag q).tapes j=((d.picked index flag).cfg q).tapes (bitSlots j) := by
  fin_cases j <;> rfl

private theorem unchanged_eight (a b c d e f g h b' f' g' : List Bool) (i : Fin 8)
    (h1 : i≠1) (h5 : i≠5) (h6 : i≠6) :
    ![a,b,c,d,e,f,g,h] i=![a,b',c,d,e,f',g',h] i := by
  fin_cases i <;> first | rfl | contradiction

theorem bit_outside_tapes (d : Data) (index : List Bool) (flag : Bool)
    (q : Fin (Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2)) (i : Fin 8)
    (hi : ∀ j,bitSlots j≠i) :
    (d.cfg bitMachine.start).tapes i=((d.picked index flag).cfg q).tapes i := by
  exact unchanged_eight _ _ _ _ _ _ _ _ _ _ _ i
    (Ne.symm (hi 0)) (Ne.symm (hi 1)) (Ne.symm (hi 4))

theorem bit_output (d : Data) (index : List Bool) (flag : Bool)
    (q : Fin (Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2)) :
    RecoveryFocus.config bitSlots (d.cfg bitMachine.start).heads (d.cfg bitMachine.start).tapes
      (⟨q,fun _=>0,
        ![frame index,[flag],List.replicate d.capacity false,frame d.committed,
          [(value d.committed).testBit (value d.index)],List.replicate d.capacity false]⟩ : Configuration 6 _)=
      (d.picked index flag).cfg q := by
  exact focus_configuration bitSlots bitSlots_injective _ _ (bitResult d index flag q) _ rfl
    (bit_result_heads d index flag q) (bit_result_tapes d index flag q)
    (by intro i _; rfl) (bit_outside_tapes d index flag q)

theorem bit_run (d : Data) (hsmall : 2*d.index.length+1≤d.capacity)
    (hcap : RecoveryCommittedBit.rawCost d.index d.committed≤d.capacity) :
    ∃ r,runFrom bitMachine (2*RecoveryCommittedBit.rawCost d.index d.committed+2) (d.cfg bitMachine.start)=some r ∧
      r.steps≤2*RecoveryCommittedBit.rawCost d.index d.committed+2 ∧
      ∃ index flag,index.length=d.index.length ∧ r.final=(d.picked index flag).cfg r.final.control := by
  obtain ⟨base,hr,hs,hh,index,flag,hi,ht⟩ := RecoveryCommittedBit.lookup_run d.index d.committed d.flag d.result d.capacity hsmall hcap
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config bitSlots bitSlots_injective
    RecoveryCommittedBit.machine (d.cfg bitMachine.start).heads (d.cfg bitMachine.start).tapes _ _ base hr
  rw [bit_input] at hrun
  have he : base.final=(⟨base.final.control,fun _=>0,
      ![frame index,[flag],List.replicate d.capacity false,frame d.committed,
        [(value d.committed).testBit (value d.index)],List.replicate d.capacity false]⟩ : Configuration 6 _) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he,bit_output] at hfinal
  exact ⟨r,hrun,by rw [hsteps]; exact hs,index,flag,hi,by rw [hfinal]; rfl⟩

end NearCubicWires.RepairOrdinary.RecoveryPrefixAssignment
