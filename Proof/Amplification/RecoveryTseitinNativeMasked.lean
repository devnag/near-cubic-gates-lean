import Proof.Amplification.RecoveryTseitinNativeWorkspace

/-! Execute the original node consumer in reusable bounded scratch and
physically return every local head while retaining both live cursors. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 1335) := decide (i≠1062 ∧ i≠1333)
noncomputable def maskedMachine := MaskedReset.machine coldNodeMachine selected
def maskedHeads (pre out : List Bool) : Fin 1336→Nat :=
  Fin.addCases (m:=1335) (n:=1) (motive:=fun _=>Nat) (coldHeads pre out) (fun _=>0)
def maskedInput (n index : Nat) (word out : List Bool) (cap : Nat) : Fin 1336→List Bool :=
  Fin.addCases (m:=1335) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps cap i) (coldInput n index word out i)) (fun _=>List.replicate cap false)

theorem masked_entry {s : Nat} (p : Machine 1335 s) (n index : Nat) (pre word out : List Bool) (cap : Nat) :
    ZeroPadding.config (Rewind.Workspace.capacities 1335 cap)
      (Rewind.recording (ZeroPadding.config (caps cap) ⟨p.start,coldHeads pre out,coldInput n index word out⟩) 0)=
    (⟨(MaskedReset.machine p selected).start,maskedHeads pre out,maskedInput n index word out cap⟩ : Configuration 1336 (s+2)) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=1335) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [ZeroPadding.config,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
        Fin.addCases_left,maskedInput,ZeroPadding.pad_zero]
    · simp only [ZeroPadding.config,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
        Fin.addCases_right,maskedInput,List.replicate_zero,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

theorem masked_node_run {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (pre tail out : List Bool) (cap : Nat) (hcap : coldNodeBudget index node ≤ cap) :
    ∃ r,runFrom maskedMachine (2*coldNodeBudget index node+2)
      ⟨maskedMachine.start,maskedHeads pre out,maskedInput n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out cap⟩=some r ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node) ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      r.final.tapes 1062=PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
        (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2) ∧
      r.final.heads 1062=pre.length+(natWord (PCPPRequestNodeSchema.tag node).val).length+
        (natWord (PCPPRequestNodeSchema.fields node 1)).length+(natWord (PCPPRequestNodeSchema.fields node 2)).length ∧
      r.final.tapes 0=List.replicate n true ∧ r.final.tapes 1=List.replicate index true ∧
      (∀ i : Fin 1335,selected i=true → r.final.heads (i.castAdd 1)=0) ∧
      (∀ i : Fin 1335,work i → (r.final.tapes (i.castAdd 1)).length ≤ cap) ∧
      r.final.tapes 1335=List.replicate cap false ∧ r.final.heads 1335=0 ∧
      r.steps ≤ 2*coldNodeBudget index node+2 := by
  obtain ⟨base,hbase,bo,bh,bt,bth,bs⟩:=cold_node_run index node hw pre tail out
  have bc:=cold_node_counters index node pre tail out base _ hbase
  have support:=scratch_support coldNodeMachine n index pre _ out _ cap base hbase (bs.trans hcap)
  obtain ⟨padded,hp,pf,ps,_pp⟩:=ZeroPadding.run_config coldNodeMachine (caps cap) _ _ base hbase
  obtain ⟨r,hr,rf,rs,_rp⟩:=MaskedReset.workspace_run coldNodeMachine selected _ cap _ padded hp
    (by
      intro i hi
      have hh : i≠1062 ∧ i≠1333 := of_decide_eq_true hi
      exact head_zero pre out i hh.1 hh.2)
    (ps.trans_le (bs.trans hcap))
  rw [masked_entry] at hr
  have htime : 2*padded.steps+2 ≤ 2*coldNodeBudget index node+2 := by omega
  have hm:=runFrom_moreFuel maskedMachine _
    ((2*coldNodeBudget index node+2)-(2*padded.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  have old (i : Fin 1335) : r.final.tapes (i.castAdd 1)=ZeroPadding.pad (caps cap i) (base.final.tapes i) := by
    rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left,ZeroPadding.config]
  have oh (i : Fin 1335) : r.final.heads (i.castAdd 1)=if selected i then 0 else base.final.heads i := by
    rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left,ZeroPadding.config]
  refine ⟨r,hm,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rs.le.trans htime⟩
  · change r.final.tapes ((1333 : Fin 1335).castAdd 1)=_
    rw [old 1333]; simpa only [caps,if_neg (by decide : ¬work 1333),ZeroPadding.pad_zero] using bo
  · change r.final.heads ((1333 : Fin 1335).castAdd 1)=_
    rw [oh 1333]; exact bh
  · change r.final.tapes ((1062 : Fin 1335).castAdd 1)=_
    rw [old 1062]; simpa only [caps,if_neg (by decide : ¬work 1062),ZeroPadding.pad_zero] using bt
  · change r.final.heads ((1062 : Fin 1335).castAdd 1)=_
    rw [oh 1062]; exact bth
  · change r.final.tapes ((0 : Fin 1335).castAdd 1)=_
    rw [old 0]; simpa only [caps,if_neg (by decide : ¬work 0),ZeroPadding.pad_zero] using bc.1
  · change r.final.tapes ((1 : Fin 1335).castAdd 1)=_
    rw [old 1]; simpa only [caps,if_neg (by decide : ¬work 1),ZeroPadding.pad_zero] using bc.2
  · intro i hi; rw [oh i,hi]; rfl
  · intro i hi
    rw [old i,caps,if_pos hi,ZeroPadding.pad_length]
    exact max_le le_rfl (support i hi)
  · rw [rf]; rfl
  · rw [rf]; rfl

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
