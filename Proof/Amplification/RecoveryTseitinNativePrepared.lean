import Proof.Amplification.RecoveryTseitinNativeKernelLayout

/-! Run the original native reference preparer with the real formula output
cursor and the initially blank node-clause scratch present on physical tapes. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (out : List Bool) (i : Fin 236) : Nat := if i=234 then out.length else 0
def extraTapes (out : List Bool) (i : Fin 236) : List Bool := if i=234 then out else []
def coldHeads (pre out : List Bool) : Fin 1335→Nat :=
  Fin.addCases (m:=1099) (n:=236) (motive:=fun _=>Nat) (heads pre.length) (extraHeads out)
def coldInput (arity index : Nat) (word out : List Bool) : Fin 1335→List Bool :=
  Fin.addCases (m:=1099) (n:=236) (motive:=fun _=>List Bool) (input arity index word) (extraTapes out)
noncomputable def prepareMachine := TapeEmbedding.machine 236 referencesMachine
def generatedRef (k : Fin 4) : Fin 1335 := (referenceSlots (RecoveryTseitinReferences.referenceSlot k)).castAdd 236
def workExtra (i : Fin 235) : Fin 236 := if h : i.val<234 then ⟨i.val,by omega⟩ else 235
theorem work_extra (i : Fin 235) : kernelWork i=(workExtra i).natAdd 1099 := by
  apply Fin.ext
  unfold kernelWork workExtra
  split_ifs <;> rfl
theorem work_not_output (i : Fin 235) : workExtra i≠234 := by
  intro he
  have h:=congrArg Fin.val he
  unfold workExtra at h
  split_ifs at h <;> dsimp at h <;> omega

theorem prepare_run (arity index : Nat) (pre tail out : List Bool) (tag a b : Nat) :
    ∃ r,runFrom prepareMachine (referencesBudget arity index tag a b)
      ⟨prepareMachine.start,coldHeads pre out,coldInput arity index (PCPPNativeNodeRead.source pre tail tag a b) out⟩=some r ∧
      r.steps≤referencesBudget arity index tag a b ∧
      (∀ k,r.final.tapes (generatedRef k)=RecoveryTseitinReferences.fields arity index a b k ∧
        r.final.heads (generatedRef k)=0) ∧
      r.final.tapes 17=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (arity+index)) true ∧
      r.final.tapes 18=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (arity+index)+1) false ∧
      r.final.heads 17=0 ∧ r.final.heads 18=0 ∧
      r.final.tapes 1062=PCPPNativeNodeRead.source pre tail tag a b ∧
      r.final.heads 1062=pre.length+(natWord tag).length+(natWord a).length+(natWord b).length ∧
      r.final.tapes 1072=UnaryTemplate.tape tag ∧ r.final.heads 1072=1 ∧
      r.final.tapes 1082=UnaryTemplate.tape a ∧ r.final.heads 1082=1 ∧
      (∀ i,r.final.tapes (kernelWork i)=[] ∧ r.final.heads (kernelWork i)=0) ∧
      r.final.tapes 1333=out ∧ r.final.heads 1333=out.length := by
  obtain ⟨base,hbase,bs,bo,bd,bl,bdh,blh,b0,bh0,bt,bht,ba,bha⟩:=references_driver_run arity index pre tail tag a b
  let r:=TapeEmbedding.receipt (extraHeads out) (extraTapes out) base
  have hr:=TapeEmbedding.run_embed referencesMachine (extraHeads out) (extraTapes out) _ _ base hbase
  refine ⟨r,hr,bs,?_,bd,bl,bdh,blh,b0,bh0,bt,bht,ba,bha,?_,?_,?_⟩
  · intro k
    simpa only [r,generatedRef,TapeEmbedding.receipt_tapes_old,TapeEmbedding.receipt_heads_old] using bo k
  · intro i
    rw [work_extra]
    simp only [r,TapeEmbedding.receipt_tapes_new,TapeEmbedding.receipt_heads_new,extraTapes,extraHeads,
      if_neg (work_not_output i),and_self]
  · change r.final.tapes ((234 : Fin 236).natAdd 1099)=out
    simp only [r,TapeEmbedding.receipt_tapes_new]
    rfl
  · change r.final.heads ((234 : Fin 236).natAdd 1099)=out.length
    simp only [r,TapeEmbedding.receipt_heads_new]
    rfl

end NearCubicWires.RepairSource.RecoveryTseitinNative
