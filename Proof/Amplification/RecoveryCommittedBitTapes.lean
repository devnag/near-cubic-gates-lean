import Proof.Amplification.RecoveryPrefixCompare

/-! Fixed-width counter and streaming committed-word layout. Each decrement
is the existing ordinary predecessor machine; the committed-word terminator
bounds the scan independently of the numeric index. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCommittedBit
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  query : List Bool
  source : List Bool
  pos : Nat
  flag : Bool
  result : Bool
  capacity : Nat

def Data.cfg {s : Nat} (d : Data) (q : Fin s) : Configuration 5 s :=
  ⟨q,![0,0,0,d.pos,0],![frame d.query,[d.flag],List.replicate d.capacity false,d.source,[d.result]]⟩
def Data.atBit (d : Data) : Data := {d with pos:=d.pos+1}
def Data.afterPred (d : Data) : Data :=
  {d with query:=RecoveryListPredecessor.result d.query true,flag:=decide (value d.query≠0)}
def Data.picked (d : Data) (bit : Bool) : Data := {d with result:=bit}

def predMachine := TapeEmbedding.machine 2 RecoveryListPredecessor.machine

theorem pred_run (d : Data) (hc : 2*d.query.length+1≤d.capacity) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom predMachine (4*d.query.length+4) (d.cfg predMachine.start)=some r ∧
      r.final=d.afterPred.cfg r.final.control ∧ r.steps=4*d.query.length+4 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryListPredecessor.predecessor_ready d.query d.flag d.capacity
  have hrun := TapeEmbedding.run_embed RecoveryListPredecessor.machine ![d.pos,0] ![d.source,[d.result]] _ _ base hr
  have hi : TapeEmbedding.config ![d.pos,0] ![d.source,[d.result]]
      (initialConfiguration RecoveryListPredecessor.machine ![frame d.query,[d.flag],List.replicate d.capacity false])=
      d.cfg predMachine.start := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hrun
  refine ⟨TapeEmbedding.receipt ![d.pos,0] ![d.source,[d.result]] base,hrun,?_,hs⟩
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,Data.cfg,Data.afterPred,hh]
  · funext i; fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,Data.cfg,Data.afterPred,ht,Nat.max_eq_left hc]

def marker : Machine 5 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val != 0
  rule := fun q scanned=>if q.val=0 then
    some ⟨if scanned 3 then 1 else 2,fun _=>none,
      fun i=>if i=3 && scanned 3 then .right else .stay⟩ else none

theorem marker_cons (d : Data) (pre bits : List Bool) (bit : Bool)
    (hs : d.source=pre++frame (bit::bits)) (hp : d.pos=pre.length) :
    ∃ r : ExecutionReceipt 5 3,runFrom marker 1 (d.cfg 0)=some r ∧
      r.final=d.atBit.cfg 1 ∧ r.steps=1 := by
  have hread : readTapeBit d.source d.pos=true := by
    rw [hs,hp]
    simpa [frame] using Streaming.read_append pre (bit::frame bits) true
  have h : step marker (d.cfg 0)=some (d.atBit.cfg 1) := by
    simp [step,marker,Data.cfg,Configuration.scanned,hread]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,Data.atBit,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem marker_nil (d : Data) (pre : List Bool) (hs : d.source=pre++frame []) (hp : d.pos=pre.length) :
    ∃ r : ExecutionReceipt 5 3,runFrom marker 1 (d.cfg 0)=some r ∧ r.final=d.cfg 2 ∧ r.steps=1 := by
  have hread : readTapeBit d.source d.pos=false := by
    rw [hs,hp]
    simpa [frame] using Streaming.read_append pre [] false
  have h : step marker (d.cfg 0)=some (d.cfg 2) := by
    simp [step,marker,Data.cfg,Configuration.scanned,hread]
    rfl
  exact (Timed.single (by rfl) h).run (by rfl)

def advance : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if i=3 then .right else .stay⟩ else none

theorem advance_run (d : Data) :
    ∃ r : ExecutionReceipt 5 2,runFrom advance 1 (d.cfg 0)=some r ∧
      r.final=d.atBit.cfg 1 ∧ r.steps=1 := by
  have h : step advance (d.cfg 0)=some (d.atBit.cfg 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) h).run (by rfl)

def writeResult (fromSource bit : Bool) : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    some ⟨1,fun i=>if i=4 then some (if fromSource then scanned 3 else bit) else none,fun _=>.stay⟩ else none

theorem write_run (d : Data) (fromSource bit : Bool) :
    ∃ r : ExecutionReceipt 5 2,runFrom (writeResult fromSource bit) 1 (d.cfg 0)=some r ∧
      r.final=(d.picked (if fromSource then readTapeBit d.source d.pos else bit)).cfg 1 ∧ r.steps=1 := by
  have h : step (writeResult fromSource bit) (d.cfg 0)=
      some ((d.picked (if fromSource then readTapeBit d.source d.pos else bit)).cfg 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryCommittedBit
