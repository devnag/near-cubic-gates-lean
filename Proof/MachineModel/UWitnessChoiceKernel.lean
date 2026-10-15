import Proof.MachineModel.UInputOrdinary
import Proof.MachineModel.OrdinaryWitnessPrefixReady

/-! Guarded choice copying. The inherited counter/advance routine is reused,
but each physical outer marker is tested before copying its payload. A short
witness therefore rejects instead of synthesizing zero choices from blanks. -/
namespace NearCubicWires.RepairOrdinary.UWitnessChoices
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool)
    (source out : List Bool) (cursor : ℕ) (accepted : Bool) : Configuration 7 s :=
  TapeEmbedding.config ![0] ![[accepted]]
    (WitnessPrefixBody.config state w counter bound cap flag source out cursor)
def check : Machine 7 12 := TapeEmbedding.machine 1 WitnessPrefixBody.check
def copyAction (next : Fin 4) (bit : Bool) (clear : Bool) : Action 7 4 :=
  ⟨next,fun i => if i.val=5 then some bit else if i.val=2 ∧ clear then some false else none,
    fun i => if i.val=4 ∨ i.val=5 then .right else .stay⟩
def copy : Machine 7 4 where
  descriptionBits := 0
  start := 0
  halted := fun s => decide (2 ≤ s.val)
  rule := fun s scanned => if s.val=0 then
    some (if scanned 4 then copyAction 1 true true else ⟨3,fun _ => none,fun _ => .stay⟩)
    else if s.val=1 then some (copyAction 2 (scanned 4) false) else none
def close : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,
    fun i => if i.val=5 then some false else if i.val=6 then some true else none,
    fun i => if i.val=5 then .right else .stay⟩ else none

theorem check_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ)
    (hn : counter+1 < 2^w) (hb : bound < 2^w) (hcap : 2*w+1 ≤ cap) :
    ∃ r,runFrom check (8*w+7) (config check.start w counter bound cap false source out cursor false)=some r ∧
      r.final=config 11 w (counter+1) bound cap (decide (counter+1 ≤ bound)) source out cursor false := by
  obtain ⟨base,hr,hf⟩ := WitnessPrefixBody.check_run w counter bound cap source out cursor hn hb hcap
  have h := TapeEmbedding.run_embed WitnessPrefixBody.check ![0] ![[false]] _ _ base hr
  exact ⟨TapeEmbedding.receipt ![0] ![[false]] base,h,by simp [TapeEmbedding.receipt,hf,config]⟩

theorem copy_run (w counter bound cap : ℕ) (pre tail out : List Bool) (bit : Bool) :
    ∃ r,runFrom copy 2
        (config 0 w counter bound cap true (pre++frame (bit::tail)) out pre.length false)=some r ∧
      r.final=config 2 w counter bound cap false (pre++frame (bit::tail))
        (out++[true,bit]) (pre.length+2) false ∧ r.steps=2 := by
  have hm : readTapeBit (pre++frame (bit::tail)) pre.length=true :=
    Streaming.read_append pre (bit::frame tail) true
  have hb : readTapeBit (pre++frame (bit::tail)) (pre.length+1)=bit := by
    have h := Streaming.read_append (pre++[true]) (frame tail) bit
    simpa [frame,List.append_assoc] using h
  have h1 : step copy (config 0 w counter bound cap true (pre++frame (bit::tail)) out pre.length false)=
      some (config 1 w counter bound cap false (pre++frame (bit::tail)) (out++[true]) (pre.length+1) false) := by
    simp [step,copy,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
      WitnessCounterCheck.config,Fin.addCases,hm]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,copyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,copyAction,Streaming.write_append,writeTapeBit]
  have h2 : step copy (config 1 w counter bound cap false (pre++frame (bit::tail)) (out++[true]) (pre.length+1) false)=
      some (config 2 w counter bound cap false (pre++frame (bit::tail)) (out++[true,bit]) (pre.length+2) false) := by
    simp [step,copy,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
      WitnessCounterCheck.config,Fin.addCases,hb]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,copyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,copyAction]
      simpa [List.append_assoc] using Streaming.write_append (out++[true]) bit
  exact ((Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2)).run (by rfl)

theorem copy_reject (w counter bound cap : ℕ) (pre out : List Bool) :
    ∃ r,runFrom copy 1 (config 0 w counter bound cap true (pre++frame []) out pre.length false)=some r ∧
      r.final=config 3 w counter bound cap true (pre++frame []) out pre.length false ∧ r.steps=1 := by
  have hm : readTapeBit (pre++frame []) pre.length=false := Streaming.read_append pre [] false
  have h : step copy (config 0 w counter bound cap true (pre++frame []) out pre.length false)=
      some (config 3 w counter bound cap true (pre++frame []) out pre.length false) := by
    simp [step,copy,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
      WitnessCounterCheck.config,Fin.addCases,hm]
    rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem close_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :
    ∃ r,runFrom close 1 (config 0 w counter bound cap false source out cursor false)=some r ∧
      r.final=config 1 w counter bound cap false source (out++[false]) cursor true ∧ r.steps=1 := by
  have h : step close (config 0 w counter bound cap false source out cursor false)=
      some (config 1 w counter bound cap false source (out++[false]) cursor true) := by
    simp [step,close,config,TapeEmbedding.config,WitnessPrefixBody.config,WitnessCounterCheck.config,Fin.addCases]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append,writeTapeBit]
  exact (Timed.single (by rfl) h).run (by rfl)

end NearCubicWires.RepairOrdinary.UWitnessChoices
