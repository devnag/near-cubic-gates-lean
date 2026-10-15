import Proof.MachineModel.OrdinaryWitnessPrefixLoop

/-! Complete bounded witness prefix: initial comparison, actual counted
stream loop and final framing delimiter. The padded suffix is never traversed. -/
namespace NearCubicWires.RepairOrdinary.WitnessPrefix
open LocalBitMultitape
open WitnessPrefixBody (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def closeAction : Action 6 2 :=
  ⟨1,fun i => if i=5 then some false else none,fun i => if i=5 then .right else .stay⟩
def close : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 1
  rule := fun s _ => if s.val=0 then some closeAction else none
def tailMachine : Machine 6 19 := Composition.machine WitnessPrefixLoop.machine close
def machine : Machine 6 31 := Composition.machine WitnessPrefixBody.check tailMachine
def budget (w B : ℕ) : ℕ := (B+1)*(8*w+12)

theorem close_step (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :
    step close (config 0 w counter bound cap false source out cursor)=
      some (config 1 w counter bound cap false source (out++[false]) cursor) := by
  change some (applyAction _ closeAction)=_
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,closeAction,config,TapeEmbedding.config,
      WitnessCounterCheck.config,HeadMove.apply,Fin.addCases]
  · funext i
    fin_cases i <;> simp [applyAction,closeAction,config,TapeEmbedding.config,
      WitnessCounterCheck.config,Fin.addCases,Streaming.write_append]

theorem close_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :
    ∃ r : ExecutionReceipt 6 2,
      runFrom close 1 (config 0 w counter bound cap false source out cursor)=some r ∧
      r.final=config 1 w counter bound cap false source (out++[false]) cursor := by
  let last := config (1 : Fin 2) w counter bound cap false source (out++[false]) cursor
  let tail : ExecutionReceipt 6 2 := ⟨last,0,last.tapeCells⟩
  have ht : runFrom close 0 last=some tail := runFrom_zero_of_halted close last (by rfl)
  have hr := runFrom_step close _ _ tail (by rfl) (close_step w counter bound cap source out cursor) ht
  exact ⟨_,hr,rfl⟩

theorem prefix_run (w cap : ℕ) (pre bits suffix out : List Bool)
    (hb : bits.length+1<2^w) (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 6 31,
      runFrom machine (budget w bits.length)
        (config machine.start w 0 bits.length cap false (pre++frame (bits++suffix)) out pre.length)=some r ∧
      r.final=config 30 w (bits.length+1) bits.length cap false
        (pre++frame (bits++suffix)) (out++frame bits) (pre.length+2*bits.length) := by
  obtain ⟨first,hf,hff⟩ := WitnessPrefixBody.check_run w 0 bits.length cap
    (pre++frame (bits++suffix)) out pre.length (by omega) (by omega) hcap
  obtain ⟨middle,hm,hmf⟩ := WitnessPrefixLoop.loop_run w 1 bits.length cap pre bits suffix out (by omega) hb hcap
  obtain ⟨last,hl,hlf⟩ := close_run w (bits.length+1) bits.length cap
    (pre++frame (bits++suffix)) (out++Streaming.marks bits) (pre.length+2*bits.length)
  have hmiddle : Composition.restart middle.final close.start=
      config 0 w (bits.length+1) bits.length cap false (pre++frame (bits++suffix))
        (out++Streaming.marks bits) (pre.length+2*bits.length) := by rw [hmf]; rfl
  rw [← hmiddle] at hl
  have htail := Composition.run_join WitnessPrefixLoop.machine close (WitnessPrefixLoop.budget w bits.length) 1
    (config WitnessPrefixLoop.machine.start w 1 bits.length cap (decide (1≤bits.length))
      (pre++frame (bits++suffix)) out pre.length) middle last hm hl
  have hfirst : Composition.restart first.final tailMachine.start=
      Composition.leftConfig 2 (config WitnessPrefixLoop.machine.start w 1 bits.length cap
        (decide (1≤bits.length)) (pre++frame (bits++suffix)) out pre.length) := by rw [hff]; rfl
  rw [← hfirst] at htail
  have hall := Composition.run_join WitnessPrefixBody.check tailMachine (8*w+7)
    (WitnessPrefixLoop.budget w bits.length+1+1)
    (config WitnessPrefixBody.check.start w 0 bits.length cap false
      (pre++frame (bits++suffix)) out pre.length) first (Composition.joinedReceipt middle last) hf htail
  have hmore := runFrom_moreFuel machine _ 1 _ (Composition.joinedReceipt first (Composition.joinedReceipt middle last)) hall
  have htime : ((8*w+7)+1+(WitnessPrefixLoop.budget w bits.length+1+1))+1=budget w bits.length := by
    dsimp only [WitnessPrefixLoop.budget,budget]
    ring
  rw [htime] at hmore
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt middle last),hmore,?_⟩
  simp only [Composition.joinedReceipt,hlf]
  have he : (out++Streaming.marks bits)++[false]=out++frame bits := by
    have hf : frame bits=Streaming.marks bits++[false] := by
      simpa only [List.append_nil,frame] using Streaming.frame_append bits []
    simp only [hf,List.append_assoc]
  rw [he]
  rfl

end NearCubicWires.RepairOrdinary.WitnessPrefix
