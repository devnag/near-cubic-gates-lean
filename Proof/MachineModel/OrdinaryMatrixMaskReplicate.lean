import Proof.MachineModel.OrdinaryMatrixCoefficientBitNative

/-! One actual gate-mask bit is replicated across the physical Buckets
sentinel. The raw bit is retained during the scan and consumed exactly
once; the sentinel is physically reset for the next gate. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskReplicate
open LocalBitMultitape RecoveryExecution
open MatrixRawBlock (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copy : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ scan => if scan 0 then
    some ⟨0,![none,none,some (scan 1)],![.right,.stay,.right]⟩
    else some ⟨1,fun _ => none,![.stay,.right,.stay]⟩
def machine := Composition.machine copy MatrixRawBlock.reset

theorem emit_step (bit : Bool) (pre suffix out : List Bool) (total done : ℕ) (hd : done<total) :
    step copy (config 0 (UnaryTemplate.tape total) (done+1) (pre++bit::suffix) pre.length out)=
      some (config 0 (UnaryTemplate.tape total) (done+2) (pre++bit::suffix) pre.length (out++[bit])) := by
  simp [step,copy,config,Configuration.scanned,UnaryTemplate.tape_mark total done hd,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem stop_step (source out : List Bool) (pos total : ℕ) :
    step copy (config 0 (UnaryTemplate.tape total) (total+1) source pos out)=
      some (config 1 (UnaryTemplate.tape total) (total+1) source (pos+1) out) := by
  simp [step,copy,config,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem copy_prefix (bit : Bool) (pre suffix out : List Bool) (total done remaining : ℕ)
    (hcount : done+remaining=total) :
    Timed copy (remaining+1)
      (config 0 (UnaryTemplate.tape total) (done+1) (pre++bit::suffix) pre.length out)
      (config 1 (UnaryTemplate.tape total) (total+1) (pre++bit::suffix) (pre.length+1)
        (out++List.replicate remaining bit)) := by
  induction remaining generalizing done out with
  | zero =>
    have hd : done=total := by omega
    subst done
    simpa using Timed.single (by rfl) (stop_step (pre++bit::suffix) out pre.length total)
  | succ n ih =>
    have hs := Timed.single (by rfl) (emit_step bit pre suffix out total done (by omega))
    have ht := ih (out++[bit]) (done+1) (by omega)
    have hh := hs.trans (by simpa only [Nat.add_assoc] using ht)
    simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem replicate_run (bit : Bool) (pre suffix out : List Bool) (count : ℕ) : ∃ actual,
    runFrom machine (2*count+4)
      (config machine.start (UnaryTemplate.tape count) 1 (pre++bit::suffix) pre.length out)=some actual ∧
    actual.final=config 4 (UnaryTemplate.tape count) 1 (pre++bit::suffix) (pre.length+1)
      (out++List.replicate count bit) ∧ actual.steps=2*count+4 := by
  obtain ⟨first,hfirst,ff,fs⟩ := (copy_prefix bit pre suffix out count 0 count (by omega)).run (by rfl)
  obtain ⟨last,hl,lf,ls,_⟩ := UnaryTemplate.reset_run count
  let appended := out++List.replicate count bit
  have he := TapeEmbedding.run_embed UnaryTemplate.machine (![pre.length+1,appended.length] : Fin 2 → ℕ)
    ![pre++bit::suffix,appended] _ _ last hl
  have hi : Composition.restart first.final MatrixRawBlock.reset.start=
      config 0 (UnaryTemplate.tape count) (count+1) (pre++bit::suffix) (pre.length+1) appended := by rw [ff]; rfl
  have he' : runFrom MatrixRawBlock.reset (count+2) (Composition.restart first.final MatrixRawBlock.reset.start)=
      some (TapeEmbedding.receipt (![pre.length+1,appended.length] : Fin 2 → ℕ) ![pre++bit::suffix,appended] last) := by
    rw [hi]
    simpa only [MatrixRawBlock.place,MatrixRawBlock.reset] using he
  have hj := Composition.run_join copy MatrixRawBlock.reset _ _ _ first _ hfirst he'
  have hc : count+1+1+(count+2)=2*count+4 := by omega
  rw [hc] at hj
  refine ⟨Composition.joinedReceipt first (TapeEmbedding.receipt (![pre.length+1,appended.length] : Fin 2 → ℕ)
    ![pre++bit::suffix,appended] last),hj,?_,?_⟩
  · change Composition.rightConfig 2 (TapeEmbedding.config (![pre.length+1,appended.length] : Fin 2 → ℕ)
      ![pre++bit::suffix,appended] last.final)=_
    rw [lf,MatrixRawBlock.place]
    rfl
  · change first.steps+1+last.steps=_
    omega

end NearCubicWires.RepairOrdinary.MatrixMaskReplicate
