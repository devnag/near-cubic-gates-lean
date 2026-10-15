import Proof.CaseAnalysis.RowsEstimatorScan

/-! Append the actual parity bit and exact cut bytes after the paid header.
The length driver is the scanner's output, never an assumed count stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Tail
open LocalBitMultitape RecoveryExecution Streaming RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bs=>if q.val=0 then
      some ⟨1,![none,none,none,some (bs 2)],![.stay,.stay,.stay,.right]⟩
    else if q.val=1 then
      if bs 1 then some ⟨1,![none,none,none,some (bs 0)],![.right,.right,.stay,.right]⟩
      else some ⟨2,fun _=>none,fun _=>.stay⟩
    else none

def cfg (q : Fin 3) (source : List Bool) (odd : Bool) (pos : ℕ) (out : List Bool) :
    Configuration 4 3:=⟨q,![pos,pos,0,out.length],
      ![source,List.replicate source.length true,[odd],out]⟩

theorem byte_step (pre tail out : List Bool) (b odd : Bool) :
    step machine (cfg 1 (pre++b::tail) odd pre.length out)=
      some (cfg 1 (pre++b::tail) odd (pre.length+1) (out++[b])):=by
  have hr:readTapeBit (List.replicate (pre++b::tail).length true) pre.length=true:=by
    simp [readTapeBit]
  simp only [List.length_append,List.length_cons] at hr
  simp [step,machine,cfg,Configuration.scanned,hr,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,write_append]

theorem stop (source out : List Bool) (odd : Bool) :
    step machine (cfg 1 source odd source.length out)=some (cfg 2 source odd source.length out):=by
  simp [step,machine,cfg,Configuration.scanned,readTapeBit]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem bytes_timed (pre bits out : List Bool) (odd : Bool) :
    Timed machine (bits.length+1) (cfg 1 (pre++bits) odd pre.length out)
      (cfg 2 (pre++bits) odd (pre.length+bits.length) (out++bits)):=by
  induction bits generalizing pre out with
  | nil=>simpa using Timed.single (by rfl) (stop pre out odd)
  | cons b bits ih=>
    have h:=(Timed.single (by rfl) (byte_step pre bits out b odd)).trans
      (by simpa only [List.append_assoc,List.length_append,List.length_singleton,List.cons_append,List.nil_append]
        using ih (pre++[b]) (out++[b]))
    simpa only [List.length_cons,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem append_run (source out : List Bool) (odd : Bool) : ∃ actual,
    runFrom machine (source.length+2) (cfg 0 source odd 0 out)=some actual ∧
    actual.final=cfg 2 source odd source.length (out++odd::source) ∧
    actual.steps=source.length+2:=by
  have hs:step machine (cfg 0 source odd 0 out)=some (cfg 1 source odd 0 (out++[odd])):=by
    simp [step,machine,cfg,Configuration.scanned,readTapeBit]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,write_append]
  have h:=(Timed.single (by rfl) hs).trans
    (by simpa only [List.nil_append,List.length_nil,Nat.zero_add] using bytes_timed [] source (out++[odd]) odd)
  have ht:1+(source.length+1)=source.length+2:=by omega
  rw [ht] at h
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h.run (by rfl)

theorem forward : CursorRestore.NoLeft machine 3:=by
  intro q bs a ha
  fin_cases q <;> simp [machine] at ha
  · cases ha;simp
  · split at ha <;> cases ha <;> simp

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Tail
