import Proof.Hierarchy.HierarchyInputLength
import Proof.PCP.VerifierDecodingCompare

/-! Print the exact sentinel unary predecessor of a framed word's bit length.
The first logical bit is skipped, every later bit writes one mark, and even
the empty input physically receives its leading false sentinel. -/
namespace NearCubicWires.RepairOrdinary.ClockFloorLog
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 6 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==5
  rule := fun s scan => match s.val with
    | 0 => some ⟨1,![none,some false],![.stay,.right]⟩
    | 1 => some (if scan 0 then ⟨2,fun _ => none,![.right,.stay]⟩ else ⟨5,fun _ => none,fun _ => .stay⟩)
    | 2 => some ⟨3,fun _ => none,![.right,.stay]⟩
    | 3 => some (if scan 0 then ⟨4,![none,some true],fun _ => .right⟩ else ⟨5,fun _ => none,fun _ => .stay⟩)
    | 4 => some ⟨3,fun _ => none,![.right,.stay]⟩
    | _ => none
def config (state : Fin 6) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 6 :=
  ⟨state,![pos,out.length],![source,out]⟩

theorem loop_pair (pre bits out : List Bool) (b : Bool) :
    Timed raw 2 (config 3 (pre++frame (b::bits)) pre.length out)
      (config 3 (pre++frame (b::bits)) (pre.length+2) (out++[true])) := by
  have hr : readTapeBit (pre++frame (b::bits)) pre.length=true := Streaming.read_append pre (b::frame bits) true
  have h1 : step raw (config 3 (pre++frame (b::bits)) pre.length out)=
      some (config 4 (pre++frame (b::bits)) (pre.length+1) (out++[true])) := by
    simp [step,raw,config,Configuration.scanned,hr]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
  have h2 : step raw (config 4 (pre++frame (b::bits)) (pre.length+1) (out++[true]))=
      some (config 3 (pre++frame (b::bits)) (pre.length+2) (out++[true])) := by
    simp [step,raw,config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2)

theorem loop_end (pre out : List Bool) :
    Timed raw 1 (config 3 (pre++frame []) pre.length out) (config 5 (pre++frame []) pre.length out) := by
  have hr : readTapeBit (pre++frame []) pre.length=false := Streaming.read_append pre [] false
  have hs : step raw (config 3 (pre++frame []) pre.length out)=some (config 5 (pre++frame []) pre.length out) := by
    simp [step,raw,config,Configuration.scanned,hr]
    rfl
  exact Timed.single (by rfl) hs

theorem loop_prefix (pre bits out : List Bool) :
    Timed raw (2*bits.length+1) (config 3 (pre++frame bits) pre.length out)
      (config 5 (pre++frame bits) (pre.length+2*bits.length) (out++List.replicate bits.length true)) := by
  induction bits generalizing pre out with
  | nil => simpa using loop_end pre out
  | cons b bits ih =>
    have hp := loop_pair pre bits out b
    have hi := ih (pre++[true,b]) (out++[true])
    have he : (pre++[true,b])++frame bits=pre++frame (b::bits) := by simp [frame,List.append_assoc]
    rw [he,show (pre++[true,b]).length=pre.length+2 by simp] at hi
    have h := hp.trans hi
    simpa [List.replicate_succ,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem raw_run (bits : List Bool) :
    ∃ r,run raw (2*bits.length+2) ![frame bits,[]]=some r ∧
      r.final=config 5 (frame bits) (2*bits.length)
        (RepairSource.VerifierDecoding.CompareMachine.word (bits.length-1)) ∧ r.steps=2*bits.length+2 := by
  have hstart : step raw (config 0 (frame bits) 0 [])=some (config 1 (frame bits) 0 [false]) := by
    simp [step,raw,config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have hp := Timed.single (by rfl) hstart
  have h : Timed raw (2*bits.length+2) (config 0 (frame bits) 0 [])
      (config 5 (frame bits) (2*bits.length) (RepairSource.VerifierDecoding.CompareMachine.word (bits.length-1))) := by
    cases bits with
    | nil =>
      have hs : step raw (config 1 (frame []) 0 [false])=some (config 5 (frame []) 0 [false]) := by rfl
      exact hp.trans (Timed.single (by rfl) hs)
    | cons b bits =>
      have hs1 : step raw (config 1 (frame (b::bits)) 0 [false])=
          some (config 2 (frame (b::bits)) 1 [false]) := by
        simp [step,raw,config,Configuration.scanned,frame,readTapeBit]
        apply configuration_ext
        · rfl
        · funext i; fin_cases i <;> rfl
        · rfl
      have hs2 : step raw (config 2 (frame (b::bits)) 1 [false])=
          some (config 3 (frame (b::bits)) 2 [false]) := by
        simp [step,raw,config]
        apply configuration_ext
        · rfl
        · funext i; fin_cases i <;> rfl
        · rfl
      have hi := loop_prefix [true,b] bits [false]
      have h := ((hp.trans (Timed.single (by rfl) hs1)).trans (Timed.single (by rfl) hs2)).trans hi
      have htime : 1+1+1+(2*bits.length+1)=2*(b::bits).length+2 := by simp; omega
      rw [htime] at h
      simpa [frame,RepairSource.VerifierDecoding.CompareMachine.word,Nat.mul_add,Nat.add_comm] using h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  have hi : config 0 (frame bits) 0 []=initialConfiguration raw ![frame bits,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,hf,hs⟩

end NearCubicWires.RepairOrdinary.ClockFloorLog
