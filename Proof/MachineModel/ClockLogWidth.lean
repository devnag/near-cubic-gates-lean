import Proof.MachineModel.ClockUnaryProduct
import Proof.PCP.VerifierDecodingLength

/-! The logarithmic input guard comes from the actual counted binary word.
The decrement deletes its last unary mark and returns to the sentinel. -/
namespace NearCubicWires.RepairOrdinary.ClockLogWidth
open LocalBitMultitape
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ell_run (N : ℕ) :
    ∃ r : ExecutionReceipt 2 6,
      run LengthMachine.machine (4*PCPResourceLedger.ell N+3) ![frame (ClockBinary.word N),[]]=some r ∧
      r.final.tapes 0=frame (ClockBinary.word N) ∧
      r.final.tapes 1=false::List.replicate (PCPResourceLedger.ell N) true ∧
      r.final.heads = ![0,1] ∧ r.steps=4*PCPResourceLedger.ell N+3 := by
  obtain ⟨r,hr,hf,hs,_⟩ := RepairSource.VerifierDecoding.LengthMachine.length_run (ClockBinary.word N)
  rw [ClockDyadicLedger.bit_width] at hr hf hs
  exact ⟨r,hr,by simp [hf,RepairSource.VerifierDecoding.LengthMachine.cfg],
    by simp [hf,RepairSource.VerifierDecoding.LengthMachine.cfg],by simp [hf,RepairSource.VerifierDecoding.LengthMachine.cfg],hs⟩

def decrement : Machine 1 4 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 3
  rule := fun s bits => if s.val=0 then
      some ⟨if bits 0 then 0 else 1,fun _ => none,fun _ => if bits 0 then .right else .left⟩
    else if s.val=1 then some ⟨2,fun _ => some false,fun _ => .left⟩
    else if s.val=2 then some ⟨if bits 0 then 2 else 3,fun _ => none,fun _ => if bits 0 then .left else .right⟩
    else none

def cfg (state : Fin 4) (source : List Bool) (pos : ℕ) : Configuration 1 4 :=
  ⟨state,fun _ => pos,fun _ => source⟩
@[simp] theorem cfg_cells (state : Fin 4) (source : List Bool) (pos : ℕ) :
    (cfg state source pos).tapeCells=source.length := by simp [cfg,Configuration.tapeCells]

theorem forward_prefix (source : List Bool) (i count : ℕ)
    (hread : ∀ j<count,readTapeBit source (i+j)=true) :
    Prefix decrement source.length count (cfg 0 source i) (cfg 0 source (i+count)) := by
  induction count generalizing i with
  | zero => simpa using Prefix.refl (cfg 0 source i) (by simp)
  | succ count ih =>
    have hr : readTapeBit source i=true := by simpa using hread 0 (by omega)
    have hs : step decrement (cfg 0 source i)=some (cfg 0 source (i+1)) := by
      simp [step,decrement,cfg,Configuration.scanned,hr]
      rfl
    have ht := ih (i+1) (by intro j hj; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hread (j+1) (by omega))
    have h := Prefix.step (by simp) (by rfl) hs ht
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem backward_prefix (source : List Bool) (n : ℕ)
    (hzero : readTapeBit source 0=false)
    (hread : ∀ j<n,readTapeBit source (j+1)=true) :
    Prefix decrement source.length (n+1) (cfg 2 source n) (cfg 3 source 1) := by
  induction n with
  | zero =>
    have hs : step decrement (cfg 2 source 0)=some (cfg 3 source 1) := by
      simp [step,decrement,cfg,Configuration.scanned,hzero]
      rfl
    exact Prefix.step (by simp) (by rfl) hs (Prefix.refl _ (by simp))
  | succ n ih =>
    have hr := hread n (by omega)
    have hs : step decrement (cfg 2 source (n+1))=some (cfg 2 source n) := by
      simp [step,decrement,cfg,Configuration.scanned,hr]
      apply configuration_ext
      · rfl
      · funext i; simp [applyAction,HeadMove.apply]
      · rfl
    exact Prefix.step (by simp) (by rfl) hs (ih (fun j hj => hread j (by omega)))

theorem decrement_run (n : ℕ) :
    ∃ r : ExecutionReceipt 1 4,
      runFrom decrement (2*n+4) (cfg 0 (false::List.replicate (n+1) true) 1)=some r ∧
      r.final=cfg 3 (false::(List.replicate n true++[false])) 1 ∧ r.steps=2*n+4 := by
  let old := false::List.replicate (n+1) true
  let output := false::(List.replicate n true++[false])
  have hforward := forward_prefix old 1 (n+1) (by
    intro j hj
    simp [old,Nat.add_comm,ClockUnaryProduct.read_sentinel,hj])
  have hread : readTapeBit old (n+2)=false := by
    simpa [old] using ClockUnaryProduct.read_sentinel (n+1) (n+1)
  have hbridge : step decrement (cfg 0 old (n+2))=some (cfg 1 old (n+1)) := by
    simp [step,decrement,cfg,Configuration.scanned,hread]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply]
    · rfl
  have herase : step decrement (cfg 1 old (n+1))=some (cfg 2 output n) := by
    simp [step,decrement,cfg]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply]
    · funext i
      have hold : old=(false::List.replicate n true)++[true] := by
        simp [old,List.replicate_add,List.cons_append]
      simpa [applyAction,hold,output] using BinaryIncrement.write_prefix (false::List.replicate n true) [] true false
  have hback := backward_prefix output n (by rfl) (by
    intro j hj
    have hr : readTapeBit (UnaryTemplate.tape n) (j+1)=true := UnaryTemplate.tape_mark n j hj
    simpa [output,UnaryTemplate.tape] using hr)
  have hlen : output.length=old.length := by simp [old,output]
  rw [hlen] at hback
  have htail := Prefix.step (by simp : (cfg 0 old (n+2)).tapeCells≤old.length)
    (by rfl : decrement.halted (0 : Fin 4)=false) hbridge
    (Prefix.step (by simp) (by rfl : decrement.halted (1 : Fin 4)=false) herase hback)
  rw [show 1+(n+1)=n+2 by omega] at hforward
  have h := hforward.trans htail
  obtain ⟨r,hr,hf,hs,_⟩ := h.run (by rfl) (by simp [old,output])
  have htime : (n+1)+(n+1+1+1)=2*n+4 := by omega
  rw [htime] at hr
  exact ⟨r,hr,hf,by omega⟩

end NearCubicWires.RepairOrdinary.ClockLogWidth
