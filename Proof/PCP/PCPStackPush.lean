import Proof.PCP.PCPUnarySplit

/-! A physical binary-field stack push. It counts the framed source cells,
then copies them backwards onto the retained stack cursor. This format lets
the matching pop recover the original field by a single reverse scan. -/
namespace NearCubicWires.RepairOrdinary.PCPStackPush
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def forwardAction (q : Fin 4) (move : HeadMove) : Action 3 4 :=
  ⟨q,![none,none,some true],![move,.stay,move]⟩
def backwardAction (bit : Bool) : Action 3 4 :=
  ⟨2,![none,some bit,some false],![.left,.right,.left]⟩
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
      some (if bits 0 then forwardAction 1 .right else forwardAction 2 .stay)
    else if q.val=1 then some (forwardAction 0 .right)
    else if q.val=2 then if bits 2 then some (backwardAction (bits 0))
      else some ⟨3,fun _ => none,fun _ => .stay⟩ else none
def forward (q : Fin 4) (source out : List Bool) (pos : ℕ) : Configuration 3 4 :=
  ⟨q,![pos,out.length,pos],![source,out,List.replicate pos true]⟩
def backward (q : Fin 4) (source out : List Bool) (remaining erased : ℕ) : Configuration 3 4 :=
  ⟨q,![remaining-1,out.length,remaining-1],
    ![source,out,List.replicate remaining true++List.replicate erased false]⟩

theorem forward_step (q next : Fin 4) (source out : List Bool) (pos : ℕ)
    (hr : machine.rule q (forward q source out pos).scanned=some (forwardAction next .right)) :
    step machine (forward q source out pos)=some (forward next source out (pos+1)) := by
  simp only [step,forward] at hr ⊢
  rw [hr]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change writeTapeBit (List.replicate pos true) pos true=List.replicate (pos+1) true
      have h := Streaming.write_append (List.replicate pos true) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using h

theorem scan (pre bits out : List Bool) :
    Timed machine (2*bits.length)
      (forward 0 (Streaming.marks pre++frame bits) out (2*pre.length))
      (forward 0 (Streaming.marks pre++frame bits) out (2*(pre.length+bits.length))) := by
  induction bits generalizing pre with
  | nil => simpa using Timed.refl machine (forward 0 (Streaming.marks pre++frame []) out (2*pre.length))
  | cons b bs ih =>
    let source := Streaming.marks pre++frame (b::bs)
    have hb : readTapeBit source (2*pre.length)=true := by
      simpa only [source,frame,RepairOrdinary.frame,Streaming.marks_length] using
        Streaming.read_append (Streaming.marks pre) (b::frame bs) true
    have h1 := forward_step 0 1 source out (2*pre.length)
      (by simp [machine,forward,Configuration.scanned,hb])
    have h2 := forward_step 1 0 source out (2*pre.length+1) (by rfl)
    have ht := ih (pre++[b])
    have he : Streaming.marks (pre++[b])++frame bs=source := by
      simp [source,Streaming.marks,frame,RepairOrdinary.frame,List.append_assoc]
    rw [he] at ht
    have hp : 2*(pre++[b]).length=2*pre.length+1+1 := by simp; omega
    rw [hp] at ht
    have h := (Timed.single (by rfl : machine.halted (0 : Fin 4)=false) h1).trans
      ((Timed.single (by rfl : machine.halted (1 : Fin 4)=false) h2).trans ht)
    have htime : 1+(1+2*bs.length)=2*(b::bs).length := by simp; omega
    rw [htime] at h
    simpa only [List.length_append,List.length_singleton,List.length_cons,List.length_nil,source,
      Nat.mul_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem turn_step (bits out : List Bool) :
    step machine (forward 0 (frame bits) out (2*bits.length))=
      some (backward 2 (frame bits) out (2*bits.length+1) 0) := by
  have hf : frame bits=Streaming.marks bits++[false] := by
    simpa [frame] using Streaming.frame_append bits []
  have hb : readTapeBit (frame bits) (2*bits.length)=false := by
    rw [hf]
    simpa only [Streaming.marks_length] using Streaming.read_append (Streaming.marks bits) [] false
  simp only [step,machine,forward,Configuration.scanned,Matrix.cons_val_zero,Fin.val_zero,
    ↓reduceIte,hb]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,forwardAction,backward,HeadMove.apply]
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change writeTapeBit (List.replicate (2*bits.length) true) (2*bits.length) true=
        List.replicate (2*bits.length+1) true++List.replicate 0 false
      have h := Streaming.write_append (List.replicate (2*bits.length) true) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one,
        List.replicate_zero,List.append_nil] using h

theorem backward_step (pre done out : List Bool) (bit : Bool) (erased : ℕ) :
    step machine (backward 2 (pre++bit::done) out (pre.length+1) erased)=
      some (backward 2 (pre++bit::done) (out++[bit]) pre.length (erased+1)) := by
  simp [step,machine,backward,Configuration.scanned,Streaming.read_append,Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,backwardAction,HeadMove.apply]
  · funext i
    fin_cases i
    · rfl
    · simpa [applyAction,backwardAction] using Streaming.write_append out bit
    · simpa [applyAction,backwardAction] using Streaming.erase_counter pre.length erased

theorem backward_end (source out : List Bool) (erased : ℕ) :
    step machine (backward 2 source out 0 erased)=some (backward 3 source out 0 erased) := by
  simp [step,machine,backward,Configuration.scanned,Streaming.read_zeros]
  rfl

theorem reverse_run (bits done out : List Bool) (erased : ℕ) :
    Timed machine (bits.length+1) (backward 2 (bits.reverse++done) out bits.length erased)
      (backward 3 (bits.reverse++done) (out++bits) 0 (bits.length+erased)) := by
  induction bits generalizing done out erased with
  | nil =>
    simpa using Timed.single (by rfl : machine.halted (2 : Fin 4)=false)
      (backward_end done out erased)
  | cons b bs ih =>
    have h1 := backward_step bs.reverse done out b erased
    simp only [List.length_reverse] at h1
    have ht := ih (b::done) (out++[b]) (erased+1)
    have h := (Timed.single (by rfl : machine.halted (2 : Fin 4)=false) h1).trans ht
    simpa only [List.reverse_cons,List.length_cons,List.length_reverse,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem push_run (bits stack : List Bool) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom machine (4*bits.length+3) (forward 0 (frame bits) stack 0)=some r ∧
      r.final=backward 3 (frame bits) (stack++(frame bits).reverse) 0 (2*bits.length+1) ∧
      r.steps=4*bits.length+3 := by
  have hf := scan [] bits stack
  simp only [Streaming.marks,List.flatMap_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.zero_add] at hf
  have hb := reverse_run (frame bits).reverse [] stack 0
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse,frame_length,Nat.add_zero] at hb
  have h := hf.trans ((Timed.single (by rfl : machine.halted (0 : Fin 4)=false)
    (turn_step bits stack)).trans hb)
  have he : 2*bits.length+(1+(2*bits.length+1+1))=4*bits.length+3 := by omega
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.PCPStackPush
