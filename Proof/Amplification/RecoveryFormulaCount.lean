import Proof.Amplification.RecoveryFormulaPrefix
import Proof.PCP.ProjectionNormalizationFieldList

/-! Count the actual fields inside one external frame. Payload false bits
are skipped in their value position; only inner-frame delimiters advance
the serializer's literal sentinel count. Empty fields and empty lists work. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaCount
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 6) (move : HeadMove) (write : Option Bool) : Action 2 6 :=
  ⟨q,![none,write],![move,if write.isSome then .right else .stay]⟩
def raw : Machine 2 6 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=5
  rule := fun q bits=>match q.val with
    | 0 => some (action 1 .stay (some false))
    | 1 => some (if bits 0 then action 2 .right none else action 5 .stay none)
    | 2 => some (if bits 0 then action 3 .right none else action 1 .right (some true))
    | 3 => some (action 4 .right none)
    | 4 => some (action 1 .right none)
    | _ => none

def cfg (q : Fin 6) (source : List Bool) (pos count : Nat) : Configuration 2 6 :=
  ⟨q,![pos,count+1],![source,VerifierDecoding.CompareMachine.word count]⟩

theorem boot (source : List Bool) : step raw (initialConfiguration raw ![source,[]])=
    some (cfg 1 source 0 0) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem marker (pre tail : List Bool) (count : Nat) :
    step raw (cfg 1 (pre++true::tail) pre.length count)=
      some (cfg 2 (pre++true::tail) (pre.length+1) count) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem inner_marker (pre tail : List Bool) (count : Nat) :
    step raw (cfg 2 (pre++true::tail) pre.length count)=
      some (cfg 3 (pre++true::tail) (pre.length+1) count) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem skip (q : Fin 6) (source : List Bool) (pos count : Nat) (hq : q=3 ∨ q=4) :
    step raw (cfg q source pos count)=some (cfg (if q=3 then 4 else 1) source (pos+1) count) := by
  rcases hq with rfl|rfl
  all_goals apply congrArg some
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem bit_trace (pre tail : List Bool) (bit : Bool) (count : Nat) :
    Timed raw 4 (cfg 1 (pre++[true,true,true,bit]++tail) pre.length count)
      (cfg 1 (pre++[true,true,true,bit]++tail) (pre.length+4) count) := by
  let source := pre++[true,true,true,bit]++tail
  have h0 := marker pre (true::true::bit::tail) count
  have h1 := inner_marker (pre++[true]) (true::bit::tail) count
  have h2 := skip 3 source (pre.length+2) count (Or.inl rfl)
  have h3 := skip 4 source (pre.length+3) count (Or.inr rfl)
  have h1' : step raw (cfg 2 source (pre.length+1) count)=some (cfg 3 source (pre.length+2) count) := by
    simpa [source,List.append_assoc,Nat.add_assoc] using h1
  have h0' : step raw (cfg 1 source pre.length count)=some (cfg 2 source (pre.length+1) count) := by
    simpa [source,List.append_assoc] using h0
  exact (Timed.single (by rfl) h0').trans ((Timed.single (by rfl) h1').trans
    ((Timed.single (by rfl) h2).trans (Timed.single (by rfl) h3)))

theorem delimiter (pre tail : List Bool) (count : Nat) :
    step raw (cfg 2 (pre++false::tail) pre.length count)=
      some (cfg 1 (pre++false::tail) (pre.length+1) (count+1)) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply,Nat.add_assoc]
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (false::List.replicate count true) (count+1) true=
        false::List.replicate (count+1) true
      simpa only [List.length_cons,List.length_replicate,List.replicate_add,List.replicate_one,List.cons_append]
        using Streaming.write_append (false::List.replicate count true) true

theorem delimiter_trace (pre tail : List Bool) (count : Nat) :
    Timed raw 2 (cfg 1 (pre++[true,false]++tail) pre.length count)
      (cfg 1 (pre++[true,false]++tail) (pre.length+2) (count+1)) := by
  have h0 := marker pre (false::tail) count
  have h1 := delimiter (pre++[true]) tail count
  have h1' : step raw (cfg 2 (pre++[true,false]++tail) (pre.length+1) count)=
      some (cfg 1 (pre++[true,false]++tail) (pre.length+2) (count+1)) := by
    simpa [List.append_assoc,Nat.add_assoc] using h1
  have h0' : step raw (cfg 1 (pre++[true,false]++tail) pre.length count)=
      some (cfg 2 (pre++[true,false]++tail) (pre.length+1) count) := by
    simpa [List.append_assoc] using h0
  exact (Timed.single (by rfl) h0').trans (Timed.single (by rfl) h1')

theorem field_trace (bits pre tail : List Bool) (count : Nat) :
    Timed raw (4*bits.length+2)
      (cfg 1 (pre++Streaming.marks (frame bits)++tail) pre.length count)
      (cfg 1 (pre++Streaming.marks (frame bits)++tail) (pre.length+4*bits.length+2) (count+1)) := by
  induction bits generalizing pre with
  | nil => simpa [RepairOrdinary.frame,Streaming.marks] using delimiter_trace pre tail count
  | cons bit bits ih =>
    have h0 := bit_trace pre (Streaming.marks (frame bits)++tail) bit count
    have ht := ih (pre++[true,true,true,bit])
    have he : (pre++[true,true,true,bit])++Streaming.marks (frame bits)++tail=
        pre++Streaming.marks (frame (bit::bits))++tail := by
      simp [RepairOrdinary.frame,Streaming.marks,List.append_assoc]
    rw [he] at ht
    have ht' : Timed raw (4*bits.length+2)
        (cfg 1 (pre++Streaming.marks (frame (bit::bits))++tail) (pre.length+4) count)
        (cfg 1 (pre++Streaming.marks (frame (bit::bits))++tail) (pre.length+4*(bit::bits).length+2) (count+1)) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using ht
    have h0' : Timed raw 4
        (cfg 1 (pre++Streaming.marks (frame (bit::bits))++tail) pre.length count)
        (cfg 1 (pre++Streaming.marks (frame (bit::bits))++tail) (pre.length+4) count) := by
      simpa [RepairOrdinary.frame,Streaming.marks,List.append_assoc] using h0
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h0'.trans ht'

theorem fields_trace (fields : List (List Bool)) (pre tail : List Bool) (count : Nat) :
    Timed raw (2*(FieldList.stream fields).length)
      (cfg 1 (pre++Streaming.marks (FieldList.stream fields)++tail) pre.length count)
      (cfg 1 (pre++Streaming.marks (FieldList.stream fields)++tail)
        (pre.length+2*(FieldList.stream fields).length) (count+fields.length)) := by
  induction fields generalizing pre count with
  | nil => simpa [FieldList.stream,Streaming.marks] using Timed.refl raw (cfg 1 (pre++tail) pre.length count)
  | cons bits fields ih =>
    have h0 := field_trace bits pre (Streaming.marks (FieldList.stream fields)++tail) count
    have ht := ih (pre++Streaming.marks (frame bits)) (count+1)
    have hs : Streaming.marks (FieldList.stream (bits::fields))=
        Streaming.marks (frame bits)++Streaming.marks (FieldList.stream fields) := by
      simp [FieldList.stream_cons,Streaming.marks]
    have he : (pre++Streaming.marks (frame bits))++Streaming.marks (FieldList.stream fields)++tail=
        pre++Streaming.marks (FieldList.stream (bits::fields))++tail := by rw [hs]; simp [List.append_assoc]
    rw [he] at ht
    have h0' : Timed raw (4*bits.length+2)
        (cfg 1 (pre++Streaming.marks (FieldList.stream (bits::fields))++tail) pre.length count)
        (cfg 1 (pre++Streaming.marks (FieldList.stream (bits::fields))++tail)
          (pre.length+4*bits.length+2) (count+1)) := by
      simpa only [hs,List.append_assoc] using h0
    have ht' : Timed raw (2*(FieldList.stream fields).length)
        (cfg 1 (pre++Streaming.marks (FieldList.stream (bits::fields))++tail)
          (pre.length+4*bits.length+2) (count+1))
        (cfg 1 (pre++Streaming.marks (FieldList.stream (bits::fields))++tail)
          (pre.length+2*(FieldList.stream (bits::fields)).length) (count+(bits::fields).length)) := by
      simpa [Streaming.marks_length,frame_length,FieldList.stream_cons,List.length_append,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    simpa [FieldList.stream_cons,List.length_append,frame_length,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h0'.trans ht'

end NearCubicWires.RepairSource.RecoveryFormulaCount
