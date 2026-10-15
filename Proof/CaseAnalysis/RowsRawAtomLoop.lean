import Proof.CaseAnalysis.RowsRawAtomRound
import Proof.Amplification.RecoveryCursorCalls

/-! The actual source-produced child count controls the absolute-index
stream directly. It is not copied into an additional enumeration driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskBodyParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 4 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def sizes : Fin 3→ℕ :=
  ![1,2+Fintype.card (RecoveryCalls.Control RowMaskBody.sizes)+2,2]
noncomputable def programs : (i : Fin 3)→Machine 4 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>CloseoutRowsRawAtomRound.machine
  | ⟨2,_⟩=>CloseoutRowsRawAtomRound.mark false
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 4→Bool) : Option (Fin 3) :=
  if i=0 then some (if bits 0 then 1 else 2) else if i=1 then some 0 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 3) (source : List Bool) (pos index count : ℕ) (out : List Bool) :=
  controlConfig (RecoveryCalls.code sizes i) (cfg (programs i).start source pos (index+1) count out)
noncomputable def final (source : List Bool) (pos index count : ℕ) (out : List Bool) :=
  RecoveryCalls.stopped sizes (cfg idle.start source pos (index+1) count out).heads
    (cfg idle.start source pos (index+1) count out).tapes
def indices (offset n : ℕ) : List (List ℕ):=(List.range' offset n).map (fun i=>[i])
def budget (offset n : ℕ):=n*(4*(offset+n)+31)+3

theorem probe (pre tail : List Bool) (bit : Bool) (index count : ℕ) (out : List Bool) :
    Timed machine 1 (entry 0 (pre++bit::tail) pre.length index count out)
      (entry (if bit then 1 else 2) (pre++bit::tail) pre.length index count out) := by
  have hn : next 0 (programs 0).start (cfg (programs 0).start (pre++bit::tail)
      pre.length (index+1) count out).scanned=some (if bit then 1 else 2) := by
    simp [next,cfg,Configuration.scanned,Streaming.read_append]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next 0 (if bit then 1 else 2) _ (by rfl) hn)

theorem round (pre tail out : List Bool) (index count : ℕ) :
    ∃ time≤CloseoutRowsRawAtomRound.budget index+1,Timed machine time
      (entry 1 (pre++true::tail) pre.length index count out)
      (entry 0 (pre++true::tail) (pre.length+1) (index+1) (count+1)
        (out++ExtIncidence.monomialWord [index])) := by
  obtain ⟨r,hr,rh,rt,_rs⟩:=CloseoutRowsRawAtomRound.round_run pre tail out index count
  obtain ⟨time,ht,trace⟩:=call_receipt sizes programs 0 next 1 0 _ _ r hr (by rfl)
  have he : RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes=
      cfg (programs 0).start (pre++true::tail) (pre.length+1) (index+1+1) (count+1)
        (out++ExtIncidence.monomialWord [index]) := by
    apply configuration_ext
    · rfl
    · simpa only [RecoveryCalls.restarted,cfg,Nat.add_assoc] using rh
    · simpa only [RecoveryCalls.restarted,cfg,Nat.add_assoc] using rt
  rw [he] at trace
  exact ⟨time,ht,trace⟩

theorem stop (source out : List Bool) (pos index count : ℕ) :
    ∃ time≤2,Timed machine time (entry 2 source pos index count out)
      (final source pos index count (out++[false])) := by
  obtain ⟨r,hr,rf,_rs⟩:=CloseoutRowsRawAtomRound.mark_run false source pos (index+1) count out
  obtain ⟨time,ht,trace⟩:=stop_receipt sizes programs 0 next 2 1 _ r hr (by rfl)
  rw [rf] at trace
  exact ⟨time,ht,trace⟩

theorem remaining (n offset count : ℕ) (pre tail out : List Bool) :
    ∃ time≤budget offset n,Timed machine time
      (entry 0 (pre++List.replicate n true++false::tail) pre.length offset count out)
      (final (pre++List.replicate n true++false::tail) (pre.length+n) (offset+n) (count+n)
        (out++ExtIncidence.stream (indices offset n))) := by
  induction n generalizing offset count pre out with
  | zero=>
    obtain ⟨time,ht,trace⟩:=stop (pre++false::tail) out pre.length offset count
    have h:=(probe pre tail false offset count out).trans trace
    exact ⟨1+time,by unfold budget;omega,by simpa [indices,ExtIncidence.stream] using h⟩
  | succ n ih=>
    let suffix:=List.replicate n true++false::tail
    obtain ⟨first,hfirst,hstep⟩:=round pre suffix out offset count
    obtain ⟨rest,hrest,hrestTrace⟩:=ih (offset+1) (count+1) (pre++[true])
      (out++ExtIncidence.monomialWord [offset])
    have source : (pre++[true])++List.replicate n true++false::tail=pre++true::suffix := by
      simp [suffix,List.append_assoc]
    simp only [List.length_append,List.length_singleton,source] at hrestTrace
    have h:=(probe pre suffix true offset count out).trans (hstep.trans hrestTrace)
    have hsrc : pre++true::suffix=pre++List.replicate (n+1) true++false::tail := by
      simp [suffix,List.replicate_succ,List.append_assoc]
    have hword : ExtIncidence.stream (indices offset (n+1))=
        ExtIncidence.monomialWord [offset]++ExtIncidence.stream (indices (offset+1) n) := by
      simp only [indices,List.range'_succ,List.map_cons,ExtIncidence.stream_cons]
    refine ⟨1+(first+rest),?_,?_⟩
    · unfold budget CloseoutRowsRawAtomRound.budget at *
      nlinarith
    · simpa only [hsrc,hword,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem range_run (offset n count : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (budget offset n)
      (entry 0 (UnaryTemplate.tape n) 1 offset count out)=some r ∧
      r.final=final (UnaryTemplate.tape n) (n+1) (offset+n) (count+n)
        (out++ExtIncidence.stream (indices offset n)) ∧ r.steps≤budget offset n := by
  obtain ⟨time,ht,trace⟩:=remaining n offset count [false] [] out
  have trace' : Timed machine time (entry 0 (UnaryTemplate.tape n) 1 offset count out)
      (final (UnaryTemplate.tape n) (n+1) (offset+n) (count+n)
        (out++ExtIncidence.stream (indices offset n))) := by
    simpa only [UnaryTemplate.tape,List.singleton_append,List.cons_append,List.nil_append,
      List.length_singleton,Nat.add_comm] using trace
  obtain ⟨r,hr,rf,rs⟩:=trace'.run (by simp [machine,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel machine time (budget offset n-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨r,more,rf,rs.le.trans ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomLoop
