import Proof.CaseAnalysis.WitnessNumericEquality

/-! The inverse Boolean-field stream reader.  Its counted scan emits binary
payload bits and rejects non-Boolean atoms before any numeric arithmetic. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lower (field : List Bool) := field.headD false
def good : List Bool→Bool
  | []=>false
  | _::rest=> !(rest.any id)
def last (previous : Bool) : List (List Bool)→Bool
  | []=>previous
  | field::rest=>last (lower field) rest

def machine : Machine 5 6 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==5
  rule:=fun q bits=>if q.val=0 then
      if bits 1 then
        some ⟨1,![none,none,some true,none,none],![.stay,.right,.right,.stay,.stay]⟩
      else some ⟨5,![none,none,some false,some (bits 3 && bits 4),some (bits 3)],![.stay,.stay,.right,.stay,.stay]⟩
    else if q.val=1 then
      if bits 0 then some ⟨2,fun _=>none,![.right,.stay,.stay,.stay,.stay]⟩
      else some ⟨0,![none,none,some false,some false,some false],![.right,.stay,.right,.stay,.stay]⟩
    else if q.val=2 then
      some ⟨3,![none,none,some (bits 0),none,some (bits 0)],![.right,.stay,.right,.stay,.stay]⟩
    else if q.val=3 then
      some ⟨if bits 0 then 4 else 0,fun _=>none,![.right,.stay,.stay,.stay,.stay]⟩
    else if q.val=4 then
      some ⟨3,![none,none,none,some (bits 3 && !(bits 0)),none],![.right,.stay,.stay,.stay,.stay]⟩
    else none

def cfg (q : Fin 6) (source count : List Bool) (pos index : ℕ)
    (out : List Bool) (passed previous : Bool) : Configuration 5 6 :=
  ⟨q,![pos,index,out.length,0,0],![source,count,out,[passed],[previous]]⟩

theorem start_step (source out pre rest : List Bool) (pos : ℕ) (passed previous : Bool) :
    step machine (cfg 0 source (pre++true::rest) pos pre.length out passed previous)=
      some (cfg 1 source (pre++true::rest) pos (pre.length+1) (out++[true]) passed previous) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,write_append]

theorem stop_step (source count out : List Bool) (pos index : ℕ) (passed previous : Bool)
    (h : readTapeBit count index=false) :
    step machine (cfg 0 source count pos index out passed previous)=
      some (cfg 5 source count pos index (out++[false]) (passed && previous) passed) := by
  simp [step,machine,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,write_append,readTapeBit,writeTapeBit]

theorem first_marker (pre rest count out : List Bool) (index : ℕ) (passed previous : Bool) :
    step machine (cfg 1 (pre++true::rest) count pre.length index out passed previous)=
      some (cfg 2 (pre++true::rest) count (pre.length+1) index out passed previous) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem empty_marker (pre rest count out : List Bool) (index : ℕ) (passed previous : Bool) :
    step machine (cfg 1 (pre++false::rest) count pre.length index out passed previous)=
      some (cfg 0 (pre++false::rest) count (pre.length+1) index (out++[false]) false false) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,write_append,writeTapeBit]

theorem first_payload (pre rest count out : List Bool) (index : ℕ) (passed previous bit : Bool) :
    step machine (cfg 2 (pre++bit::rest) count pre.length index out passed previous)=
      some (cfg 3 (pre++bit::rest) count (pre.length+1) index (out++[bit]) passed bit) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,write_append,writeTapeBit]

theorem tail_marker (pre rest count out : List Bool) (index : ℕ) (passed previous bit : Bool) :
    step machine (cfg 3 (pre++bit::rest) count pre.length index out passed previous)=
      some (cfg (if bit then 4 else 0) (pre++bit::rest) count (pre.length+1) index out passed previous) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem tail_payload (pre rest count out : List Bool) (index : ℕ) (passed previous bit : Bool) :
    step machine (cfg 4 (pre++bit::rest) count pre.length index out passed previous)=
      some (cfg 3 (pre++bit::rest) count (pre.length+1) index out (passed && !bit) previous) := by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,readTapeBit,writeTapeBit]

theorem tail_timed (pre bits rest count out : List Bool) (index : ℕ) (passed previous : Bool) :
    Timed machine (2*bits.length+1)
      (cfg 3 (pre++frame bits++rest) count pre.length index out passed previous)
      (cfg 0 (pre++frame bits++rest) count (pre.length+2*bits.length+1) index out
        (passed && !(bits.any id)) previous) := by
  induction bits generalizing pre passed with
  | nil=>simpa [frame,RepairOrdinary.frame] using
      Timed.single (by rfl) (tail_marker pre rest count out index passed previous false)
  | cons b bits ih=>
    have h0:=Timed.single (by rfl) (tail_marker pre (b::frame bits++rest) count out index passed previous true)
    have h1:=Timed.single (by rfl) (tail_payload (pre++[true]) (frame bits++rest) count out index passed previous b)
    have ht:=ih (pre++[true,b]) (passed && !b)
    have hs:(pre++[true,b])++frame bits++rest=pre++true::b::(frame bits++rest):=by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hs] at ht
    have h1':Timed machine 1
        (cfg 4 (pre++true::b::(frame bits++rest)) count (pre.length+1) index out passed previous)
        (cfg 3 (pre++true::b::(frame bits++rest)) count (pre++[true,b]).length index out (passed && !b) previous):=by
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,
        List.length_cons,List.length_nil,Nat.add_zero,Nat.add_assoc] using h1
    have hall:=h0.trans (h1'.trans ht)
    have htime:1+(1+(2*bits.length+1))=2*(b::bits).length+1:=by simp;omega
    rw [htime] at hall
    simpa [frame,RepairOrdinary.frame,List.length_append,List.any_cons,Bool.not_or,
      Bool.and_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem field_core (pre field rest count out : List Bool) (index : ℕ) (passed previous : Bool) :
    Timed machine (2*field.length+1)
      (cfg 1 (pre++frame field++rest) count pre.length index out passed previous)
      (cfg 0 (pre++frame field++rest) count (pre.length+2*field.length+1) index
        (out++[lower field]) (passed && good field) (lower field)) := by
  cases field with
  | nil=>simpa [frame,RepairOrdinary.frame,lower,good] using
      Timed.single (by rfl) (empty_marker pre rest count out index passed previous)
  | cons b bits=>
    have h0:=Timed.single (by rfl) (first_marker pre (b::frame bits++rest) count out index passed previous)
    have h1:=Timed.single (by rfl) (first_payload (pre++[true]) (frame bits++rest) count out index passed previous b)
    have ht:=tail_timed (pre++[true,b]) bits rest count (out++[b]) index passed b
    have hs:(pre++[true,b])++frame bits++rest=pre++true::b::(frame bits++rest):=by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hs] at ht
    have h1':Timed machine 1
        (cfg 2 (pre++true::b::(frame bits++rest)) count (pre.length+1) index out passed previous)
        (cfg 3 (pre++true::b::(frame bits++rest)) count (pre++[true,b]).length index (out++[b]) passed b):=by
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,
        List.length_cons,List.length_nil,Nat.add_zero,Nat.add_assoc] using h1
    have hall:=h0.trans (h1'.trans ht)
    have htime:1+(1+(2*bits.length+1))=2*(b::bits).length+1:=by simp;omega
    rw [htime] at hall
    simpa [frame,RepairOrdinary.frame,List.length_append,lower,good,
      Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem field_timed (pre field rest counterPre counterRest out : List Bool) (passed previous : Bool) :
    Timed machine (2*field.length+2)
      (cfg 0 (pre++frame field++rest) (counterPre++true::counterRest) pre.length counterPre.length out passed previous)
      (cfg 0 (pre++frame field++rest) (counterPre++true::counterRest)
        (pre.length+2*field.length+1) (counterPre.length+1) (out++[true,lower field])
        (passed && good field) (lower field)) := by
  have h0:=Timed.single (by rfl) (start_step (pre++frame field++rest) out counterPre counterRest pre.length passed previous)
  have ht:=field_core pre field rest (counterPre++true::counterRest) (out++[true]) (counterPre.length+1) passed previous
  have hall:=h0.trans ht
  rw [show 1+(2*field.length+1)=2*field.length+2 by omega] at hall
  simpa only [List.append_assoc,List.cons_append,List.nil_append,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using hall

end NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
