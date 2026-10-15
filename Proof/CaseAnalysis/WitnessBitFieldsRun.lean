import Proof.CaseAnalysis.WitnessBitFields
import Proof.CaseAnalysis.WitnessReencodeReady

/-! The retained unary leaf count drives one scan of the entire field stream.
Every field, including a malformed non-Boolean one, pays only its bit length. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
open LocalBitMultitape RecoveryExecution Streaming
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_timed (pre : List Bool) (fields : List (List Bool))
    (rest counterPre out : List Bool) (passed previous : Bool) :
    Timed machine ((FieldList.stream fields).length+fields.length+1)
      (cfg 0 (pre++FieldList.stream fields++rest) (counterPre++List.replicate fields.length true)
        pre.length counterPre.length out passed previous)
      (cfg 5 (pre++FieldList.stream fields++rest) (counterPre++List.replicate fields.length true)
        (pre.length+(FieldList.stream fields).length) (counterPre.length+fields.length)
        (out++frame (fields.map lower)) (passed && fields.all good && last previous fields)
        (passed && fields.all good)) := by
  induction fields generalizing pre counterPre out passed previous with
  | nil=>
    have hs:=stop_step (pre++rest) counterPre out pre.length counterPre.length passed previous
      (by simp [readTapeBit])
    simpa [last,frame,RepairOrdinary.frame] using Timed.single (by rfl) hs
  | cons field fields ih=>
    have h0:=field_timed pre field (FieldList.stream fields++rest) counterPre
      (List.replicate fields.length true) out passed previous
    have ht:=ih (pre++frame field) (counterPre++[true]) (out++[true,lower field])
      (passed && good field) (lower field)
    have hs:(pre++frame field)++FieldList.stream fields++rest=
        pre++frame field++(FieldList.stream fields++rest):=by simp only [List.append_assoc]
    have hc:(counterPre++[true])++List.replicate fields.length true=
        counterPre++true::List.replicate fields.length true:=by simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hs,hc] at ht
    have hm:(pre++frame field).length=pre.length+2*field.length+1:=by rw [List.length_append,frame_length];omega
    have hcounter:(counterPre++[true]).length=counterPre.length+1:=by simp
    rw [hm,hcounter] at ht
    have hall:=h0.trans ht
    have htime:(2*field.length+2)+((FieldList.stream fields).length+fields.length+1)=
        (FieldList.stream (field::fields)).length+(field::fields).length+1:=by
      simp only [FieldList.stream_cons,List.length_append,List.length_cons,frame_length]
      omega
    rw [htime] at hall
    simpa [FieldList.stream_cons,List.replicate_succ,List.length_append,frame_length,
      List.map_cons,frame,RepairOrdinary.frame,List.all_cons,last,Bool.and_assoc,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

def input (fields : List (List Bool)) (passed : Bool) : Fin 5→List Bool :=
  ![FieldList.stream fields,RepairSource.VerifierDecoding.CompareMachine.word fields.length,[],[passed],[]]

def boot : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,![none,none,none,none,some true],![.stay,.right,.stay,.stay,.stay]⟩ else none

def bootOut (fields : List (List Bool)) (passed : Bool) : Configuration 5 2 :=
  ⟨1,![0,1,0,0,0],![FieldList.stream fields,RepairSource.VerifierDecoding.CompareMachine.word fields.length,
    [],[passed],[true]]⟩

theorem boot_run (fields : List (List Bool)) (passed : Bool) : ∃ r,
    run boot 1 (input fields passed)=some r ∧ r.final=bootOut fields passed ∧ r.steps=1 := by
  have hs:step boot (initialConfiguration boot (input fields passed))=some (bootOut fields passed):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

def reader:=Composition.machine boot machine
def time (fields : List (List Bool)) := (FieldList.stream fields).length+fields.length+3

theorem reader_run (fields : List (List Bool)) (passed : Bool) : ∃ r,
    run reader (time fields) (input fields passed)=some r ∧ r.steps=time fields ∧
      r.final.tapes 2=frame (fields.map lower) ∧
      r.final.tapes 3=[passed && fields.all good && last true fields] := by
  obtain ⟨a,ha,hfinal,hsteps⟩:=boot_run fields passed
  have ht:=fields_timed [] fields [] [false] [] passed true
  have he:Composition.restart a.final machine.start=
      cfg 0 (FieldList.stream fields) (RepairSource.VerifierDecoding.CompareMachine.word fields.length)
        0 1 [] passed true:=by rw [hfinal];rfl
  obtain ⟨b,hb,bfinal,bsteps⟩:=ht.run (by rfl)
  simp only [List.nil_append,List.append_nil,List.length_nil] at hb
  change runFrom machine ((FieldList.stream fields).length+fields.length+1)
    (cfg 0 (FieldList.stream fields) (RepairSource.VerifierDecoding.CompareMachine.word fields.length)
      0 1 [] passed true)=some b at hb
  rw [←he] at hb
  have h:=Composition.run_join boot machine 1 _ _ a b ha hb
  change run reader (1+1+((FieldList.stream fields).length+fields.length+1)) (input fields passed)=some _ at h
  have heq:1+1+((FieldList.stream fields).length+fields.length+1)=time fields:=by unfold time;omega
  rw [heq] at h
  refine ⟨_,h,?_,?_,?_⟩
  · simp only [Composition.joinedReceipt,hsteps,bsteps,time]
    omega
  · rw [show (Composition.joinedReceipt a b).final=Composition.rightConfig 2 b.final by rfl,bfinal]
    rfl
  · rw [show (Composition.joinedReceipt a b).final=Composition.rightConfig 2 b.final by rfl,bfinal]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
