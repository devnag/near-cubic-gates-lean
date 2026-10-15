import Proof.CaseAnalysis.WitnessNatMeaning

namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reader_retains (fields : List (List Bool)) (passed : Bool)
    (r : ExecutionReceipt 5 8) (hr : run reader (time fields) (input fields passed)=some r) :
    r.final.tapes 0=FieldList.stream fields ∧
      r.final.tapes 1=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      r.final.tapes 4=[passed && fields.all good] := by
  obtain ⟨a,ha,hfinal,_⟩:=boot_run fields passed
  obtain ⟨b,hb,bfinal,_⟩:=(fields_timed [] fields [] [false] [] passed true).run (by rfl)
  have he:Composition.restart a.final machine.start=
      cfg 0 (FieldList.stream fields) (RepairSource.VerifierDecoding.CompareMachine.word fields.length)
        0 1 [] passed true:=by rw [hfinal];rfl
  simp only [List.nil_append,List.append_nil,List.length_nil] at hb
  change runFrom machine ((FieldList.stream fields).length+fields.length+1)
    (cfg 0 (FieldList.stream fields) (RepairSource.VerifierDecoding.CompareMachine.word fields.length)
      0 1 [] passed true)=some b at hb
  rw [←he] at hb
  have h:=Composition.run_join boot machine 1 _ _ a b ha hb
  change run reader (1+1+((FieldList.stream fields).length+fields.length+1)) (input fields passed)=some _ at h
  rw [show 1+1+((FieldList.stream fields).length+fields.length+1)=time fields by unfold time;omega] at h
  have eqr:r=Composition.joinedReceipt a b:=Option.some.inj (hr.symm.trans h)
  rw [eqr]
  change b.final.tapes 0=_ ∧ b.final.tapes 1=_ ∧ b.final.tapes 4=_
  rw [bfinal]
  simp only [cfg,List.nil_append,List.append_nil]
  exact ⟨rfl,rfl,rfl⟩

def readyMachine:=Rewind.machine reader
def readyInput (fields : List (List Bool)) (passed : Bool) : Fin 6→List Bool :=
  Fin.addCases (motive:=fun _ : Fin (5+1)=>List Bool) (input fields passed) (fun _=>[])
def readyTime (fields : List (List Bool)):=2*time fields+2

theorem ready_full (fields : List (List Bool)) (passed : Bool) : ∃ output,
    ClockJoin.ReadyRun readyMachine (readyTime fields) (readyInput fields passed) output ∧
      output 0=FieldList.stream fields ∧
      output 1=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      output 2=frame (fields.map lower) ∧
      output 3=[passed && fields.all good && last true fields] ∧
      output 4=[passed && fields.all good] := by
  obtain ⟨base,hb,hs,hout,hflag⟩:=reader_run fields passed
  obtain ⟨hsource,hcount,hvector⟩:=reader_retains fields passed base hb
  obtain ⟨r,hr,ht,_,hh,hsteps,_⟩:=Rewind.Workspace.reset_workspace reader _ _ base hb 0
  change run readyMachine (2*base.steps+2) (readyInput fields passed)=some r at hr
  rw [hs] at hr hsteps
  refine ⟨r.final.tapes,⟨r,hr,rfl,hh,hsteps.le⟩,?_,?_,?_,?_,?_⟩
  · exact (ht 0).trans hsource
  · exact (ht 1).trans hcount
  · exact (ht 2).trans hout
  · exact (ht 3).trans hflag
  · exact (ht 4).trans hvector

theorem ready (fields : List (List Bool)) (passed : Bool) : ∃ output,
    ClockJoin.ReadyRun readyMachine (readyTime fields) (readyInput fields passed) output ∧
      output 0=FieldList.stream fields ∧
      output 1=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      output 2=frame (fields.map lower) ∧
      output 3=[passed && fields.all good && last true fields] := by
  obtain ⟨output,hr,h0,h1,h2,h3,_⟩:=ready_full fields passed
  exact ⟨output,hr,h0,h1,h2,h3⟩

theorem field_stream_length (fields : List (List Bool)) :
    (FieldList.stream fields).length=PCPSerializerMass.mass fields := by
  induction fields with
  | nil=>rfl
  | cons field fields ih=>
    simp only [FieldList.stream_cons,List.length_append,frame_length,PCPSerializerMass.mass,
      List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]

theorem raw_time_bound (bits : List Bool) : readyTime (Reencode.fields bits) ≤ 16*(bits.length+1)^2 := by
  have hc:=Reencode.count_bound bits
  change (PCPPNativeCanonicalTree.tree (RadixSemantics.value bits)).atoms.length ≤ bits.length+1 at hc
  have hm:=Nat.mul_le_mul_right (2*bits.length+1) hc
  unfold readyTime time
  rw [field_stream_length,Reencode.fields_mass]
  simp only [Reencode.fields,List.length_map]
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
