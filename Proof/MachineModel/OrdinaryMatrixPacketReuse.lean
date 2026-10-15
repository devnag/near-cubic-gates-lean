import Proof.MachineModel.OrdinaryMatrixPacketReusableCall

/-! The reusable actual ordinary packet body: erase bounded local work,
restore the retained request, and execute the indexed Williams packet.
All external dimensions, copy counters and live cursors survive physically. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketReuse
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
open MatrixWilliamsProduct (source)
open MatrixPacketRestoreDock (slots slots_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last (a : WilliamsAlgorithm) (E : ℕ) (negative : Bool) :=
  RecoveryFocus.machine (slots a E) (MatrixVariablePacketReset.machine a negative)
noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) (negative : Bool) :=
  Composition.machine (MatrixPacketRestore.machine a E) (last a E negative)
noncomputable def input (a : WilliamsAlgorithm) (E left right : ℕ) (negative : Bool)
    (heads : Fin (MatrixPacketWorkClear.tapes a E) → ℕ) (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool) :=
  Composition.restart (MatrixPacketRestore.input a E left right heads ambient) (machine a E negative).start
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit cap : ℕ) :=
  MatrixPacketRestore.budget (word r) cap+1+MatrixVariablePacketReset.budget a r bit negative

theorem reuse_run (a : WilliamsAlgorithm) (E cap log left right : ℕ) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (heads : Fin (MatrixPacketWorkClear.tapes a E) → ℕ) (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool)
    (ht : bit<r.p) (hcap : MatrixVariablePacketWorkspace.footprint a r bit negative≤cap)
    (hd : ambient (MatrixPacketWorkClear.capTape a E)=List.replicate cap true)
    (hl : ambient (MatrixPacketWorkClear.logTape a E)=List.replicate log false)
    (hb : ∀ j,(ambient (MatrixPacketWorkClear.work a E j)).length≤cap)
    (hh : ∀ j,heads (MatrixPacketWorkClear.slots a E j)=0)
    (hs : ambient (MatrixPacketWorkClear.original a E)=physicalInput r)
    (hsh : heads (MatrixPacketWorkClear.original a E)=0)
    (hphead : ∀ i,heads (MatrixPacketBootstrapErase.old a E i)=(MatrixVariablePacketReset.input a r bit out).heads i)
    (hpdata : ∀ i,¬MatrixVariablePacketWorkspace.working a i →
      ambient (MatrixPacketBootstrapErase.old a E i)=(MatrixVariablePacketReset.input a r bit out).tapes i) : ∃ actual,
    runFrom (machine a E negative) (budget a r negative bit cap) (input a E left right negative heads ambient)=some actual ∧
    actual.final.tapes (slots a E ((MatrixVariablePacket.outputTape a).castAdd 1))=out++packet r negative bit ∧
    actual.final.heads (slots a E ((MatrixVariablePacket.outputTape a).castAdd 1))=(out++packet r negative bit).length ∧
    actual.final.tapes (slots a E ((MatrixVariablePacket.offset a).castAdd 1))=UnaryTemplate.tape (2*bit) ∧
    actual.final.heads (slots a E ((MatrixVariablePacket.offset a).castAdd 1))=1 ∧
    (∀ i,MatrixVariablePacketWorkspace.working a i →
      (actual.final.tapes (slots a E i)).length=cap ∧ actual.final.heads (slots a E i)=0) ∧
    (∀ j,actual.final.tapes (slots a E ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1))=
      ZeroPadding.pad (MatrixVariablePacketWorkspace.caps a cap ((((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1))
        (MatrixVariableDimensions.values r negative bit j)) ∧
    (∀ i,(∀ j,slots a E j≠i) →
      actual.final.tapes i=MatrixPacketRestore.output a E cap log left right (word r) ambient i ∧
      actual.final.heads i=(Fin.addCases (motive := fun _ => ℕ) heads (fun _ : Fin 2 => 0)) i) ∧
    actual.steps≤budget a r negative bit cap := by
  obtain ⟨prepared,hr,rt,rh,rs⟩ := MatrixPacketRestore.restore_run a E cap log left right (word r) heads ambient hd hl hb hh hs hsh
  have ch : ∀ i,prepared.final.heads (slots a E i)=(MatrixVariablePacketReset.input a r bit out).heads i := by
    intro i
    have h:=congrFun rh (slots a E i)
    change prepared.final.heads (slots a E i)=
      (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => ℕ) heads (fun _ => 0))
        ((MatrixPacketBootstrapErase.old a E i).castAdd 2) at h
    rw [Fin.addCases_left] at h
    exact h.trans (hphead i)
  have ct : ∀ i,prepared.final.tapes (slots a E i)=
      (ZeroPadding.config (MatrixVariablePacketWorkspace.caps a cap) (MatrixVariablePacketReset.input a r bit out)).tapes i := by
    intro i
    exact (congrFun rt (slots a E i)).trans
      (MatrixPacketPreparedEntry.tapes a E cap log left right r bit out ambient hpdata i)
  obtain ⟨focused,hf,outT,outH,offT,offH,support,fields,other,bs⟩ :=
    MatrixPacketReusableCall.call_run a E cap r negative bit out prepared.final ht hcap ch ct
  have joined := Composition.run_join (MatrixPacketRestore.machine a E) (last a E negative)
    _ _ _ prepared focused hr hf
  refine ⟨Composition.joinedReceipt prepared focused,joined,outT,outH,offT,offH,support,fields,?_,?_⟩
  · intro i no
    obtain ⟨kt,kh⟩ := other i no
    exact ⟨kt.trans (congrFun rt i),kh.trans (congrFun rh i)⟩
  · change prepared.steps+1+focused.steps≤_
    rw [rs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixPacketReuse
