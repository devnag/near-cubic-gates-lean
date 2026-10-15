import Proof.MachineModel.OrdinaryMatrixPacketRestoreControls

/-! The physical recurrent state of the sign/bit packet scheduler. Its
capacity and copy counters are produced by the cold entry and reused. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketState
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open MatrixPacketRestoreDock (slots)
open MatrixPacketRestoreControls (controls values)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def offset (a : WilliamsAlgorithm) : Fin (MatrixVariablePacketWorkspace.tapes a) :=
  (MatrixVariablePacket.offset a).castAdd 1
noncomputable def output (a : WilliamsAlgorithm) : Fin (MatrixVariablePacketWorkspace.tapes a) :=
  (MatrixVariablePacket.outputTape a).castAdd 1
structure State (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool) where
  heads : Fin (MatrixPacketRestore.tapes a E) → ℕ
  tapes : Fin (MatrixPacketRestore.tapes a E) → List Bool
  bounded : ∀ i,MatrixVariablePacketWorkspace.working a i → (tapes (slots a E i)).length≤cap
  workHeads : ∀ i,MatrixVariablePacketWorkspace.working a i → heads (slots a E i)=0
  offsetT : tapes (slots a E (offset a))=UnaryTemplate.tape (2*bit)
  offsetH : heads (slots a E (offset a))=1
  outputT : tapes (slots a E (output a))=out
  outputH : heads (slots a E (output a))=out.length
  controlT : ∀ j,tapes (controls a E j)=values cap (word r) j
  controlH : ∀ j,heads (controls a E j)=0

noncomputable def data (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (negative : Bool) (st : State a E cap r bit out) :=
  RecoveryCalls.restarted (MatrixPacketReuse.machine a E negative) st.heads st.tapes

theorem entry_heads (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    st.heads (slots a E i)=(MatrixVariablePacketReset.input a r bit out).heads i := by
  by_cases h0 : i.val=424
  · have he : i=offset a := Fin.ext h0
    subst i
    apply st.offsetH.trans
    symm
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (motive := fun _ => ℕ)
      (MatrixVariablePacket.input a r bit out).heads (fun _ => 0)) ((MatrixVariablePacket.offset a).castAdd 1)=1
    refine Eq.trans (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixVariablePacket.input a r bit out).heads) (right := fun _ : Fin 1 => 0)
      (MatrixVariablePacket.offset a)) ?_
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (motive := fun _ => ℕ)
      (MatrixVariableProduct.input a r bit).heads (MatrixVariableCount.extraHeads out))
        (((424 : Fin 425).castAdd (MatrixWilliamsProduct.source a).program.tapeCount).castAdd 17)=1
    refine Eq.trans (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixVariableProduct.input a r bit).heads) (right := MatrixVariableCount.extraHeads out)
      ((424 : Fin 425).castAdd (MatrixWilliamsProduct.source a).program.tapeCount)) ?_
    change (Fin.addCases (m := 425) (n := (MatrixWilliamsProduct.source a).program.tapeCount) (motive := fun _ => ℕ)
      (MatrixVariableInput.input r bit).heads (fun _ => 0))
        ((424 : Fin 425).castAdd (MatrixWilliamsProduct.source a).program.tapeCount)=1
    refine Eq.trans (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixVariableInput.input r bit).heads) (right := fun _ : Fin (MatrixWilliamsProduct.source a).program.tapeCount => 0)
      (424 : Fin 425)) ?_
    change (MatrixVariablePlane.input r bit).heads 424=1
    rw [MatrixVariablePlane.input_heads]
    rfl
  by_cases h1 : i.val=MatrixVariableProduct.tapes a+16
  · have he : i=output a := Fin.ext h1
    subst i
    apply st.outputH.trans
    symm
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (motive := fun _ => ℕ)
      (MatrixVariablePacket.input a r bit out).heads (fun _ => 0)) ((MatrixVariablePacket.outputTape a).castAdd 1)=out.length
    refine Eq.trans (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixVariablePacket.input a r bit out).heads) (right := fun _ : Fin 1 => 0)
      (MatrixVariablePacket.outputTape a)) ?_
    change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (motive := fun _ => ℕ)
      (MatrixVariableProduct.input a r bit).heads (MatrixVariableCount.extraHeads out))
        ((16 : Fin 17).natAdd (MatrixVariableProduct.tapes a))=out.length
    refine Eq.trans (Fin.addCases_right (motive := fun _ => ℕ)
      (left := (MatrixVariableProduct.input a r bit).heads) (right := MatrixVariableCount.extraHeads out)
      (16 : Fin 17)) ?_
    simp [MatrixVariableCount.extraHeads]
  have hi : MatrixVariablePacketWorkspace.working a i := ⟨h0,h1⟩
  exact (st.workHeads i hi).trans (MatrixVariablePacketWorkspace.entry_bounds a r bit out i hi).1.symm

theorem entry_data (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) (i : Fin (MatrixVariablePacketWorkspace.tapes a))
    (hi : ¬MatrixVariablePacketWorkspace.working a i) :
    st.tapes (slots a E i)=(MatrixVariablePacketReset.input a r bit out).tapes i := by
  by_cases h0 : i.val=424
  · have he : i=offset a := Fin.ext h0
    subst i
    apply st.offsetT.trans
    symm
    rw [MatrixPacketEntryForm.input_tapes]
    simp [offset,MatrixVariablePacket.offset]
  have h1 : i.val=MatrixVariableProduct.tapes a+16 := by
    unfold MatrixVariablePacketWorkspace.working at hi
    omega
  have he : i=output a := Fin.ext h1
  subst i
  apply st.outputT.trans
  symm
  rw [MatrixPacketEntryForm.input_tapes]
  have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  simp only [output,MatrixVariablePacket.outputTape,Fin.val_castAdd,Fin.val_natAdd]
  rw [if_neg (by omega),if_neg (by omega)]
  exact if_pos h1

theorem input_eq (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (negative : Bool) (st : State a E cap r bit out) :
    MatrixPacketReuse.input a E (2*(word r).length+1) (4*(word r).length+3) negative
      (fun i => st.heads (i.castAdd 2)) (fun i => st.tapes (i.castAdd 2))=
      data a E cap r bit out negative st := by
  apply configuration_ext
  · rfl
  · change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => ℕ)
      (fun i => st.heads (i.castAdd 2)) (fun _ => 0))=st.heads
    funext i
    refine Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]
    · rw [Fin.addCases_right]
      fin_cases j
      · exact (st.controlH 3).symm
      · exact (st.controlH 4).symm
  · change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
      (fun i => st.tapes (i.castAdd 2)) (MatrixPacketRestore.extras (2*(word r).length+1) (4*(word r).length+3)))=st.tapes
    funext i
    refine Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]
    · rw [Fin.addCases_right]
      fin_cases j
      · exact (st.controlT 3).symm
      · exact (st.controlT 4).symm

theorem clear_heads (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) (j : Fin (MatrixPacketWorkClear.count a+2)) :
    st.heads ((MatrixPacketWorkClear.slots a E j).castAdd 2)=0 := by
  refine Fin.addCases (m := MatrixPacketWorkClear.count a+1) (n := 1) (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (m := MatrixPacketWorkClear.count a) (n := 1) (fun k => ?_) (fun k => ?_) i
    · simp only [MatrixPacketWorkClear.slots,Fin.addCases_left]
      have he:=MatrixPacketBootstrapErase.work_eq_old a E k
      exact (congrArg (fun j => st.heads (j.castAdd 2)) he).trans
        (st.workHeads _ (MatrixPacketBootstrapErase.work_working a E k))
    · fin_cases k
      simp only [MatrixPacketWorkClear.slots,Fin.addCases_left,Fin.addCases_right]
      exact st.controlH 0
  · fin_cases i
    simp only [MatrixPacketWorkClear.slots,Fin.addCases_right]
    exact st.controlH 1

theorem state_run (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (negative : Bool) (st : State a E cap r bit out) (ht : bit<r.p)
    (hcap : MatrixVariablePacketWorkspace.footprint a r bit negative≤cap) :
    ∃ next : State a E cap r bit (out++packet r negative bit),∃ actual,
      runFrom (MatrixPacketReuse.machine a E negative) (MatrixPacketReuse.budget a r negative bit cap)
        (data a E cap r bit out negative st)=some actual ∧
      actual.final.heads=next.heads ∧ actual.final.tapes=next.tapes ∧
      actual.steps≤MatrixPacketReuse.budget a r negative bit cap := by
  obtain ⟨actual,ha,outT,outH,offT,offH,support,_,other,bs⟩ := MatrixPacketReuse.reuse_run a E cap (cap+1)
    (2*(word r).length+1) (4*(word r).length+3) r negative bit out
    (fun i => st.heads (i.castAdd 2)) (fun i => st.tapes (i.castAdd 2)) ht hcap
    (st.controlT 0) (st.controlT 1)
    (by intro j
        have he:=MatrixPacketBootstrapErase.work_eq_old a E j
        exact (congrArg (fun k => (st.tapes (k.castAdd 2)).length) he).le.trans
          (st.bounded _ (MatrixPacketBootstrapErase.work_working a E j)))
    (clear_heads a E cap r bit out st) (st.controlT 2) (st.controlH 2)
    (entry_heads a E cap r bit out st) (entry_data a E cap r bit out st)
  have ct (j : Fin 5) : actual.final.tapes (controls a E j)=values cap (word r) j :=
    (other _ (MatrixPacketRestoreControls.controls_outside a E j)).1.trans
      (MatrixPacketRestoreControls.output_controls a E cap (word r) _ j)
  have ch (j : Fin 5) : actual.final.heads (controls a E j)=0 := by
    have h:=(other _ (MatrixPacketRestoreControls.controls_outside a E j)).2
    fin_cases j
    · exact h.trans (Eq.trans (Fin.addCases_left (m := MatrixPacketWorkClear.tapes a E) (n := 2)
        (motive := fun _ => ℕ) (left := fun i => st.heads (i.castAdd 2)) (right := fun _ => 0) (MatrixPacketWorkClear.capTape a E)) (st.controlH 0))
    · exact h.trans (Eq.trans (Fin.addCases_left (m := MatrixPacketWorkClear.tapes a E) (n := 2)
        (motive := fun _ => ℕ) (left := fun i => st.heads (i.castAdd 2)) (right := fun _ => 0) (MatrixPacketWorkClear.logTape a E)) (st.controlH 1))
    · exact h.trans (Eq.trans (Fin.addCases_left (m := MatrixPacketWorkClear.tapes a E) (n := 2)
        (motive := fun _ => ℕ) (left := fun i => st.heads (i.castAdd 2)) (right := fun _ => 0) (MatrixPacketWorkClear.original a E)) (st.controlH 2))
    · exact h.trans (Fin.addCases_right (m := MatrixPacketWorkClear.tapes a E) (n := 2)
        (motive := fun _ => ℕ) (left := fun i => st.heads (i.castAdd 2)) (right := fun _ => 0) 0)
    · exact h.trans (Fin.addCases_right (m := MatrixPacketWorkClear.tapes a E) (n := 2)
        (motive := fun _ => ℕ) (left := fun i => st.heads (i.castAdd 2)) (right := fun _ => 0) 1)
  let next : State a E cap r bit (out++packet r negative bit) :=
    ⟨actual.final.heads,actual.final.tapes,(fun i hi => (support i hi).1.le),
      (fun i hi => (support i hi).2),offT,offH,outT,outH,ct,ch⟩
  rw [input_eq a E cap r bit out negative st] at ha
  exact ⟨next,actual,ha,rfl,rfl,bs⟩

end NearCubicWires.RepairOrdinary.MatrixPacketState
