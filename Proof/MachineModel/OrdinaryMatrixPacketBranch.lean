import Proof.MachineModel.OrdinaryMatrixPacketHeader

/-! The positive branch consumes the first physical p mark, then runs
all packets while preserving the header's external work and cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketBranch
open LocalBitMultitape RecoveryExecution MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def slots (a : WilliamsAlgorithm) (E : ℕ)
    (i : Fin (MatrixPacketRestore.tapes a E+1)) : Fin (MatrixPacketHeader.tapes a E) :=
  ⟨i.val,by have h:=i.isLt; unfold MatrixPacketHeader.tapes; omega⟩
theorem slots_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (slots a E) := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin (MatrixPacketHeader.tapes a E) => k.val) h)
theorem slots_old (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixPacketRestore.tapes a E)) :
    slots a E (i.castAdd 1)=MatrixPacketHeader.old a E i := rfl
theorem slots_driver (a : WilliamsAlgorithm) (E : ℕ) :
    slots a E ((0 : Fin 1).natAdd (MatrixPacketRestore.tapes a E))=MatrixPacketHeader.extra a E 0 := rfl
noncomputable def raised (a : WilliamsAlgorithm) (E : ℕ) (heads : Fin (MatrixPacketHeader.tapes a E) → ℕ)
    (i : Fin (MatrixPacketHeader.tapes a E)) := if i=MatrixPacketHeader.extra a E 0 then heads i+1 else heads i
noncomputable def advance (a : WilliamsAlgorithm) (E : ℕ) : Machine (MatrixPacketHeader.tapes a E) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=MatrixPacketHeader.extra a E 0 then .right else .stay⟩ else none
noncomputable def positive (a : WilliamsAlgorithm) (E C : ℕ) :=
  RecoveryFocus.machine (slots a E) (MatrixPacketPositive.machine a E C)
noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) := Composition.machine (advance a E) (positive a E C)
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) := 2+MatrixPacketPositive.budget a E C r

theorem advance_run (a : WilliamsAlgorithm) (E : ℕ) (heads : Fin (MatrixPacketHeader.tapes a E) → ℕ)
    (ambient : Fin (MatrixPacketHeader.tapes a E) → List Bool) : ∃ actual,
    runFrom (advance a E) 1 (RecoveryCalls.restarted (advance a E) heads ambient)=some actual ∧
    actual.final.heads=raised a E heads ∧ actual.final.tapes=ambient ∧ actual.steps=1 := by
  have hstep : step (advance a E) (RecoveryCalls.restarted (advance a E) heads ambient)=
      some ⟨1,raised a E heads,ambient⟩ := by
    simp only [step,advance,RecoveryCalls.restarted,Fin.val_zero,if_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=MatrixPacketHeader.extra a E 0 <;> simp [applyAction,raised,hi,HeadMove.apply]
    · rfl
  obtain ⟨actual,ha,hf,hs⟩:=(Timed.single (by rfl) hstep).run (by rfl)
  exact ⟨actual,ha,by rw [hf],by rw [hf],hs⟩

theorem restart_fields {t s k : ℕ} (p : Machine t k) (c : Configuration t s)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (hh : c.heads=heads) (ht : c.tapes=tapes) :
    RecoveryCalls.restarted p heads tapes=Composition.restart c p.start := by
  apply configuration_ext
  · rfl
  · exact hh.symm
  · exact ht.symm

theorem selected_fields (a : WilliamsAlgorithm) (E C : ℕ) (r : Request)
    (heads : Fin (MatrixPacketHeader.tapes a E) → ℕ) (ambient : Fin (MatrixPacketHeader.tapes a E) → List Bool)
    (oldT : ∀ i,ambient (MatrixPacketHeader.old a E i)=MatrixPacketColdPrepare.cold a E r i)
    (oldH : ∀ i,heads (MatrixPacketHeader.old a E i)=0)
    (pT : ambient (MatrixPacketHeader.extra a E 0)=UnaryTemplate.tape r.p)
    (pH : heads (MatrixPacketHeader.extra a E 0)=1) :
    (∀ j,ambient (slots a E j)=(MatrixPacketPositive.input a E C r).tapes j) ∧
    (∀ j,raised a E heads (slots a E j)=(MatrixPacketPositive.input a E C r).heads j) := by
  have hnot (i : Fin (MatrixPacketRestore.tapes a E)) : MatrixPacketHeader.old a E i≠MatrixPacketHeader.extra a E 0 := by
    intro he
    have hv:=congrArg (fun k : Fin (MatrixPacketHeader.tapes a E) => k.val) he
    change i.val=MatrixPacketRestore.tapes a E+0 at hv
    have h:=i.isLt
    omega
  constructor
  · intro j
    refine Fin.addCases (m := MatrixPacketRestore.tapes a E) (n := 1) (fun i => ?_) (fun i => ?_) j
    · exact (oldT i).trans (Fin.addCases_left (motive := fun _ => List Bool)
        (left := MatrixPacketColdPrepare.cold a E r) (right := fun _ : Fin 1 => UnaryTemplate.tape r.p) i).symm
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact pT.trans (Fin.addCases_right (motive := fun _ => List Bool)
        (left := MatrixPacketColdPrepare.cold a E r) (right := fun _ : Fin 1 => UnaryTemplate.tape r.p) 0).symm
  · intro j
    refine Fin.addCases (m := MatrixPacketRestore.tapes a E) (n := 1) (fun i => ?_) (fun i => ?_) j
    · rw [slots_old,raised,if_neg (hnot i),oldH]
      exact (Fin.addCases_left (motive := fun _ => ℕ) (left := fun _ => 0) (right := fun _ : Fin 1 => 2) i).symm
    · have hi : i=0 := Subsingleton.elim _ _
      subst i
      rw [slots_driver,raised,if_pos rfl,pH]
      exact (Fin.addCases_right (motive := fun _ => ℕ) (left := fun _ => 0) (right := fun _ : Fin 1 => 2) 0).symm

theorem focused_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (hp : 0<r.p)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤MatrixPacketBootstrapState.capacity E C r)
    (heads : Fin (MatrixPacketHeader.tapes a E) → ℕ) (ambient : Fin (MatrixPacketHeader.tapes a E) → List Bool)
    (selectedT : ∀ j,ambient (slots a E j)=(MatrixPacketPositive.input a E C r).tapes j)
    (selectedH : ∀ j,heads (slots a E j)=(MatrixPacketPositive.input a E C r).heads j) : ∃ actual,
      runFrom (positive a E C) (MatrixPacketPositive.budget a E C r)
        (RecoveryCalls.restarted (positive a E C) heads ambient)=some actual ∧
      actual.final.tapes (MatrixPacketHeader.old a E (MatrixPacketRestoreDock.slots a E (MatrixPacketState.output a)))=MatrixScoreBatch.output r ∧
      actual.final.tapes (MatrixPacketHeader.old a E (MatrixPacketRestoreControls.controls a E 2))=physicalInput r ∧
      actual.final.heads (MatrixPacketHeader.old a E (MatrixPacketRestoreControls.controls a E 2))=0 ∧
      actual.steps≤MatrixPacketPositive.budget a E C r := by
  obtain ⟨base,hb,bout,bsrc,bsh,bs⟩:=MatrixPacketPositive.output_run a E C r hp hcap
  have hi : RecoveryFocus.config (slots a E) heads ambient (MatrixPacketPositive.input a E C r)=
      RecoveryCalls.restarted (positive a E C) heads ambient :=
    WilliamsSourceCrop.focus_same (slots a E) (RecoveryCalls.restarted (positive a E C) heads ambient)
      (MatrixPacketPositive.input a E C r) selectedH selectedT
  obtain ⟨actual,ha,hf,hs⟩:=RecoveryFocus.run_config (slots a E) (slots_injective a E) (MatrixPacketPositive.machine a E C)
    heads ambient _ (MatrixPacketPositive.input a E C r) base hb
  rw [hi] at ha
  have localT (j : Fin (MatrixPacketRestore.tapes a E+1)) : actual.final.tapes (slots a E j)=base.final.tapes j := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E)]
  have localH (j : Fin (MatrixPacketRestore.tapes a E+1)) : actual.final.heads (slots a E j)=base.final.heads j := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a E) (slots_injective a E)]
  exact ⟨actual,ha,(localT _).trans bout,(localT _).trans bsrc,(localH _).trans bsh,hs.trans_le bs⟩

theorem branch_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (hp : 0<r.p)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤MatrixPacketBootstrapState.capacity E C r)
    (heads : Fin (MatrixPacketHeader.tapes a E) → ℕ) (ambient : Fin (MatrixPacketHeader.tapes a E) → List Bool)
    (oldT : ∀ i,ambient (MatrixPacketHeader.old a E i)=MatrixPacketColdPrepare.cold a E r i)
    (oldH : ∀ i,heads (MatrixPacketHeader.old a E i)=0)
    (pT : ambient (MatrixPacketHeader.extra a E 0)=UnaryTemplate.tape r.p)
    (pH : heads (MatrixPacketHeader.extra a E 0)=1) : ∃ actual,
      runFrom (machine a E C) (budget a E C r) (RecoveryCalls.restarted (machine a E C) heads ambient)=some actual ∧
      actual.final.tapes (MatrixPacketHeader.old a E (MatrixPacketRestoreDock.slots a E (MatrixPacketState.output a)))=MatrixScoreBatch.output r ∧
      actual.final.tapes (MatrixPacketHeader.old a E (MatrixPacketRestoreControls.controls a E 2))=physicalInput r ∧
      actual.final.heads (MatrixPacketHeader.old a E (MatrixPacketRestoreControls.controls a E 2))=0 ∧
      actual.steps≤budget a E C r := by
  obtain ⟨first,hfirst,fh,ft,fs⟩:=advance_run a E heads ambient
  obtain ⟨selectedT,selectedH⟩:=selected_fields a E C r heads ambient oldT oldH pT pH
  obtain ⟨last,hl,lo,lt,lh,ls⟩:=focused_run a E C r hp hcap (raised a E heads) ambient selectedT selectedH
  have hi:=restart_fields (positive a E C) first.final (raised a E heads) ambient fh ft
  rw [hi] at hl
  have joined:=Composition.run_join (advance a E) (positive a E C) _ _ _ first last hfirst hl
  exact ⟨Composition.joinedReceipt first last,joined,lo,lt,lh,
    by change first.steps+1+last.steps≤budget a E C r; unfold budget; omega⟩

end NearCubicWires.RepairOrdinary.MatrixPacketBranch
