import Proof.MachineModel.OrdinaryMatrixVariableDimensions

/-! Actual externally indexed signed plane through canonical Williams
framing. Only the physically supplied bit-offset sentinel lies outside cold
workspace; its head and exact value survive for the all-plane loop. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableInput
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 425 := ![410,409,420,407,394,422,423]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots MatrixWilliamsFrame.machine
noncomputable def machine (negative : Bool) := Composition.machine (MatrixVariableDimensions.machine negative) last
noncomputable def input (r : Request) (bit : ℕ) := Composition.leftConfig 24 (MatrixVariableDimensions.input r bit)
noncomputable def word (r : Request) (negative : Bool) (bit : ℕ) :=
  natWord r.U++MatrixSignedPlane.plane r negative bit++MatrixRightPlaneNative.plane r
noncomputable def budget (r : Request) := MatrixVariableDimensions.budget r+1+(6*(2*r.d+3)+12*(r.U*r.Capacity)+38)

theorem input_run (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) : ∃ actual,
    runFrom (machine negative) (budget r) (input r bit)=some actual ∧
    actual.final.tapes 422=frame (word r negative bit) ∧ actual.final.heads 422=0 ∧
    (∀ j,actual.final.tapes (MatrixVariableDimensions.selected j)=MatrixVariableDimensions.values r negative bit j) ∧
    (∀ j,actual.final.heads (MatrixVariableDimensions.selected j)=MatrixVariableDimensions.heads j) ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,blank,bs⟩ := MatrixVariableDimensions.dimensions_run r negative bit ht
  obtain ⟨body,hr,bodyT,bodyH,bodyS⟩ := MatrixWilliamsFrame.frame_run (natWord r.U)
    (MatrixSignedPlane.plane r negative bit) (MatrixRightPlaneNative.plane r) (r.U*r.Capacity)
    (MatrixWilliamsInput.left_length r negative bit) (MatrixWilliamsInput.right_length r)
  rw [MatrixWilliamsInput.header_length] at hr bodyS
  let entry := initialConfiguration MatrixWilliamsFrame.machine (MatrixWilliamsFrame.resetInput (natWord r.U)
    (MatrixSignedPlane.plane r negative bit) (MatrixRightPlaneNative.plane r) (r.U*r.Capacity))
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes entry=Composition.restart base.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact bh 8
      · exact bh 7
      · exact bh 9
      · exact bh 4
      · exact bh 5
      · exact (blank 0).2
      · exact (blank 1).2
    · intro j; fin_cases j
      · change base.final.tapes 410=UnaryTemplate.tape (natWord r.U).length
        rw [MatrixWilliamsInput.header_length]
        exact bt 8
      · exact bt 7
      · exact bt 9
      · exact bt 4
      · exact bt 5
      · exact (blank 0).1
      · exact (blank 1).1
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixWilliamsFrame.machine
    base.final.heads base.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join (MatrixVariableDimensions.machine negative) last _ _ _ base focused hb hf
  have localT (j : Fin 7) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 7) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have retained (i : Fin 425) (hn : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=base.final.tapes i ∧ focused.final.heads i=base.final.heads i := by
    rw [ff]; simp [RecoveryFocus.config,hn]
  refine ⟨Composition.joinedReceipt base focused,hj,(localT 5).trans (bodyT 5),(localH 5).trans (bodyH 5),?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (retained 12 (by decide)).1.trans (bt 0)
    · exact (retained 22 (by decide)).1.trans (bt 1)
    · exact (retained 400 (by decide)).1.trans (bt 2)
    · exact (retained 200 (by decide)).1.trans (bt 3)
    · exact (localT 3).trans (bodyT 3)
    · exact (localT 4).trans (bodyT 4)
    · exact (retained 424 (by decide)).1.trans (bt 6)
    · exact (localT 1).trans (bodyT 1)
    · have he := (localT 0).trans (bodyT 0)
      change focused.final.tapes 410=UnaryTemplate.tape (natWord r.U).length at he
      rw [MatrixWilliamsInput.header_length] at he
      exact he
    · exact (localT 2).trans (bodyT 2)
  · intro j; fin_cases j
    · exact (retained 12 (by decide)).2.trans (bh 0)
    · exact (retained 22 (by decide)).2.trans (bh 1)
    · exact (retained 400 (by decide)).2.trans (bh 2)
    · exact (retained 200 (by decide)).2.trans (bh 3)
    · exact (localH 3).trans (bodyH 3)
    · exact (localH 4).trans (bodyH 4)
    · exact (retained 424 (by decide)).2.trans (bh 6)
    · exact (localH 1).trans (bodyH 1)
    · exact (localH 0).trans (bodyH 0)
    · exact (localH 2).trans (bodyH 2)
  · change base.steps+1+focused.steps≤budget r
    rw [fs,bodyS]
    unfold budget
    omega

theorem budget_eq (r : Request) : budget r=MatrixWilliamsInput.budget r := rfl

end NearCubicWires.RepairOrdinary.MatrixVariableInput
