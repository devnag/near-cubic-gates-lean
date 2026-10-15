import Proof.MachineModel.OrdinaryMatrixVariablePlane

/-! Canonical header production on the actual externally indexed signed
plane body. Every bit-offset and p-loop control field is retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableHeader
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 425 := ![12,409,410,411]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots MatrixPowerHeader.machine
noncomputable def machine (negative : Bool) := Composition.machine (MatrixVariablePlane.machine negative) last
noncomputable def input (r : Request) (bit : ℕ) := Composition.leftConfig 9 (MatrixVariablePlane.input r bit)
noncomputable def budget (r : Request) := MatrixVariablePlane.budget r+1+(6*r.d+14)
def selected : Fin 9 → Fin 425 := ![12,22,400,200,407,394,424,409,410]
noncomputable def values (r : Request) (negative : Bool) (bit : ℕ) : Fin 9 → List Bool :=
  ![UnaryTemplate.tape r.d,UnaryTemplate.tape r.p,UnaryTemplate.tape r.U,UnaryTemplate.tape r.Capacity,
    MatrixSignedPlane.plane r negative bit,MatrixRightPlaneNative.plane r,UnaryTemplate.tape (2*bit),
    RepairRepresentation.natWord r.U,UnaryTemplate.tape (2*r.d+3)]
def heads : Fin 9 → ℕ := ![0,1,1,1,0,0,1,0,0]

theorem header_run (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) : ∃ actual,
    runFrom (machine negative) (budget r) (input r bit)=some actual ∧
    (∀ j,actual.final.tapes (selected j)=values r negative bit j) ∧
    (∀ j,actual.final.heads (selected j)=heads j) ∧
    (∀ i : Fin 12,actual.final.tapes ((i.castAdd 1).natAdd 412)=[] ∧ actual.final.heads ((i.castAdd 1).natAdd 412)=0) ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,blank,bs⟩ := MatrixVariablePlane.plane_run r negative bit ht
  obtain ⟨body,hr,b0,b1,b2,bodyH,bodyS⟩ := MatrixPowerHeader.header_run r.d
  let entry := initialConfiguration MatrixPowerHeader.machine (MatrixPowerHeader.resetInput r.d)
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes entry=Composition.restart base.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact bh 0
      · exact (blank 0).2
      · exact (blank 1).2
      · exact (blank 2).2
    · intro j; fin_cases j
      · exact bt 0
      · exact (blank 0).1
      · exact (blank 1).1
      · exact (blank 2).1
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixPowerHeader.machine
    base.final.heads base.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join (MatrixVariablePlane.machine negative) last _ _ _ base focused hb hf
  have localT (j : Fin 4) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 4) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have retained (i : Fin 425) (hn : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=base.final.tapes i ∧ focused.final.heads i=base.final.heads i := by
    rw [ff]; simp [RecoveryFocus.config,hn]
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (localT 0).trans b0
    · exact (retained 22 (by decide)).1.trans (bt 1)
    · exact (retained 400 (by decide)).1.trans (bt 2)
    · exact (retained 200 (by decide)).1.trans (bt 3)
    · exact (retained 407 (by decide)).1.trans (bt 4)
    · exact (retained 394 (by decide)).1.trans (bt 5)
    · exact (retained 424 (by decide)).1.trans (bt 6)
    · exact (localT 1).trans b1
    · exact (localT 2).trans b2
  · intro j; fin_cases j
    · exact (localH 0).trans (bodyH 0)
    · exact (retained 22 (by decide)).2.trans (bh 1)
    · exact (retained 400 (by decide)).2.trans (bh 2)
    · exact (retained 200 (by decide)).2.trans (bh 3)
    · exact (retained 407 (by decide)).2.trans (bh 4)
    · exact (retained 394 (by decide)).2.trans (bh 5)
    · exact (retained 424 (by decide)).2.trans (bh 6)
    · exact (localH 1).trans (bodyH 1)
    · exact (localH 2).trans (bodyH 2)
  · intro i
    have hn : RecoveryFocus.pick slots ((i.castAdd 1).natAdd 412)=none := by fin_cases i <;> decide
    have h := retained ((i.castAdd 1).natAdd 412) hn
    let k : Fin 15 := ⟨i.val+3,by omega⟩
    have he : (k.castAdd 1).natAdd 409=(i.castAdd 1).natAdd 412 := Fin.ext (by simp [k]; omega)
    have hb := blank k
    rw [he] at hb
    exact ⟨h.1.trans hb.1,h.2.trans hb.2⟩
  · change base.steps+1+focused.steps≤budget r
    rw [fs,bodyS]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixVariableHeader
