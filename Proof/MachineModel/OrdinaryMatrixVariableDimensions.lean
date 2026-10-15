import Proof.MachineModel.OrdinaryMatrixVariableHeader

/-! The externally indexed cold plane body produces its own exact matrix
length sentinel using the accepted actual unary product, preserving controls. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableDimensions
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 12 → Fin 425 := ![400,412,413,414,415,200,416,417,418,419,420,421]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots MatrixWilliamsDimensions.countMachine
noncomputable def machine (negative : Bool) := Composition.machine (MatrixVariableHeader.machine negative) last
noncomputable def input (r : Request) (bit : ℕ) := Composition.leftConfig 23 (MatrixVariableHeader.input r bit)
noncomputable def budget (r : Request) := MatrixVariableHeader.budget r+1+(8*r.U*r.Capacity+10*r.U+30)
def selected : Fin 10 → Fin 425 := ![12,22,400,200,407,394,424,409,410,420]
noncomputable def values (r : Request) (negative : Bool) (bit : ℕ) : Fin 10 → List Bool :=
  ![UnaryTemplate.tape r.d,UnaryTemplate.tape r.p,UnaryTemplate.tape r.U,UnaryTemplate.tape r.Capacity,
    MatrixSignedPlane.plane r negative bit,MatrixRightPlaneNative.plane r,UnaryTemplate.tape (2*bit),
    RepairRepresentation.natWord r.U,UnaryTemplate.tape (2*r.d+3),UnaryTemplate.tape (r.U*r.Capacity)]
def heads : Fin 10 → ℕ := ![0,1,0,0,0,0,1,0,0,0]

theorem dimensions_run (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) : ∃ actual,
    runFrom (machine negative) (budget r) (input r bit)=some actual ∧
    (∀ j,actual.final.tapes (selected j)=values r negative bit j) ∧
    (∀ j,actual.final.heads (selected j)=heads j) ∧
    (∀ i : Fin 2,actual.final.tapes ((i.castAdd 1).natAdd 422)=[] ∧ actual.final.heads ((i.castAdd 1).natAdd 422)=0) ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,blank,bs⟩ := MatrixVariableHeader.header_run r negative bit ht
  obtain ⟨body,hr,b0,b5,b10,bodyH,bodyS⟩ := MatrixWilliamsDimensions.count_run r.U r.Capacity
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes (MatrixWilliamsDimensions.countEntry r.U r.Capacity)=
      Composition.restart base.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact bh 2
      · exact (blank 0).2
      · exact (blank 1).2
      · exact (blank 2).2
      · exact (blank 3).2
      · exact bh 3
      · exact (blank 4).2
      · exact (blank 5).2
      · exact (blank 6).2
      · exact (blank 7).2
      · exact (blank 8).2
      · exact (blank 9).2
    · intro j; fin_cases j
      · exact bt 2
      · exact (blank 0).1
      · exact (blank 1).1
      · exact (blank 2).1
      · exact (blank 3).1
      · exact bt 3
      · exact (blank 4).1
      · exact (blank 5).1
      · exact (blank 6).1
      · exact (blank 7).1
      · exact (blank 8).1
      · exact (blank 9).1
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixWilliamsDimensions.countMachine
    base.final.heads base.final.tapes _ _ body hr
  rw [hi] at hf
  have hj := Composition.run_join (MatrixVariableHeader.machine negative) last _ _ _ base focused hb hf
  have localT (j : Fin 12) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 12) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have retained (i : Fin 425) (hn : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=base.final.tapes i ∧ focused.final.heads i=base.final.heads i := by
    rw [ff]; simp [RecoveryFocus.config,hn]
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (retained 12 (by decide)).1.trans (bt 0)
    · exact (retained 22 (by decide)).1.trans (bt 1)
    · exact (localT 0).trans b0
    · exact (localT 5).trans b5
    · exact (retained 407 (by decide)).1.trans (bt 4)
    · exact (retained 394 (by decide)).1.trans (bt 5)
    · exact (retained 424 (by decide)).1.trans (bt 6)
    · exact (retained 409 (by decide)).1.trans (bt 7)
    · exact (retained 410 (by decide)).1.trans (bt 8)
    · exact (localT 10).trans b10
  · intro j; fin_cases j
    · exact (retained 12 (by decide)).2.trans (bh 0)
    · exact (retained 22 (by decide)).2.trans (bh 1)
    · exact (localH 0).trans (bodyH 0)
    · exact (localH 5).trans (bodyH 5)
    · exact (retained 407 (by decide)).2.trans (bh 4)
    · exact (retained 394 (by decide)).2.trans (bh 5)
    · exact (retained 424 (by decide)).2.trans (bh 6)
    · exact (retained 409 (by decide)).2.trans (bh 7)
    · exact (retained 410 (by decide)).2.trans (bh 8)
    · exact (localH 10).trans (bodyH 10)
  · intro i
    have hn : RecoveryFocus.pick slots ((i.castAdd 1).natAdd 422)=none := by fin_cases i <;> decide
    have h := retained ((i.castAdd 1).natAdd 422) hn
    let k : Fin 12 := ⟨i.val+10,by omega⟩
    have he : (k.castAdd 1).natAdd 412=(i.castAdd 1).natAdd 422 := Fin.ext (by simp [k]; omega)
    have hb := blank k
    rw [he] at hb
    exact ⟨h.1.trans hb.1,h.2.trans hb.2⟩
  · change base.steps+1+focused.steps≤budget r
    rw [fs,bodyS]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixVariableDimensions
