import Proof.MachineModel.OrdinaryMatrixRankStreamReverse

/-! Cold rank-stream rewind entry: the retained raw H is physically
converted to the sentinel consumed by the nested gate/U/field controller. -/
namespace NearCubicWires.RepairOrdinary.MatrixRankReverseEntry
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dimensionSlots : Fin 5 → Fin 8 := ![1,4,5,6,7]
def reverseSlots : Fin 4 → Fin 8 := ![0,6,2,3]
noncomputable def first := RecoveryFocus.machine dimensionSlots MatrixRawDimension.resetMachine
noncomputable def last : Machine 8 (2+(MatrixRankStreamReverse.loopStates+2)) := RecoveryFocus.machine reverseSlots MatrixRankStreamReverse.machine
noncomputable def machine := Composition.machine first last
def input (source : List Bool) (H U G : ℕ) : Fin 8 → List Bool :=
  ![source,List.replicate H true,UnaryTemplate.tape U,UnaryTemplate.tape G,[],[],[],[]]
def heads (pos : ℕ) : Fin 8 → ℕ := ![pos,0,0,0,0,0,0,0]
noncomputable def cfg (source : List Bool) (H U G pos : ℕ) : Configuration 8
    (6+(2+(MatrixRankStreamReverse.loopStates+2))) :=
  ⟨machine.start,heads pos,input source H U G⟩
def budget (H U G : ℕ) := (4*H+8)+1+MatrixRankStreamReverse.budget H U G

theorem entry_run (source : List Bool) (H U G pos : ℕ) :
    ∃ actual,runFrom machine (budget H U G) (cfg source H U G pos)=some actual ∧
      actual.steps ≤ budget H U G ∧
      actual.final.heads=heads (pos-G*MatrixRankPacketReverse.distance H U) ∧
      actual.final.tapes 0=source ∧ actual.final.tapes 2=UnaryTemplate.tape U ∧
      actual.final.tapes 3=UnaryTemplate.tape G ∧
      actual.final.tapes 4=List.replicate H true ∧ actual.final.tapes 5=List.replicate H true ∧
      actual.final.tapes 6=UnaryTemplate.tape H := by
  obtain ⟨dimension,hd,d1,d2,d3,dh,ds⟩ := MatrixRawDimension.reset_run H
  let entry := initialConfiguration MatrixRawDimension.resetMachine (MatrixRawDimension.resetInput H)
  obtain ⟨prepared,hp,pf,ps⟩ := RecoveryFocus.run_config dimensionSlots (by decide)
    MatrixRawDimension.resetMachine (heads pos) (input source H U G) _ entry dimension hd
  have hi : RecoveryFocus.config dimensionSlots (heads pos) (input source H U G) entry=
      ⟨first.start,heads pos,input source H U G⟩ := by
    apply WilliamsSourceCrop.focus_same dimensionSlots
      (⟨first.start,heads pos,input source H U G⟩ : Configuration 8 6) entry
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at hp
  have pslot (i : Fin 5) : prepared.final.tapes (dimensionSlots i)=dimension.final.tapes i := by
    rw [pf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot dimensionSlots (by decide)]
  have pold (i : Fin 8) (hi : ∀ j,dimensionSlots j≠i) : prepared.final.tapes i=input source H U G i := by
    rw [pf]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  have ph : prepared.final.heads=heads pos := by
    rw [pf]
    funext i
    cases hx : RecoveryFocus.pick dimensionSlots i with
    | none => simp only [RecoveryFocus.config,hx]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick dimensionSlots hx
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot dimensionSlots (by decide),dh]
      fin_cases j <;> rfl
  obtain ⟨body,hb,bs,bh,bt⟩ := MatrixRankStreamReverse.reverse_run source H U G pos
  have inputLast : RecoveryFocus.config reverseSlots prepared.final.heads prepared.final.tapes
      (MatrixRankStreamReverse.cfg source H U G pos)=Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [ph]
      fin_cases i <;> rfl
    · intro i
      fin_cases i
      · exact pold 0 (by decide)
      · exact (pslot 3).trans d3
      · exact pold 2 (by decide)
      · exact pold 3 (by decide)
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config (s := 2+(MatrixRankStreamReverse.loopStates+2)) reverseSlots (by decide) MatrixRankStreamReverse.machine
    prepared.final.heads prepared.final.tapes _ _ body hb
  rw [inputLast] at hf
  have whole := Composition.run_join first last _ _ _ prepared focused hp hf
  have outSlot (i : Fin 4) : focused.final.tapes (reverseSlots i)=
      (![source,UnaryTemplate.tape H,UnaryTemplate.tape U,UnaryTemplate.tape G] : Fin 4 → List Bool) i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot reverseSlots (by decide),bt]
  have outOld (i : Fin 8) (hi : ∀ j,reverseSlots j≠i) : focused.final.tapes i=prepared.final.tapes i := by
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  refine ⟨Composition.joinedReceipt prepared focused,whole,?_,?_,outSlot 0,outSlot 2,outSlot 3,
    (outOld 4 (by decide)).trans ((pslot 1).trans d1),
    (outOld 5 (by decide)).trans ((pslot 2).trans d2),outSlot 1⟩
  · change prepared.steps+1+focused.steps ≤ budget H U G
    rw [ps,fs,ds]
    unfold budget
    omega
  · change focused.final.heads=_
    rw [ff]
    funext i
    cases hx : RecoveryFocus.pick reverseSlots i with
    | none =>
      have hi : i≠0 := by
        intro he
        subst i
        have hs := RecoveryFocus.pick_slot reverseSlots (by decide) 0
        change RecoveryFocus.pick reverseSlots 0=some 0 at hs
        rw [hx] at hs
        contradiction
      simp only [RecoveryFocus.config,hx,ph]
      fin_cases i <;> first | contradiction | rfl
    | some j =>
      have hj := RecoveryFocus.slot_of_pick reverseSlots hx
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot reverseSlots (by decide),bh]
      fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.MatrixRankReverseEntry
