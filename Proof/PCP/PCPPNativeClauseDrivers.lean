import Proof.PCP.PCPPNativeClauseTemplate
import Proof.PCP.PCPPNativeQueryConjunction

/-! The actual raw capacity and clause count produce the two capacity
drivers, the head-one clause sentinel, and the fixed true cell. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDrivers
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlots : Fin 4→Fin 10 := ![4,5,6,7]
def fixedSlots : Fin 2→Fin 10 := ![8,9]
noncomputable def first := TapeEmbedding.machine 6 MatrixDimensionHeader.machine
noncomputable def second := RecoveryFocus.machine countSlots MatrixDimensionHeader.machine
noncomputable def third := RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine [true])
noncomputable def machine := Composition.machine (Composition.machine first second) third
def extra (M : ℕ) : Fin 6→List Bool := ![List.replicate M true,[],[],[],[],[]]
def input (C M : ℕ) : Fin 10→List Bool :=
  Fin.addCases (m:=4) (n:=6) (motive:=fun _=>List Bool) (MatrixRawDimension.input C) (extra M)
def budget (C M : ℕ) := 2*C+2*M+12

theorem drivers_run (C M : ℕ) : ∃ result,
    run machine (budget C M) (input C M)=some result ∧ result.steps=budget C M ∧
    result.final.heads 1=0 ∧ result.final.tapes 1=List.replicate C true ∧
    result.final.heads 2=0 ∧ result.final.tapes 2=List.replicate C true ∧
    result.final.heads 7=1 ∧ result.final.tapes 7=UnaryTemplate.tape M ∧
    result.final.heads 8=0 ∧ result.final.tapes 8=[true] := by
  obtain ⟨a,ar,a1,a2,_,ah,as⟩:=MatrixRawDimension.raw_run C
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 6=>0) (extra M) a
  have firstRun:=TapeEmbedding.run_embed MatrixDimensionHeader.machine (fun _ : Fin 6=>0) (extra M) _ _ a ar
  obtain ⟨b,br,_,_,bt,bh,bs⟩:=MatrixRawDimension.raw_run M
  obtain ⟨c,cr,_,cs,ch,ct,keepc⟩:=RecoveryFocus.dock countSlots (by decide) MatrixDimensionHeader.machine _
    lifted.final.heads lifted.final.tapes (initialConfiguration MatrixDimensionHeader.machine (MatrixRawDimension.input M))
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) b br
  have joined:=Composition.run_join first second _ _ _ lifted c firstRun cr
  obtain ⟨d,dr,dt,dh,ds⟩:=HierarchyFixedWord.word_ready [true]
  obtain ⟨e,er,_,es,eh,et,keepe⟩:=RecoveryFocus.dock fixedSlots (by decide) (HierarchyFixedWord.machine [true]) _
    c.final.heads c.final.tapes (initialConfiguration (HierarchyFixedWord.machine [true]) (fun _=>[]))
    (by intro j; fin_cases j; exact (keepc 8 (by decide)).1; exact (keepc 9 (by decide)).1)
    (by intro j; fin_cases j; exact (keepc 8 (by decide)).2; exact (keepc 9 (by decide)).2) d dr
  have allRun:=Composition.run_join (Composition.machine first second) third _ _ _
    (Composition.joinedReceipt lifted c) e joined er
  have fuel : (2*C+3)+1+(2*M+3)+1+(2*[true].length+2)=budget C M := by simp [budget]; omega
  rw [fuel] at allRun
  have init : Composition.leftConfig _ (Composition.leftConfig 4
      (TapeEmbedding.config (fun _ : Fin 6=>0) (extra M)
        (initialConfiguration MatrixDimensionHeader.machine (MatrixRawDimension.input C))))=
      initialConfiguration machine (input C M) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=4) (n:=6) (fun _=>?_) (fun _=>?_) i <;>
        simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [init] at allRun
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt lifted c) e,allRun,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps+1+e.steps=budget C M
    rw [cs,es,as,bs,ds]
    exact fuel
  · change e.final.heads 1=0
    rw [(keepe 1 (by decide)).1,(keepc 1 (by decide)).1]
    exact congrFun ah 1
  · change e.final.tapes 1=_
    rw [(keepe 1 (by decide)).2,(keepc 1 (by decide)).2]
    exact a1
  · change e.final.heads 2=0
    rw [(keepe 2 (by decide)).1,(keepc 2 (by decide)).1]
    exact congrFun ah 2
  · change e.final.tapes 2=_
    rw [(keepe 2 (by decide)).2,(keepc 2 (by decide)).2]
    exact a2
  · change e.final.heads 7=1
    rw [(keepe 7 (by decide)).1]
    exact (ch 3).trans (congrFun bh 3)
  · change e.final.tapes 7=_
    rw [(keepe 7 (by decide)).2]
    exact (ct 3).trans bt
  · change e.final.heads 8=0
    exact (eh 0).trans (dh 0)
  · change e.final.tapes 8=_
    exact (et 0).trans (congrFun dt 0)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDrivers
