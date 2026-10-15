import Proof.PCP.PCPPQueryPrepareCopy

/-! The literal query input produces both unary value drivers before the
source call. Their values are read from the retained query-index cursor and
the separately copied arity field of the same PCPP request. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryPrepare
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexSlots : Fin 11→Fin 27 := ![1,7,8,9,10,11,12,13,14,15,16]
def aritySlots : Fin 11→Fin 27 := ![5,17,18,19,20,21,22,23,24,25,26]
noncomputable def indexProgram := RecoveryFocus.machine indexSlots PCPPQueryNatural.machine
noncomputable def arityProgram := RecoveryFocus.machine aritySlots PCPPQueryNatural.machine
noncomputable def prefixMachine := Composition.machine PCPPQueryPrepareCopy.machine indexProgram
noncomputable def machine := Composition.machine prefixMachine arityProgram
def word (arity : ℕ) (code : List Bool) := natWord arity++code
def input (arity index : ℕ) (code : List Bool) :=
  PCPPQueryPrepareCopy.input (frame (word arity code)++natWord index)
def budget (arity index : ℕ) (code : List Bool) :=
  PCPPQueryPrepareCopy.budget (word arity code) (natWord index)+
    PCPPQueryNatural.budget index+PCPPQueryNatural.budget arity+2

theorem prepare_run (arity index : ℕ) (code : List Bool) :
    ∃ r,run machine (budget arity index code) (input arity index code)=some r ∧
      r.steps≤budget arity index code ∧
      r.final.tapes 3=frame (word arity code) ∧ r.final.heads 3=0 ∧
      r.final.tapes 16=UnaryTemplate.tape index ∧ r.final.heads 16=1 ∧
      r.final.tapes 26=UnaryTemplate.tape arity ∧ r.final.heads 26=1 := by
  obtain ⟨a,ha,haf,has⟩ := PCPPQueryPrepareCopy.copy_run (word arity code) (natWord index)
  have hit : ∀ j,a.final.tapes (indexSlots j)=if j=0 then
      frame (word arity code)++natWord index++[] else [] := by
    intro j
    rw [haf]
    fin_cases j <;> simp [PCPPQueryPrepareCopy.output,PCPPQueryPrepareCopy.tapes,indexSlots]
  have hih : ∀ j,a.final.heads (indexSlots j)=if j=0 then (frame (word arity code)).length else 0 := by
    intro j
    rw [haf]
    fin_cases j <;> simp [PCPPQueryPrepareCopy.output,PCPPQueryPrepareCopy.heads,indexSlots]
  obtain ⟨b,hb,hbs,_,_,hindex,hindexHead,hbOther⟩ := PCPPQueryNatural.focus_run indexSlots (by decide)
    a.final (frame (word arity code)) [] index hit hih
  have hAB := Composition.run_join PCPPQueryPrepareCopy.machine indexProgram _ _ _ a b ha hb
  let ab := Composition.joinedReceipt a b
  have hnone (j : Fin 11) : RecoveryFocus.pick indexSlots (aritySlots j)=none := by
    fin_cases j <;> decide
  have hat : ∀ j,ab.final.tapes (aritySlots j)=if j=0 then []++natWord arity++code else [] := by
    intro j
    change b.final.tapes (aritySlots j)=_
    rw [(hbOther (aritySlots j) (hnone j)).1,haf]
    fin_cases j <;> simp [PCPPQueryPrepareCopy.output,PCPPQueryPrepareCopy.tapes,aritySlots,word]
  have hah : ∀ j,ab.final.heads (aritySlots j)=if j=0 then ([] : List Bool).length else 0 := by
    intro j
    change b.final.heads (aritySlots j)=_
    rw [(hbOther (aritySlots j) (hnone j)).2,haf]
    fin_cases j <;> simp [PCPPQueryPrepareCopy.output,PCPPQueryPrepareCopy.heads,aritySlots]
  obtain ⟨c,hc,hcs,_,_,harity,harityHead,hcOther⟩ := PCPPQueryNatural.focus_run aritySlots (by decide)
    ab.final [] code arity hat hah
  have hABC := Composition.run_join prefixMachine arityProgram _ _ _ ab c hAB hc
  have htime : (PCPPQueryPrepareCopy.budget (word arity code) (natWord index)+1+PCPPQueryNatural.budget index)+1+
      PCPPQueryNatural.budget arity=budget arity index code := by unfold budget; omega
  rw [htime] at hABC
  have hentry : Composition.leftConfig PCPPQueryNatural.states
      (Composition.leftConfig PCPPQueryNatural.states
        (initialConfiguration PCPPQueryPrepareCopy.machine (input arity index code)))=
      initialConfiguration machine (input arity index code) := rfl
  dsimp only [input] at hentry
  rw [hentry] at hABC
  have hc3 := hcOther 3 (by decide)
  have hb3 := hbOther 3 (by decide)
  have hc16 := hcOther 16 (by decide)
  refine ⟨Composition.joinedReceipt ab c,hABC,?_,?_,?_,?_,?_,harity,harityHead⟩
  · change (a.steps+1+b.steps)+1+c.steps≤_
    rw [has]
    unfold budget
    omega
  · change c.final.tapes 3=_
    rw [hc3.1]
    change b.final.tapes 3=_
    rw [hb3.1,haf]
    rfl
  · change c.final.heads 3=0
    rw [hc3.2]
    change b.final.heads 3=0
    rw [hb3.2,haf]
    rfl
  · change c.final.tapes 16=_
    rw [hc16.1]
    exact hindex
  · change c.final.heads 16=1
    rw [hc16.2]
    exact hindexHead

end NearCubicWires.RepairOrdinary.PCPPQueryPrepare
