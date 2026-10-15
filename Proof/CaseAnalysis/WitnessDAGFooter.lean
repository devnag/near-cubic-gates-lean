import Proof.CaseAnalysis.WitnessDAGFields

/-! Append the original output-address payload using the retained canonical
natural's literal bit count. Invalid payloads also run in the same linear
bound; their canonical flag is consumed by the whole oracle decision. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGFooter
open LocalBitMultitape RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def wordSlots (i : Fin 7) : Fin 9:=i.castAdd 2
def appendSlots : Fin 3→Fin 9:=![4,7,8]
theorem word_injective : Function.Injective wordSlots:=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 9=>i.val) h)
def input (bits out : List Bool) : Fin 9→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (7+2)=>List Bool) (NativeWord.input bits) ![[],out]
def heads (out : List Bool) (i : Fin 9) : ℕ:=if i=8 then out.length else 0
noncomputable def word:=RecoveryFocus.machine wordSlots NativeWord.machine
noncomputable def append:=RecoveryFocus.machine appendSlots NativeAppend.machine
noncomputable def machine:=Composition.machine word append
noncomputable def entry (bits out : List Bool):=
  (⟨machine.start,heads out,input bits out⟩ : Configuration 9 _)

theorem footer_run (bits out : List Bool) : ∃ actual,
    runFrom machine (10*bits.length+28) (entry bits out)=some actual ∧
      actual.steps≤10*bits.length+28 ∧
      actual.final.tapes 8=out++NativeWord.word bits ∧
      actual.final.heads 8=(out++NativeWord.word bits).length:=by
  obtain ⟨base,hbase,bword⟩:=NativeWord.word_run bits
  obtain ⟨a,ha,ah,atape,as⟩:=hbase.focus_at wordSlots word_injective (heads out) (input bits out)
    (by intro i;simp only [input,wordSlots,Fin.addCases_left])
    (by intro i;simp [heads,wordSlots,show i.castAdd 2≠(8 : Fin 9) by apply Fin.ne_of_val_ne;simp;omega])
  obtain ⟨next,hnext,nf,ns⟩:=NativeAppend.append_run bits [] out
  obtain ⟨b,hb,_,bt,bheads,btapes,_⟩:=RecoveryFocus.dock appendSlots (by decide) NativeAppend.machine _
    a.final.heads a.final.tapes (NativeAppend.entry bits [] out)
    (by intro i;rw [ah];fin_cases i <;> rfl)
    (by
      intro i
      rw [atape]
      fin_cases i
      · change install wordSlots _ base (wordSlots 4)=_
        rw [install_slot _ word_injective,bword]
        rfl
      all_goals rw [install_other _ _ _ _ (by decide)];rfl) next hnext
  have hall:=Composition.run_join word append _ _ _ a b ha hb
  have he:NativeWord.budget bits+1+(2*bits.length+5)=10*bits.length+28:=by unfold NativeWord.budget;omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt a b,hall,?_,?_,?_⟩
  · change a.steps+1+b.steps≤10*bits.length+28
    unfold NativeWord.budget at as
    omega
  · exact (btapes 2).trans (by rw [nf];rfl)
  · exact (bheads 2).trans (by rw [nf];rfl)

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGFooter
