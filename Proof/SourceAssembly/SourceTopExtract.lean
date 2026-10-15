import Proof.SourceAssembly.SourceTopEntry

/- Extract the real framed TOP field from the actual native circuit stream.
The count is read physically; neither its value nor the field is hardwired. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyTopExtract
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairSource.ProjectionNormalization RecoveryRootRound
noncomputable section

def fieldSlots : Fin 2→Fin 3 := ![0,2]
def field := RecoveryFocus.machine fieldSlots MatrixScoreBankField.machine
def raw := Composition.machine (PCPPQueryField.machine false) field
def input (n : Nat) (bits tail : List Bool) : Fin 3→List Bool :=
  ![natWord n++frame bits++tail,[],[]]
def mid (n : Nat) (bits tail : List Bool) : Fin 3→List Bool :=
  ![natWord n++frame bits++tail,PCPPQueryField.saved n [],[]]
def output (n : Nat) (bits tail : List Bool) : Fin 3→List Bool :=
  ![natWord n++frame bits++tail,PCPPQueryField.saved n [],frame bits]
def heads (n : Nat) (bits : List Bool) : Fin 3→Nat :=
  ![(natWord n).length+(frame bits).length,0,(frame bits).length]
def rawBudget (n : Nat) (bits : List Bool) := 2*natBitLength n+2*bits.length+5

theorem raw_run (n : Nat) (bits tail : List Bool) :
    Step raw (rawBudget n bits) (fun _=>0) (input n bits tail)
      (heads n bits) (output n bits tail) := by
  obtain ⟨f,hf,ff,_⟩:=PCPPQueryField.nat_run false [] (frame bits++tail) [] [] n
  have first : Step (PCPPQueryField.machine false) (2*natBitLength n+3)
      (fun _=>0) (input n bits tail) (![(natWord n).length,0,0]) (mid n bits tail) := by
    apply ((Step.of_run hf (congrArg Configuration.heads ff) (congrArg Configuration.tapes ff)).congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;> simp [PCPPQueryField.cfg,PCPPQueryField.payload,
      PCPPQueryField.selected,PCPPQueryField.saved,input,mid,List.append_assoc,DecompositionSource.natWord_length]
  obtain ⟨f,hf,ff,_⟩:=MatrixScoreBankField.field_run bits (natWord n) tail []
  have second := (Step.of_run hf (congrArg Configuration.heads ff) (congrArg Configuration.tapes ff)).dock
    fieldSlots (by decide) (![(natWord n).length,0,0]) (mid n bits tail)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  have last : Step field (2*bits.length+1) (![(natWord n).length,0,0]) (mid n bits tail)
      (heads n bits) (output n bits tail) := by
    apply second.congr ?_ ?_
    · funext i;fin_cases i
      · exact dockH_slot fieldSlots (by decide) _ _ 0
      · exact dockH_other fieldSlots _ _ 1 (by decide)
      · exact (dockH_slot fieldSlots (by decide) _ _ (1 : Fin 2)).trans (by rfl)
    · funext i;fin_cases i
      · exact install_slot fieldSlots (by decide) _ _ 0
      · exact install_other fieldSlots _ _ 1 (by decide)
      · exact (install_slot fieldSlots (by decide) _ _ (1 : Fin 2)).trans (by rfl)
  have all:=first.seq last
  have ht : (2*natBitLength n+3)+1+(2*bits.length+1)=rawBudget n bits := by unfold rawBudget;omega
  rw [ht] at all
  exact all

def machine := Rewind.machine raw
def budget (n : Nat) (bits : List Bool) := 2*rawBudget n bits+2

theorem run (n : Nat) (bits tail : List Bool) :
    ∃ A, Step machine (budget n bits) (fun _=>0)
      (Fin.addCases (input n bits tail) (fun _ : Fin 1=>[])) (fun _=>0) A ∧
      A 0=natWord n++frame bits++tail ∧ A 2=frame bits := by
  obtain ⟨first,hf,_hH,hA,hs⟩:=raw_run n bits tail
  obtain ⟨last,hl,lt,lh,_⟩:=Rewind.reset_run raw (rawBudget n bits) (input n bits tail) first hf
  refine ⟨last.final.tapes,(Step.of_run hl (funext lh) rfl).enlarge ?_,?_,?_⟩
  · unfold budget;omega
  · exact (lt 0).trans (congrFun hA 0)
  · exact (lt 2).trans (congrFun hA 2)

end
end SourceAssemblyTopExtract
