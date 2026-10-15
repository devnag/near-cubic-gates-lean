import Proof.SourceAssembly.SourceNativeListReady

/- The exact packet-index producer: real native header, real count stream,
real retained unary count. Its output cursor is the logical word endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyIndexExact
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SourceAssemblyNativeList (stream savedFields)
noncomputable section

def copySlots : Fin 4 → Fin 5 := ![3,1,2,4]
def directions (i : Fin 5) : HeadMove := if i=4 then .right else .stay
def header := TapeEmbedding.machine 2 (PCPPQueryField.machine true)
def advance := DecompositionCountPosition.move directions
def copies := RecoveryFocus.machine copySlots SourceAssemblyNativeList.machine
def machine := Composition.machine (Composition.machine header advance) copies

def input (xs : List Nat) (tail backing : List Bool) : Fin 5→List Bool :=
  ![natWord xs.length++tail,backing,[],stream xs,UnaryTemplate.tape xs.length]
def output (xs : List Nat) (tail backing : List Bool) : Fin 5→List Bool :=
  ![natWord xs.length++tail,savedFields xs (PCPPQueryField.saved xs.length backing),
    natListWord xs,stream xs,UnaryTemplate.tape xs.length]
def outputHeads (xs : List Nat) : Fin 5→Nat :=
  ![(natWord xs.length).length,0,(natListWord xs).length,(stream xs).length,1]
def budget (xs : List Nat) := 2*natBitLength xs.length+(stream xs).length+5*xs.length+9

theorem exact_run (xs : List Nat) (tail backing : List Bool) :
    Step machine (budget xs) (fun _=>0) (input xs tail backing)
      (outputHeads xs) (output xs tail backing) := by
  obtain ⟨r,hr,hf,_⟩:=PCPPQueryField.nat_run true [] tail backing [] xs.length
  have raw:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).embed
    (fun _ : Fin 2=>0) (![stream xs,UnaryTemplate.tape xs.length] : Fin 2→List Bool)
  let H0 : Fin 5→Nat:=![(natWord xs.length).length,0,(natWord xs.length).length,0,0]
  let H1 : Fin 5→Nat:=![(natWord xs.length).length,0,(natWord xs.length).length,0,1]
  let A : Fin 5→List Bool:=![natWord xs.length++tail,PCPPQueryField.saved xs.length backing,
    natWord xs.length,stream xs,UnaryTemplate.tape xs.length]
  have first : Step header (2*natBitLength xs.length+3) (fun _=>0) (input xs tail backing) H0 A := by
    apply (raw.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;> simp [PCPPQueryField.cfg,PCPPQueryField.payload,
      PCPPQueryField.saved,PCPPQueryField.selected,Fin.addCases,input,H0,A,
      DecompositionSource.natWord_length]
  obtain ⟨m,hm,mf,_⟩:=DecompositionCountPosition.move_run directions H0 A
  have middle : Step advance 1 H0 A H1 A := Step.of_run hm
    (by rw [mf];funext i;fin_cases i <;> rfl) (by rw [mf])
  have run:=(SourceAssemblyNativeListReady.unary_run [] xs []
    (PCPPQueryField.saved xs.length backing) (natWord xs.length)).dock copySlots (by decide)
    H1 A (by intro i;fin_cases i <;> simp [copySlots,H1])
    (by intro i;fin_cases i <;> simp [copySlots,A])
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at run
  have last : Step copies ((stream xs).length+5*xs.length+3) H1 A
      (outputHeads xs) (output xs tail backing) := by
    apply run.congr ?_ ?_
    · funext i;fin_cases i
      · exact dockH_other copySlots _ _ 0 (by decide)
      · exact dockH_slot copySlots (by decide) _ _ 1
      · exact dockH_slot copySlots (by decide) _ _ 2
      · exact dockH_slot copySlots (by decide) _ _ 0
      · exact dockH_slot copySlots (by decide) _ _ 3
    · funext i;fin_cases i
      · exact install_other copySlots _ _ 0 (by decide)
      · exact install_slot copySlots (by decide) _ _ 1
      · exact install_slot copySlots (by decide) _ _ 2
      · exact install_slot copySlots (by decide) _ _ 0
      · exact install_slot copySlots (by decide) _ _ 3
  have all := (first.seq middle).seq last
  have hc : (2*natBitLength xs.length+3+1+1)+1+((stream xs).length+5*xs.length+3)=budget xs := by
    unfold budget
    omega
  rw [hc] at all
  exact all

theorem advance_forward : CursorRestore.NoLeft advance 2 := by
  intro q bits a ha
  fin_cases q <;> simp [advance,DecompositionCountPosition.move] at ha
  subst a
  simp [directions]

theorem forward : CursorRestore.NoLeft machine 2 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.embedded_forward 2 (PCPPQueryField.machine true) 2 EquationRowRaw.header_field_forward)
      advance_forward)
    (CursorRestore.focus_forward copySlots (by decide)
      SourceAssemblyNativeList.machine 2 SourceAssemblyNativeListReady.forward)

def framed := AppendOutputFrame.machine machine 2

theorem framed_run (xs : List Nat) (tail backing : List Bool) :
    ∃ A, Step framed (2*budget xs+4*(natListWord xs).length+7) (fun _=>0)
      (AppendOutputFrame.input (input xs tail backing)) (fun _=>0) A ∧
      A 7=RepairOrdinary.frame (natListWord xs) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=exact_run xs tail backing
  obtain ⟨s,hs,st,sh,ss⟩:=AppendOutputFrame.frame_run machine 2 forward (budget xs)
    (input xs tail backing) r hr (natListWord xs)
    (by rw [rt];rfl) (by rw [rh];rfl)
  refine ⟨s.final.tapes,?_,st⟩
  exact (Step.of_run hs (funext sh) rfl).enlarge (by omega)

end
end SourceAssemblyIndexExact
