import Proof.CaseAnalysis.CaseTwoBinaryMeaning
import Proof.Hierarchy.HierarchyFixedWord

/-! Extract the actual input, native clause address, and padded final position
from one occurrence block. The original address frame survives every read.
All three unary widths/offsets are caller-produced and charged there. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressFields
open LocalBitMultitape SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def oneSlots : Fin 2→Fin 27:=![20,26]
def inputSlots : Fin 8→Fin 27:=![0,4,5,1,6,7,8,9]
def clauseSlots : Fin 13→Fin 27:=![0,10,1,2,11,12,13,14,15,16,17,18,19]
def positionSlots : Fin 8→Fin 27:=![0,21,3,20,22,23,24,25]
def one:=RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
def readInput:=RecoveryFocus.machine inputSlots SliceFrame.machine
def readClause:=RecoveryFocus.machine clauseSlots BinaryField.machine
def readPosition:=RecoveryFocus.machine positionSlots SliceFrame.machine
def machine:=Composition.machine (Composition.machine (Composition.machine one readInput) readClause) readPosition
def word {q cb : ℕ} (u : BitInput q) (clause : BitInput cb) (pad : List Bool) (position : Bool):=
  List.ofFn u++(List.ofFn clause++(pad++[position]))
def input {q cb : ℕ} (u : BitInput q) (clause : BitInput cb) (pad : List Bool) (position : Bool) (i : Fin 27):=
  if i=0 then frame (word u clause pad position) else if i=1 then List.replicate q true
  else if i=2 then List.replicate cb true else if i=3 then List.replicate (q+cb+pad.length) true else []
def heads (i : Fin 27):=if i=19 then 1 else 0
def budget (q cb padding index : ℕ):=4+1+SliceFrame.budget 0 q+1+
  BinaryField.budget q cb index+1+SliceFrame.budget (q+cb+padding) 1

theorem fields_run {q cb : ℕ} (u : BitInput q) (clause : BitInput cb) (pad : List Bool) (position : Bool) : ∃ out,
    run machine (budget q cb pad.length (binaryAddress clause).val) (input u clause pad position)=some out ∧
      out.steps≤budget q cb pad.length (binaryAddress clause).val ∧ out.final.heads=heads ∧
      out.final.tapes 0=frame (word u clause pad position) ∧ out.final.tapes 4=List.ofFn u ∧
      out.final.tapes 8=frame (List.ofFn u) ∧ out.final.tapes 19=UnaryTemplate.tape (binaryAddress clause).val ∧
      out.final.tapes 21=[position]:=by
  obtain ⟨oneReceipt,ho,ot,oh,os⟩:=HierarchyFixedWord.word_ready [true]
  have oneReady:ClockJoin.ReadyRun (HierarchyFixedWord.machine [true]) 4 (fun _=>[]) _:=
    ⟨oneReceipt,ho,ot,oh,os.le⟩
  have firstReady:=oneReady.focus oneSlots (by decide) (input u clause pad position)
    (by intro j;fin_cases j <;>rfl)
  let A:=install oneSlots (input u clause pad position) ![[true],[false]]
  obtain ⟨uout,hu,uf,ur,ukeep,_,uw⟩:=SliceFrame.slice_run [] (List.ofFn u) (List.ofFn clause++(pad++[position]))
  simp only [List.length_nil,List.length_ofFn] at hu uw
  have uReady:=hu.focus inputSlots (by decide) A (by
    intro j
    rw [show A (inputSlots j)=input u clause pad position (inputSlots j) from
      install_other oneSlots _ _ _ (by fin_cases j <;>decide)]
    fin_cases j <;>first | rfl | (change List.replicate q true=List.replicate (List.ofFn u).length true;rw [List.length_ofFn]))
  let B:=install inputSlots A uout
  have joined:=ClockJoin.join _ _ _ _ _ _ _ firstReady uReady
  obtain ⟨first,hfirst,ft,fh,fs⟩:=joined
  obtain ⟨cr,hcr,cs,ci,cih,ch,ckeep,_,_⟩:=BinaryField.address_run (List.ofFn u) (pad++[position]) clause
  simp only [List.length_ofFn] at hcr cs
  have ct (j : Fin 13) : first.final.tapes (clauseSlots j)=
      (fun i : Fin 13=>if i=0 then frame (List.ofFn u++List.ofFn clause++(pad++[position]))
        else if i=2 then List.replicate q true else if i=3 then List.replicate cb true else []) j:=by
    rw [ft]
    fin_cases j
    · change install inputSlots A uout 0=frame (List.ofFn u++List.ofFn clause++(pad++[position]))
      exact (install_slot inputSlots (by decide) A uout 0).trans
        (by simpa only [List.nil_append,List.append_assoc] using ukeep)
    · exact (install_other inputSlots A uout 10 (by decide)).trans
        (install_other oneSlots (input u clause pad position) _ 10 (by decide))
    · exact (install_slot inputSlots (by decide) A uout 3).trans uw
    all_goals
      exact (install_other inputSlots A uout _ (by decide)).trans
        (install_other oneSlots (input u clause pad position) _ _ (by decide))
  obtain ⟨second,hsecond,_,ss,sh,st,skeep⟩:=RecoveryFocus.dock clauseSlots (by decide)
    BinaryField.machine _ first.final.heads first.final.tapes _ (by intro j;exact fh _) ct cr hcr
  have secondHeads:second.final.heads=heads:=by
    funext j
    by_cases hj : ∃ i,clauseSlots i=j
    · obtain ⟨i,rfl⟩:=hj
      by_cases hi : i=12
      · subst i;exact (sh 12).trans cih
      · have hslot : clauseSlots i≠19:=by intro h;apply hi;exact (show Function.Injective clauseSlots from by decide) h
        rw [heads,if_neg hslot]
        exact (sh i).trans (ch i hi)
    · rw [(skeep j (by intro i hi;exact hj ⟨i,hi⟩)).1,fh,heads]
      have h19 : j≠19:=by intro h;subst j;exact hj ⟨12,rfl⟩
      simp only [h19,if_false]
  obtain ⟨pout,hp,_,pr,pkeep,_,_⟩:=SliceFrame.slice_run (List.ofFn u++List.ofFn clause++pad) [position] []
  simp only [List.length_append,List.length_ofFn,List.length_singleton] at hp
  have preword : (List.ofFn u++List.ofFn clause++pad)++[position]++[]=word u clause pad position:=by
    simp only [word,List.append_nil,List.append_assoc]
  have fresh (i : Fin 27) (hc : ∀ j,clauseSlots j≠i) (hu : ∀ j,inputSlots j≠i)
      (ho : ∀ j,oneSlots j≠i) : second.final.tapes i=input u clause pad position i:=
    (skeep i hc).2.trans ((congrFun ft i).trans
      ((install_other inputSlots A uout i hu).trans (install_other oneSlots _ _ i ho)))
  obtain ⟨last,hl,lh,lt,ls⟩:=hp.focus_at positionSlots (by decide) second.final.heads second.final.tapes
    (by intro j;fin_cases j
        · change second.final.tapes 0=frame ((List.ofFn u++List.ofFn clause++pad)++[position]++[])
          rw [preword]
          exact (st 0).trans (by simpa only [word,List.append_assoc] using ckeep)
        · exact fresh 21 (by decide) (by decide) (by decide)
        · change second.final.tapes 3=List.replicate (List.ofFn u++List.ofFn clause++pad).length true
          rw [fresh 3 (by decide) (by decide) (by decide)]
          simp only [List.length_append,List.length_ofFn];rfl
        · change second.final.tapes 20=[true]
          rw [(skeep 20 (by decide)).2,ft,install_other inputSlots _ _ 20 (by decide)]
          exact install_slot oneSlots (by decide) _ _ 0
        · exact fresh 22 (by decide) (by decide) (by decide)
        · exact fresh 23 (by decide) (by decide) (by decide)
        · exact fresh 24 (by decide) (by decide) (by decide)
        · exact fresh 25 (by decide) (by decide) (by decide))
    (by intro j;rw [secondHeads];fin_cases j <;>rfl)
  have two:=Composition.run_join (Composition.machine one readInput) readClause _ _ _ first second hfirst hsecond
  have whole:=Composition.run_join (Composition.machine (Composition.machine one readInput) readClause) readPosition
    _ _ _ _ last two hl
  refine ⟨_,whole,?_,lh.trans secondHeads,?_,?_,?_,?_,?_⟩
  · change first.steps+1+second.steps+1+last.steps≤_
    rw [ss]
    unfold budget
    omega
  · change last.final.tapes 0=_
    rw [lt]
    exact (install_slot positionSlots (by decide) _ pout 0).trans (pkeep.trans (congrArg frame preword))
  · change last.final.tapes 4=_
    rw [lt,install_other positionSlots _ _ 4 (by decide),(skeep 4 (by decide)).2,ft]
    exact (install_slot inputSlots (by decide) A uout 1).trans ur
  · change last.final.tapes 8=_
    rw [lt,install_other positionSlots _ _ 8 (by decide),(skeep 8 (by decide)).2,ft]
    exact (install_slot inputSlots (by decide) A uout 6).trans uf
  · change last.final.tapes 19=_
    rw [lt,install_other positionSlots _ _ 19 (by decide)]
    exact (st 12).trans ci
  · change last.final.tapes 21=_
    rw [lt]
    exact (install_slot positionSlots (by decide) _ pout 1).trans pr

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressFields
