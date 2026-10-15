import Proof.PCP.PCPPQueryNatural
import Proof.PCP.PCPPNativeLiteralSplit
import Proof.Circuits.DecompositionCountPosition
import Proof.MachineModel.Layout

/-! Decode the actual signed native PCPP literal word. The output index
is its original proof coordinate; its sign remains a separate physical bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalLiteral
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 2 PCPPQueryNatural.machine
def directions (i : Fin 13) : HeadMove := if i=10 then .left else .stay
def move := DecompositionCountPosition.move directions
def slots : Fin 3 → Fin 13 := ![10,11,12]
noncomputable def last := RecoveryFocus.machine slots PCPPNativeLiteralSplit.raw
noncomputable def machine := Composition.machine (Composition.machine first move) last
def budget (index : ℕ) (negative : Bool) :=
  PCPPQueryNatural.budget (2*index+negative.toNat)+2*index+negative.toNat+5
def heads (pos : ℕ) (i : Fin 13) := if i=0 then pos else 0
def data (source : List Bool) (i : Fin 13) := if i=0 then source else []

theorem raw_run (index : ℕ) (negative : Bool) (pre tail : List Bool) :
    ∃ r,runFrom machine (budget index negative)
      ⟨machine.start,heads pre.length,data (pre++RepairRepresentation.natWord (2*index+negative.toNat)++tail)⟩=some r ∧
      r.final.tapes 0=pre++RepairRepresentation.natWord (2*index+negative.toNat)++tail ∧
      r.final.heads 0=pre.length+2*natBitLength (2*index+negative.toNat)+1 ∧
      r.final.tapes 11=List.replicate index true ∧ r.final.tapes 12=[negative] ∧
      r.steps ≤ budget index negative := by
  obtain ⟨a,ha,_,at0,ah0,at10,ah10⟩:=PCPPQueryNatural.natural_run pre tail (2*index+negative.toNat)
  have aStep:=Step.of_run ha rfl rfl
  have initial:=aStep.embed (fun _ : Fin 2=>0) (fun _ : Fin 2=>[])
  let H : Fin 13 → ℕ:=Fin.addCases (m:=11) (n:=2) (motive:=fun _=>ℕ) a.final.heads (fun _ : Fin 2=>0)
  let A : Fin 13 → List Bool:=Fin.addCases (m:=11) (n:=2) (motive:=fun _=>List Bool) a.final.tapes (fun _ : Fin 2=>[])
  obtain ⟨b,hb,bf,_⟩:=DecompositionCountPosition.move_run directions H A
  have bStep:=Step.of_run hb (congrArg Configuration.heads bf) (congrArg Configuration.tapes bf)
  obtain ⟨c,hc,cf,_⟩:=PCPPNativeLiteralSplit.raw_run index negative
  have lastStep:=Step.of_run hc (congrArg Configuration.heads cf) (congrArg Configuration.tapes cf)
  have entryH : ∀ j,(fun i=>(directions i).apply (H i)) (slots j)=0 := by
    intro j;fin_cases j
    · change HeadMove.left.apply (a.final.heads 10)=0
      rw [ah10];rfl
    all_goals rfl
  have entryA : ∀ j,A (slots j)=(![UnaryTemplate.tape (2*index+negative.toNat),[],[]] : Fin 3 → List Bool) j := by
    intro j;fin_cases j
    · exact at10
    all_goals rfl
  have moved := initial.seq bStep
  have docked:=lastStep.dock slots (by decide) (fun i=>(directions i).apply (H i)) A entryH entryA
  have all:=moved.seq docked
  have ein : Fin.addCases (m:=11) (n:=2) (motive:=fun _=>ℕ) (PCPPQueryNatural.entry
      (pre++RepairRepresentation.natWord (2*index+negative.toNat)++tail) pre.length).heads
      (fun _ : Fin 2=>0)=heads pre.length := by funext i;fin_cases i <;> rfl
  have tin : Fin.addCases (m:=11) (n:=2) (motive:=fun _=>List Bool) (PCPPQueryNatural.entry
      (pre++RepairRepresentation.natWord (2*index+negative.toNat)++tail) pre.length).tapes
      (fun _ : Fin 2=>[])=data (pre++RepairRepresentation.natWord (2*index+negative.toNat)++tail) := by
    funext i;fin_cases i <;> rfl
  have time : PCPPQueryNatural.budget (2*index+negative.toNat)+1+1+1+(2*index+negative.toNat+2)=budget index negative := by
    unfold budget;omega
  rw [time] at all
  obtain ⟨r,hr,rh,rt,rs⟩:=all.congr_in ein tin
  refine ⟨r,hr,?_,?_,?_,?_,rs⟩
  · rw [rt,install_other _ _ _ 0 (by intro j;fin_cases j <;> decide)]
    exact at0
  · rw [rh,ExtDecompositionBatch.dockH_other _ _ _ 0 (by intro j;fin_cases j <;> decide)]
    exact ah0
  · change r.final.tapes (slots 1)=_
    rw [rt,install_slot _ (by decide)]
    rfl
  · change r.final.tapes (slots 2)=_
    rw [rt,install_slot _ (by decide)]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalLiteral
