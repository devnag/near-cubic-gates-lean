import Proof.Circuits.DecompositionCachedChildPosition
import Proof.Circuits.DecompositionSourceCount
import Proof.Assembly.AppendOutputLength
import Proof.MachineModel.Runs
import Proof.MachineModel.Layout

/-! Cold measurement of the ORIGINAL native child cache. The count is decoded
from its real header, the existing counted parser consumes every child, and
cursor recording produces its byte length. No length or count word is advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdMeasure
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryExecution RecoveryRootRound
open RepairRepresentation RepairSource.ProjectionNormalization

theorem field_forward (keep : Bool) : CursorRestore.NoLeft (PCPPQueryField.machine keep) 0 := by
  intro q bs a ha
  fin_cases q <;> simp [PCPPQueryField.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp)
    | (cases ha; simp)

theorem signed_forward : CursorRestore.NoLeft DecompositionSource.Fields.machine 0 := by
  apply CursorRestore.composition_forward
  · intro q bs a ha
    simp [DecompositionSource.Fields.sign] at ha
    cases ha
    simp
  · exact field_forward true

theorem scan_forward : CursorRestore.NoLeft DecompositionCachedChild.machine 0 := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.embedded_forward 2 _ 0 (field_forward false)
  · have child : CursorRestore.NoLeft DecompositionSource.Records.child 0 := by
      apply CursorRestore.composition_forward
      · exact CursorRestore.repeat_forward _ _ 0 signed_forward
      · exact EquationRowCuts.embedded_forward 1 _ 0 signed_forward
    exact CursorRestore.repeat_forward _ _ 0 child

noncomputable def scanner := AppendOutputLength.record DecompositionCachedChild.machine 0
def scanHeads : Fin 6→Nat := ![0,0,0,1,1,0]
def scanInput {q : Nat} (gs : List (ExactThresholdGate q)) : Fin 6→List Bool :=
  ![exactListWord gs,[],[],UnaryTemplate.tape q,UnaryTemplate.tape gs.length,[]]

theorem scan_run {q : Nat} (gs : List (ExactThresholdGate q)) :
    ∃ H T,Step scanner (DecompositionCachedChild.budget gs gs.length) (scanHeads) (scanInput gs) H T ∧
      T 0=exactListWord gs ∧ T 3=UnaryTemplate.tape q ∧
      T 4=UnaryTemplate.tape gs.length ∧ T 5=List.replicate (exactListWord gs).length true := by
  obtain ⟨r,hr,h0,hh0,h3,_hh3,h4,_hh4,hs⟩ := DecompositionCachedChild.position_run gs gs.length le_rfl
  obtain ⟨hp,hh⟩ := prefix_of_run DecompositionCachedChild.machine _ _ r hr
  obtain ⟨delta,_hd,hdelta,ht⟩ := AppendOutputLength.recording_timed hp 0 scan_forward 0
  have he : delta=(exactListWord gs).length := by
    rw [hh0] at hdelta
    simpa [DecompositionCachedChild.entry,exactListWord] using hdelta.symm
  rw [he,Nat.zero_add,hs] at ht
  obtain ⟨result,hresult,hfinal,_⟩ := ht.run (by
    simp only [AppendOutputLength.record,Rewind.recording,Rewind.config,Fin.addCases_left]
    exact hh)
  have hi : Rewind.recording (DecompositionCachedChild.entry gs gs.length) 0=
      (⟨scanner.start,scanHeads,scanInput gs⟩ : Configuration 6 _) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  rw [hi] at hresult
  refine ⟨result.final.heads,result.final.tapes,Step.of_run hresult rfl rfl,?_,?_,?_,?_⟩
  · rw [hfinal];exact h0
  · rw [hfinal];exact h3
  · rw [hfinal];exact h4
  · rw [hfinal];rfl

def input {q : Nat} (gs : List (ExactThresholdGate q)) : Fin 16→List Bool :=
  fun i=>if i=0 then exactListWord gs else if i=12 then UnaryTemplate.tape q else []
def slots : Fin 6→Fin 16 := ![0,13,14,12,10,15]
noncomputable def count := TapeEmbedding.machine 4 DecompositionSource.Count.machine
noncomputable def scan := RecoveryFocus.machine slots scanner
def move : Machine 16 2 where
  descriptionBits := 0
  start := 0
  halted := fun s=>decide (s=1)
  rule := fun s _=>if s=0 then some ⟨1,fun _=>none,fun i=>if i=12 then .right else .stay⟩ else none
def raised (H : Fin 16→Nat) (i : Fin 16) := if i=12 then H i+1 else H i
noncomputable def raw := Composition.machine (Composition.machine count move) scan
noncomputable def machine := Rewind.machine raw
def coldInput {q : Nat} (gs : List (ExactThresholdGate q)) : Fin 17→List Bool :=
  fun i=>Fin.addCases (input gs) (fun _ : Fin 1=>[]) i
def rawBudget {q : Nat} (gs : List (ExactThresholdGate q)) :=
  DecompositionSource.Count.budget gs.length+DecompositionCachedChild.budget gs gs.length+3
def budget {q : Nat} (gs : List (ExactThresholdGate q)) := 2*rawBudget gs+2

theorem move_run (H : Fin 16→Nat) (T : Fin 16→List Bool) :
    Step move 1 H T (raised H) T := by
  have hs : step move (⟨move.start,H,T⟩ : Configuration 16 2)=some ⟨1,raised H,T⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hs).run rfl
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem raw_run {q : Nat} (gs : List (ExactThresholdGate q)) :
    ∃ H T,Step raw (rawBudget gs) (fun _=>0) (input gs) H T ∧
      T 0=exactListWord gs ∧ T 10=UnaryTemplate.tape gs.length ∧
      T 12=UnaryTemplate.tape q ∧ T 15=List.replicate (exactListWord gs).length true := by
  obtain ⟨r,hr,_hs,h0,hh0,h10,hh10⟩ := DecompositionSource.Count.count_run gs.length (gs.flatMap exactWord)
  have first := (Step.of_run hr rfl rfl).embed (fun _ : Fin 4=>0)
    (![UnaryTemplate.tape q,[],[],[]] : Fin 4→List Bool)
  have hfirst : Step count (DecompositionSource.Count.budget gs.length) (fun _=>0) (input gs)
      (Fin.addCases r.final.heads (fun _ : Fin 4=>0))
      (Fin.addCases r.final.tapes (![UnaryTemplate.tape q,[],[],[]] : Fin 4→List Bool)) := by
    apply first.congr_in
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  let H : Fin 16→Nat := fun i=>Fin.addCases r.final.heads (fun _ : Fin 4=>0) i
  let T : Fin 16→List Bool := fun i=>Fin.addCases r.final.tapes (![UnaryTemplate.tape q,[],[],[]] : Fin 4→List Bool) i
  obtain ⟨J,U,hscan,hu0,hu3,hu4,hu5⟩ := scan_run gs
  have second := hscan.focus slots (by decide) (raised H) T
  have hin : ∀ j,raised H (slots j)=scanHeads j := by
    intro j;fin_cases j
    · exact hh0
    · rfl
    · rfl
    · rfl
    · exact hh10
    · rfl
  have tin : ∀ j,T (slots j)=scanInput gs j := by
    intro j;fin_cases j
    · exact h0
    · rfl
    · rfl
    · rfl
    · exact h10
    · rfl
  have second' := second.congr_in (dockH_existing _ _ _ hin) (install_existing _ _ _ tin)
  have whole := (hfirst.seq (move_run H T)).seq second'
  refine ⟨dockH slots (raised H) J,install slots T U,?_,?_,?_,?_,?_⟩
  · have hb : DecompositionSource.Count.budget gs.length+1+1+1+
        DecompositionCachedChild.budget gs gs.length=rawBudget gs := by unfold rawBudget;omega
    rw [hb] at whole
    exact whole
  · exact (install_slot slots (by decide) T U 0).trans hu0
  · exact (install_slot slots (by decide) T U 4).trans hu4
  · exact (install_slot slots (by decide) T U 3).trans hu3
  · exact (install_slot slots (by decide) T U 5).trans hu5

/-- Full physical producer, with complete actual final tape bank and no
capacity/count premises. Ports 10 and 15 feed the cold arithmetic DAG. -/
theorem run {q : Nat} (gs : List (ExactThresholdGate q)) :
    ∃ T,Step machine (budget gs) (fun _=>0) (coldInput gs) (fun _=>0) T ∧
      T 0=exactListWord gs ∧ T 10=UnaryTemplate.tape gs.length ∧
      T 12=UnaryTemplate.tape q ∧ T 15=List.replicate (exactListWord gs).length true := by
  obtain ⟨H,T,⟨r,hr,_hh,ht,hs⟩,h0,h10,h12,h15⟩ := raw_run gs
  obtain ⟨result,hresult,hkeep,hheads,hsteps,_⟩ := Rewind.reset_run raw (rawBudget gs) (input gs) r hr
  have step := (Step.of_run hresult (funext hheads) rfl).enlarge
    (by unfold budget;omega : 2*r.steps+2≤budget gs)
  refine ⟨result.final.tapes,step,?_,?_,?_,?_⟩
  · exact (hkeep 0).trans ((congrFun ht 0).trans h0)
  · exact (hkeep 10).trans ((congrFun ht 10).trans h10)
  · exact (hkeep 12).trans ((congrFun ht 12).trans h12)
  · exact (hkeep 15).trans ((congrFun ht 15).trans h15)

end NearCubicWires.P1Closure.BinaryCacheColdMeasure
