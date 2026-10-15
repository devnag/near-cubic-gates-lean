import Proof.Hierarchy.HierarchyBinaryPower

/-! Total binary input-length counting. The initial zero delimiter is
physically written, including on the empty input, before the retained-input
counting loop runs. -/
namespace NearCubicWires.RepairOrdinary.HierarchyInputLength
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,fun i => if i.val=0 then some false else none,
    fun _ => .stay⟩ else none
def marked (bits : List Bool) : Fin 3 → List Bool := ![[false],[],frame bits]
noncomputable def raw := Composition.machine mark ClockInputLength.machine
noncomputable def machine := Rewind.machine raw
def input (bits : List Bool) : Fin 4 → List Bool := ClockLengthReady.source bits
def rawBudget (bits : List Bool) := ClockInputLength.cost bits.length bits+2
def budget (bits : List Bool) := 2*rawBudget bits+2

theorem mark_ready (bits : List Bool) : ReadyRun mark 1 (ClockLengthReady.input bits) (marked bits) := by
  let c : Configuration 3 2 := ⟨1,fun _ => 0,marked bits⟩
  have hp : step mark (initialConfiguration mark (ClockLengthReady.input bits))=some c := by
    simp [step,mark,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ClockLengthReady.input,marked,applyAction,writeTapeBit,c]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) hp).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem raw_run (bits : List Bool) :
    ∃ cap,cap≤2*PCPResourceLedger.ell bits.length+3 ∧ ∃ r,
      run raw (rawBudget bits) (ClockLengthReady.input bits)=some r ∧
      r.final.tapes 0=frame (ClockBinary.word bits.length) ∧
      r.final.tapes 1=List.replicate cap false ∧ r.final.tapes 2=frame bits ∧
      r.steps ≤ rawBudget bits := by
  obtain ⟨cap,hcap,last,hlast,hf,hs⟩ := ClockInputLength.loop_run bits.length 0 0 [] bits []
    (by simp) (by omega)
  have hi : ClockInputLength.config (RecordController.test 10) (ClockBinary.word 0) 0
      ([]++frame bits++[]) 0=initialConfiguration ClockInputLength.machine (marked bits) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ClockInputLength.config,ClockBinary.word,marked,initialConfiguration,frame]
  simp only [List.length_nil] at hlast
  rw [hi] at hlast
  obtain ⟨first,hfirst,ht,hh,hsteps⟩ := mark_ready bits
  have hre : Composition.restart first.final ClockInputLength.machine.start=
      initialConfiguration ClockInputLength.machine (marked bits) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [← hre] at hlast
  have h := Composition.run_join mark ClockInputLength.machine 1 (ClockInputLength.cost bits.length bits)
    _ first last hfirst hlast
  have he : 1+1+ClockInputLength.cost bits.length bits=rawBudget bits := by
    dsimp [rawBudget]; omega
  rw [he] at h
  refine ⟨cap,hcap,Composition.joinedReceipt first last,h,?_,?_,?_,?_⟩
  · simp [Composition.joinedReceipt,Composition.rightConfig,hf,ClockInputLength.config]
  · simp [Composition.joinedReceipt,Composition.rightConfig,hf,ClockInputLength.config]
  · simp [Composition.joinedReceipt,Composition.rightConfig,hf,ClockInputLength.config]
  · dsimp only [Composition.joinedReceipt]
    dsimp [rawBudget]
    omega

theorem count_run (bits : List Bool) :
    ∃ cap scratch,cap≤2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ rawBudget bits ∧ ∃ r,
      run machine (budget bits) (input bits)=some r ∧
      r.final.tapes 0=frame (ClockBinary.word bits.length) ∧
      r.final.tapes 1=List.replicate cap false ∧ r.final.tapes 2=frame bits ∧
      r.final.tapes 3=List.replicate scratch false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget bits := by
  obtain ⟨cap,hcap,base,hb,h0,h1,h2,hs⟩ := raw_run bits
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw
    (rawBudget bits) (ClockLengthReady.input bits) base hb 0
  have hbnd : 2*base.steps+2≤budget bits := by dsimp [budget]; omega
  have hm := run_moreFuel machine (2*base.steps+2) (budget bits-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbnd] at hm
  exact ⟨cap,base.steps,hcap,hs,r,hm,(ht 0).trans h0,(ht 1).trans h1,(ht 2).trans h2,
    by simpa using hcounter,hh,by omega⟩

end NearCubicWires.RepairOrdinary.HierarchyInputLength
