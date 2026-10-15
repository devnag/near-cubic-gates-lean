import Proof.PCP.PCPControlOps
import Proof.PCP.ProjectionNormalizationField

/-! Paid framed operand movement for the serializer. The streaming variant
advances exactly one input field and resets only its local output. The ready
variant also restores the source and can be repeated on canonical results.
All retained zero storage is represented by explicit padding. -/
namespace NearCubicWires.RepairOrdinary.PCPFieldMoves
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool := decide (i=1)
def advanceMachine : Machine 3 5 := MaskedReset.machine Field.machine selected
def readyMachine : Machine 3 5 := Rewind.machine Field.machine
def caps (outCap logCap : ℕ) : Fin 3 → ℕ := ![0,outCap,logCap]
def entry (pre bits suffix : List Bool) (outCap logCap : ℕ) : Configuration 3 5 :=
  ZeroPadding.config (caps outCap logCap)
    (Rewind.recording (Field.cfg 0 (pre++frame bits++suffix) pre.length []) 0)
def output (pre bits suffix : List Bool) (outCap logCap : ℕ) : Fin 3 → List Bool :=
  ![pre++frame bits++suffix,ZeroPadding.pad outCap (frame bits),
    List.replicate (max logCap (2*bits.length+1)) false]

theorem padded_output (bits pre suffix : List Bool) (outCap logCap : ℕ) (q : Fin 5)
    (heads : Fin 3 → ℕ) :
    (ZeroPadding.config (caps outCap logCap)
      (⟨q,heads,![pre++frame bits++suffix,frame bits,List.replicate (2*bits.length+1) false]⟩ :
        Configuration 3 5)).tapes=output pre bits suffix outCap logCap := by
  funext i
  fin_cases i
  · exact ZeroPadding.pad_zero _
  · rfl
  · change ZeroPadding.pad logCap (List.replicate (2*bits.length+1) false)=_
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
    congr 1
    omega

theorem advance_run (pre bits suffix : List Bool) (outCap logCap : ℕ) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom advanceMachine (4*bits.length+4) (entry pre bits suffix outCap logCap)=some r ∧
      r.final.tapes=output pre bits suffix outCap logCap ∧
      r.final.heads=![pre.length+2*bits.length+1,0,0] ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hr,hf,hs⟩ := Field.copy_run pre bits suffix []
  have hhead : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=1 := by simpa [selected] using hi
    subst i
    rw [hf,hs]
    change ([]++frame bits).length≤2*bits.length+1
    simp [frame_length]
  obtain ⟨first,hfirst,hfinal,hsteps,_⟩ :=
    MaskedReset.reset_run Field.machine selected _ _ base hr hhead
  have he : 2*base.steps+2=4*bits.length+4 := by omega
  rw [he] at hfirst hsteps
  have ho : first.final.tapes=![pre++frame bits++suffix,frame bits,
      List.replicate (2*bits.length+1) false] := by
    rw [hfinal,hf,hs]
    funext i; fin_cases i <;> rfl
  obtain ⟨r,hrun,hrt,hrs,_⟩ := ZeroPadding.run_config advanceMachine (caps outCap logCap) _ _ first hfirst
  refine ⟨r,hrun,?_,?_,hrs.trans hsteps⟩
  · rw [hrt]
    change (fun i => ZeroPadding.pad (caps outCap logCap i) (first.final.tapes i))=_
    rw [ho]
    exact padded_output bits pre suffix outCap logCap 0 (fun _ => 0)
  · rw [hrt,hfinal,hf]
    funext i
    fin_cases i <;> rfl

theorem ready_run (bits suffix : List Bool) (outCap logCap : ℕ) :
    ReadyRun readyMachine (4*bits.length+4)
      ![frame bits++suffix,List.replicate outCap false,List.replicate logCap false]
      (output [] bits suffix outCap logCap) := by
  obtain ⟨base,hr,hf,hs⟩ := Field.copy_run [] bits suffix []
  obtain ⟨first,hfirst,hfinal,hsteps,_⟩ := Rewind.recorded_run Field.machine _ _ base hr 0
    (by intro i; fin_cases i <;> simp [Field.cfg])
  have he : 0+2*base.steps+2=4*bits.length+4 := by omega
  rw [he] at hfirst hsteps
  have ho : first.final.tapes=![[]++frame bits++suffix,frame bits,
      List.replicate (2*bits.length+1) false] := by
    rw [hfinal,hf,hs,Nat.zero_add]
    funext i; fin_cases i <;> rfl
  obtain ⟨r,hrun,hrt,hrs,_⟩ := ZeroPadding.run_config readyMachine (caps outCap logCap) _ _ first hfirst
  refine ⟨r,?_,?_,?_,hrs.trans hsteps⟩
  · change runFrom readyMachine (4*bits.length+4)
      (initialConfiguration readyMachine
        ![frame bits++suffix,List.replicate outCap false,List.replicate logCap false])=some r
    convert hrun using 2
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,caps,ZeroPadding.pad,
        initialConfiguration,Rewind.recording,Rewind.config,Field.cfg] <;> rfl
  · rw [hrt]
    change (fun i => ZeroPadding.pad (caps outCap logCap i) (first.final.tapes i))=_
    rw [ho]
    exact padded_output bits [] suffix outCap logCap 0 (fun _ => 0)
  · intro i
    rw [hrt,hfinal]
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPFieldMoves
