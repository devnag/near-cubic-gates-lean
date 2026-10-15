import Proof.Assembly.AppendFrameKernel
import Proof.Amplification.RecoveryScratchErase
import Proof.Hierarchy.CompetitorRecordRewind
import Proof.MachineModel.Runs

/-! Concrete reusable field operations for the padded physical cycle.
Lengths, zero reserves and unary sweep drivers are explicit tape inputs.
The same machines work at every runtime size, preserve all source bits,
and pay for framing, clearing and head restoration. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace CycleFields.Primitives
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

theorem clock_step {t s n : Nat} {p : Machine t s}
    {input output : Fin t→List Bool} (h : ClockJoin.ReadyRun p n input output) :
    Step p n (fun _=>0) input (fun _=>0) output := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,funext hh,ht,hs⟩

abbrev frameMachine := AppendFrameKernel.machine

def frameInput (bits : List Bool) (sourceCap lengthCap targetCap logCap : Nat) :
    Fin 4 → List Bool :=
  ![ZeroPadding.pad sourceCap bits,
    ZeroPadding.pad lengthCap (List.replicate bits.length true),
    List.replicate targetCap false,List.replicate logCap false]

def frameOutput (bits : List Bool) (sourceCap lengthCap targetCap logCap : Nat) :
    Fin 4 → List Bool :=
  ![ZeroPadding.pad sourceCap bits,
    ZeroPadding.pad lengthCap (List.replicate bits.length true),
    ZeroPadding.pad targetCap (frame bits),List.replicate logCap false]

/-- Turn an actual raw word and its actual unary length into a retained frame.
The input and output use the same fixed physical reserves. -/
theorem frame_step (bits : List Bool) (sourceCap lengthCap targetCap logCap : Nat)
    (hlog : 2*bits.length+1 ≤ logCap) :
    Step frameMachine (4*bits.length+4) (fun _=>0)
      (frameInput bits sourceCap lengthCap targetCap logCap) (fun _=>0)
      (frameOutput bits sourceCap lengthCap targetCap logCap) := by
  have h := (clock_step (AppendFrameKernel.ready bits)).pad
    (![sourceCap,lengthCap,targetCap,logCap] : Fin 4→Nat)
  have hin : (fun i => ZeroPadding.pad
      ((![sourceCap,lengthCap,targetCap,logCap] : Fin 4→Nat) i)
      (AppendFrameKernel.input bits i)) =
      frameInput bits sourceCap lengthCap targetCap logCap := by
    funext i
    fin_cases i <;> simp [AppendFrameKernel.input,frameInput,ZeroPadding.pad]
  have hout : (fun i => ZeroPadding.pad
      ((![sourceCap,lengthCap,targetCap,logCap] : Fin 4→Nat) i)
      (AppendFrameKernel.output bits i)) =
      frameOutput bits sourceCap lengthCap targetCap logCap := by
    funext i
    fin_cases i <;> simp [AppendFrameKernel.output,frameOutput]
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
    congr 1
    omega
  rw [hin,hout] at h
  exact h

abbrev eraseMachine (t : Nat) := RecoveryScratchErase.resetMachine t

def eraseInput {t : Nat} (capacity logCap : Nat) (A : Fin t→List Bool) :
    Fin (t+1+1)→List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1=>List.replicate capacity true))
    (fun _ : Fin 1=>List.replicate logCap false)

def eraseOutput (t capacity logCap : Nat) : Fin (t+1+1)→List Bool :=
  eraseInput capacity logCap (fun _ : Fin t=>List.replicate capacity false)

/-- Physically clear a whole fixed block, retaining its allocation and its
unary capacity driver. No logical zero-padding step is used as allocation. -/
theorem erase_step {t : Nat} (capacity logCap : Nat) (A : Fin t→List Bool)
    (hA : ∀ i,(A i).length ≤ capacity) (hlog : capacity+1 ≤ logCap) :
    Step (eraseMachine t) (2*capacity+4) (fun _=>0)
      (eraseInput capacity logCap A) (fun _=>0)
      (eraseOutput t capacity logCap) := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready capacity logCap A hA)
  rw [max_eq_left hlog] at h
  exact h

theorem dock_zero {t u : Nat} (slots : Fin t→Fin u) :
    dockH slots (fun _=>0) (fun _=>0) = fun _=>0 := by
  funext i
  unfold dockH
  cases RecoveryFocus.pick slots i <;> rfl

/-- Execute a restoring worker directly on its existing full-bank inputs. -/
theorem focus_existing {m t st fuel : Nat} {p : Machine m st}
    {input output : Fin m→List Bool}
    (h : Step p fuel (fun _=>0) input (fun _=>0) output)
    (slots : Fin m→Fin t) (injective : Function.Injective slots)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hH : ∀ i,H (slots i)=0) (hA : ∀ i,A (slots i)=input i) :
    Step (RecoveryFocus.machine slots p) fuel H A H (install slots A output) := by
  have hheads : dockH slots H (fun _=>0)=H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH,hp]
      exact (hH j).symm.trans (congrArg H he)
  have htapes := install_existing slots A input hA
  simpa only [hheads,htapes] using h.focus slots injective H A

/-- Rewind a produced raw word from its actual append position, preserving
both that word and the common reusable log reserve. -/
theorem rewind_step (word : List Bool) (pos capacity logCap : Nat)
    (hpos : pos≤capacity) (hlog : capacity≤logCap) :
    Step CompetitorRecordRewind.machine (2*capacity+2) (![pos,0,0])
      (![word,List.replicate capacity true,List.replicate logCap false])
      (fun _=>0) (![word,List.replicate capacity true,List.replicate logCap false]) := by
  obtain ⟨r,hr,hf,hs⟩ := CompetitorRecordRewind.rewind_run word capacity pos hpos
  have h := (Step.of_run hr (congrArg Configuration.heads hf)
    (congrArg Configuration.tapes hf)).pad (![0,0,logCap] : Fin 3→Nat)
  have hin : (fun i => ZeroPadding.pad ((![0,0,logCap] : Fin 3→Nat) i)
      ((CompetitorRecordRewind.cfg 0 word pos capacity 0 0 []).tapes i)) =
      (![word,List.replicate capacity true,List.replicate logCap false] : Fin 3→List Bool) := by
    funext i
    fin_cases i <;> simp [CompetitorRecordRewind.cfg,ZeroPadding.pad]
  have hout : (fun i => ZeroPadding.pad ((![0,0,logCap] : Fin 3→Nat) i)
      ((CompetitorRecordRewind.cfg 2 word 0 capacity 0 0 (List.replicate capacity false)).tapes i)) =
      (![word,List.replicate capacity true,List.replicate logCap false] : Fin 3→List Bool) := by
    funext i
    fin_cases i <;> simp [CompetitorRecordRewind.cfg]
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
    congr 1
    omega
  dsimp only [CompetitorRecordRewind.cfg] at hin
  rw [hin,hout] at h
  exact h.congr (by funext i;fin_cases i <;> rfl) rfl

/-- A focused field operation gives its literal full-bank join, preserving
all ambient tapes and heads outside the four selected ports. -/
theorem frame_docked {t : Nat} (slots : Fin 4→Fin t)
    (injective : Function.Injective slots) (H : Fin t→Nat) (A : Fin t→List Bool)
    (bits : List Bool) (sourceCap lengthCap targetCap logCap : Nat)
    (hlog : 2*bits.length+1 ≤ logCap) :
    Step (RecoveryFocus.machine slots frameMachine) (4*bits.length+4)
      (dockH slots H (fun _=>0))
      (install slots A (frameInput bits sourceCap lengthCap targetCap logCap))
      (dockH slots H (fun _=>0))
      (install slots A (frameOutput bits sourceCap lengthCap targetCap logCap)) :=
  (frame_step bits sourceCap lengthCap targetCap logCap hlog).focus slots injective H A

end
end CycleFields.Primitives
