import Proof.Rows.Plan
import Proof.MachineModel.FrameCopy
import Proof.MachineModel.UInputFields

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace RequestInputFields
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PacketProduction
noncomputable section

/-- These five fields are exactly Request.input, in its accepted order. -/
def values (a : DecompositionAlgorithm) (r : Request) : Fin 5 → List Bool :=
  ![r.nativeWord,r.supportWord a,
    FixedLivePackets.CyclicChoice.mask (r.family a).occurrences r.liveScale,
    r.indexWord a,r.topWord a]

def chunks (ws : Fin 5 → List Bool) : List (List Bool) :=
  [frame (ws 0),frame (ws 1),frame (ws 2),frame (ws 3),frame (ws 4)]
def word (ws : Fin 5 → List Bool) := (chunks ws).flatten
def leadWord (ws : Fin 5 → List Bool) (n : Nat) := ((chunks ws).take n).flatten
def tail (ws : Fin 5 → List Bool) (n : Nat) := ((chunks ws).drop n).flatten

theorem word_values (a : DecompositionAlgorithm) (r : Request) :
    word (values a r)=r.input a := by
  simp [word,chunks,values,Request.input,List.append_assoc]

def slots (j : Fin 5) : Fin 3 → Fin 13 :=
  ![1,⟨j.val+3,by omega⟩,⟨j.val+8,by omega⟩]
def unwrapSlots : Fin 3 → Fin 13 := ![0,1,2]

theorem injective (j : Fin 5) : Function.Injective (slots j) := by
  intro i k h
  have hv:=congrArg Fin.val h
  fin_cases i <;> fin_cases k <;> simp [slots] at hv ⊢

theorem unwrap_injective : Function.Injective unwrapSlots := by decide

theorem pick_slots (j : Fin 5) (i : Fin 13) : RecoveryFocus.pick (slots j) i =
    if i=1 then some 0 else if i.val=j.val+3 then some 1
    else if i.val=j.val+8 then some 2 else none := by
  fin_cases j <;> fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ (injective _) 0
    | exact RecoveryFocus.pick_slot _ (injective _) 1
    | exact RecoveryFocus.pick_slot _ (injective _) 2
    | decide

theorem pick_unwrap (i : Fin 13) : RecoveryFocus.pick unwrapSlots i =
    if i=0 then some 0 else if i=1 then some 1 else if i=2 then some 2 else none := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ unwrap_injective 0
    | exact RecoveryFocus.pick_slot _ unwrap_injective 1
    | exact RecoveryFocus.pick_slot _ unwrap_injective 2
    | decide

def heads (ws : Fin 5 → List Bool) (n : Nat) : Fin 13 → Nat :=
  fun i => if i=1 then (leadWord ws n).length else 0

def bank (ws : Fin 5 → List Bool) (n : Nat) : Fin 13 → List Bool :=
  ![frame (word ws),word ws,List.replicate (word ws).length false,
    if 0<n then frame (ws 0) else [],if 1<n then frame (ws 1) else [],
    if 2<n then frame (ws 2) else [],if 3<n then frame (ws 3) else [],
    if 4<n then frame (ws 4) else [],
    if 0<n then List.replicate (frame (ws 0)).length false else [],
    if 1<n then List.replicate (frame (ws 1)).length false else [],
    if 2<n then List.replicate (frame (ws 2)).length false else [],
    if 3<n then List.replicate (frame (ws 3)).length false else [],
    if 4<n then List.replicate (frame (ws 4)).length false else []]

def input (ws : Fin 5 → List Bool) : Fin 13 → List Bool :=
  fun i => if i=0 then frame (word ws) else []

def unwrap := RecoveryFocus.machine unwrapSlots Streaming.machine
def copy (j : Fin 5) := RecoveryFocus.machine (slots j) FrameCopy.machine
def machine := Composition.machine unwrap
  (Composition.machine (copy 0) (Composition.machine (copy 1)
    (Composition.machine (copy 2) (Composition.machine (copy 3) (copy 4)))))
def budget (ws : Fin 5 → List Bool) := 6*(word ws).length+17

theorem unwrap_run (ws : Fin 5 → List Bool) :
    Step unwrap (4*(word ws).length+2) (fun _ => 0) (input ws)
      (heads ws 0) (bank ws 0) := by
  obtain ⟨r,run,tapes,hs,_⟩:=UInputFields.unwrap_ready (word ws)
  have base:=Step.of_run run (funext hs) tapes
  have focused:=base.dock unwrapSlots unwrap_injective (fun _ => 0) (input ws)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl)
  apply focused.congr
  · funext i;fin_cases i <;> simp [dockH,pick_unwrap,heads,leadWord]
  · funext i;fin_cases i <;> simp [install,pick_unwrap,input,bank]

theorem split (ws : Fin 5 → List Bool) (j : Fin 5) :
    word ws=leadWord ws j.val++frame (ws j)++tail ws (j.val+1) := by
  fin_cases j <;> simp [word,leadWord,tail,chunks,List.append_assoc]

theorem copy_run (ws : Fin 5 → List Bool) (j : Fin 5) :
    Step (copy j) (2*(frame (ws j)).length+2)
      (heads ws j.val) (bank ws j.val)
      (heads ws (j.val+1)) (bank ws (j.val+1)) := by
  obtain ⟨r,run,final,_⟩:=FrameCopy.copy_run (leadWord ws j.val) (ws j) (tail ws (j.val+1))
  have base:=Step.of_run run (congrArg Configuration.heads final) (congrArg Configuration.tapes final)
  change Step FrameCopy.machine (2*(frame (ws j)).length+2)
    (![(leadWord ws j.val).length,0,0] : Fin 3 → Nat)
    ![leadWord ws j.val++frame (ws j)++tail ws (j.val+1),[],[]]
    (![(leadWord ws j.val).length+(frame (ws j)).length,0,0] : Fin 3 → Nat)
    ![leadWord ws j.val++frame (ws j)++tail ws (j.val+1),frame (ws j),
      List.replicate (frame (ws j)).length false] at base
  rw [←split ws j] at base
  have focused:=base.dock (slots j) (injective j) (heads ws j.val) (bank ws j.val)
    (by intro i;fin_cases j <;> fin_cases i <;> simp [heads,slots])
    (by intro i;fin_cases j <;> fin_cases i <;> simp [bank,slots])
  apply focused.congr
  · funext i
    fin_cases j <;> fin_cases i <;>
      simp [dockH,pick_slots,heads,leadWord,chunks] <;> omega
  · funext i
    fin_cases j <;> fin_cases i <;>
      simp [install,pick_slots,bank]

theorem run (ws : Fin 5 → List Bool) :
    Step machine (budget ws) (fun _ => 0) (input ws) (heads ws 5) (bank ws 5) := by
  have h:=(unwrap_run ws).seq ((copy_run ws 0).seq ((copy_run ws 1).seq
    ((copy_run ws 2).seq ((copy_run ws 3).seq (copy_run ws 4)))))
  have fuel : (4*(word ws).length+2)+1+
      ((2*(frame (ws 0)).length+2)+1+((2*(frame (ws 1)).length+2)+1+
      ((2*(frame (ws 2)).length+2)+1+((2*(frame (ws 3)).length+2)+1+
      (2*(frame (ws 4)).length+2)))))=budget ws := by
    simp only [budget,word,chunks,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil]
    omega
  rw [fuel] at h
  exact h

theorem request_run (a : DecompositionAlgorithm) (r : Request) :
    Step machine (6*(r.input a).length+17) (fun _ => 0)
      (fun i => if i=0 then frame (r.input a) else [])
      (heads (values a r) 5) (bank (values a r) 5) := by
  have h:=run (values a r)
  rw [budget,word_values] at h
  apply h.congr_in rfl
  funext i
  change (if i=0 then frame (word (values a r)) else [])=_
  rw [word_values]

end
end RequestInputFields
