import Proof.MachineModel.Runs
import Proof.MachineModel.Layout
import Proof.CaseAnalysis.RowsMetadataCopy

/-! The physical seam between the prepared native writer and the existing
row transaction. Rewind only the produced header, copy its paid C-cell
support into the consumer's initially blank header port, and execute the
consumer. All producer scratch and heads remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HeaderHandoff
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound

def tapes (t u : Nat) := (t+1)+(u+2)
def pack {t u : Nat} {α : Type} (A : Fin t→α) (log : α)
    (B : Fin u→α) (tail : Fin 2→α) : Fin (tapes t u)→α :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1=>log)) (Fin.addCases B tail)
def target {t u : Nat} (j : Fin u) : Fin (tapes t u) := (j.castAdd 2).natAdd (t+1)
def copySlots {t u : Nat} (src : Fin t) (dst : Fin u) : Fin 4→Fin (tapes t u) :=
  ![(src.castAdd 1).castAdd (u+2),target dst,
    ((0 : Fin 2).natAdd u).natAdd (t+1),((1 : Fin 2).natAdd u).natAdd (t+1)]
theorem target_injective {t u : Nat} : Function.Injective (@target t u) := by
  intro i j h;apply Fin.ext
  have h:=congrArg Fin.val h
  simp only [target,Fin.val_natAdd,Fin.val_castAdd] at h
  omega
theorem copy_injective {t u : Nat} (src : Fin t) (dst : Fin u) :
    Function.Injective (copySlots src dst) := by
  intro i j h
  have h:=congrArg Fin.val h
  have hf:=src.isLt;have ht:=dst.isLt
  fin_cases i <;> fin_cases j <;> simp [copySlots,target] at h ⊢ <;> omega

noncomputable def first {t u s : Nat} (p : Machine t s) (src : Fin t) :=
  TapeEmbedding.machine (u+2) (MaskedReset.machine p (fun i=>decide (i=src)))
noncomputable def copy {t u : Nat} (src : Fin t) (dst : Fin u) :=
  RecoveryFocus.machine (copySlots src dst) RecoveryBoundedTapeCopy.machine
noncomputable def last {t u s : Nat} (p : Machine u s) := RecoveryFocus.machine (@target t u) p
noncomputable def machine {t u s z : Nat} (p : Machine t s) (q : Machine u z)
    (src : Fin t) (dst : Fin u) := Composition.machine
  (Composition.machine (first (u:=u) p src) (copy src dst)) (last (t:=t) q)
def resetHeads {t : Nat} (H : Fin t→Nat) (src : Fin t) := fun i=>if i=src then 0 else H i
def extra (C : Nat) : Fin 2→List Bool := ![List.replicate C true,List.replicate (C+1) false]

theorem transfer {t u : Nat} (src : Fin t) (dst : Fin u)
    (HA : Fin t→Nat) (HB : Fin u→Nat) (A : Fin t→List Bool) (B : Fin u→List Bool)
    (word : List Bool) (C R : Nat) (ha : HA src=0) (hb : HB dst=0)
    (hw : A src=word) (ht : B dst=ZeroPadding.pad C word) (hc : word.length≤C) :
    Step (copy src dst) (2*C+4)
      (pack HA 0 HB (fun _=>0))
      (pack A (List.replicate R false) (Function.update B dst (List.replicate C false)) (extra C))
      (pack HA 0 HB (fun _=>0)) (pack A (List.replicate R false) B (extra C)) := by
  let H:=pack HA 0 HB (fun _ : Fin 2=>0)
  let old:=pack A (List.replicate R false) (Function.update B dst (List.replicate C false)) (extra C)
  have h:=(Step.of_ready (CloseoutRowsMetadataCopy.copy_ready word C hc)).dock
    (copySlots src dst) (copy_injective src dst) H old
    (by intro i;fin_cases i <;> simp [H,pack,copySlots,target,ha,hb])
    (by intro i;fin_cases i <;> simp [old,pack,copySlots,target,extra,
      CloseoutRowsMetadataCopy.input,hw])
  have hh : dockH (copySlots src dst) H (fun _=>0)=H := by
    apply dockH_existing
    intro i;fin_cases i <;> simp [H,pack,copySlots,target,ha,hb]
  refine h.congr hh ?_
  apply HierarchyAllocation.install_eq (copySlots src dst) (copy_injective src dst)
  · intro i;fin_cases i <;> simp [pack,copySlots,target,extra,CloseoutRowsMetadataCopy.output,hw,ht]
  · intro i hi
    revert hi
    refine Fin.addCases (m:=t+1) (n:=u+2) (fun j _=>?_) (fun j=>?_) i
    · simp only [old,pack,Fin.addCases_left]
    · refine Fin.addCases (m:=u) (n:=2) (fun j hi=>?_) (fun j _=>?_) j
      · have hn : j≠dst := by intro e;subst j;exact hi 1 rfl
        simp only [old,pack,Fin.addCases_left,Fin.addCases_right,Function.update_of_ne hn]
      · simp only [old,pack,Fin.addCases_right]

theorem run {t u s z : Nat} (p : Machine t s) (q : Machine u z)
    (src : Fin t) (dst : Fin u) (np nq C R : Nat)
    (HP JP : Fin t→Nat) (AP ZP : Fin t→List Bool)
    (HQ JQ : Fin u→Nat) (AQ ZQ : Fin u→List Bool) (word : List Bool)
    (hp : Step p np HP AP JP ZP) (hq : Step q nq HQ AQ JQ ZQ)
    (hph : HP src=0) (hqh : HQ dst=0) (hword : ZP src=word)
    (hinput : AQ dst=ZeroPadding.pad C word) (hC : word.length≤C) (hR : np≤R) :
    Step (machine p q src dst) (2*np+2*C+nq+8)
      (pack HP 0 HQ (fun _=>0))
      (pack AP (List.replicate R false) (Function.update AQ dst (List.replicate C false)) (extra C))
      (dockH (@target t u) (pack (resetHeads JP src) 0 HQ (fun _=>0)) JQ)
      (install (@target t u) (pack ZP (List.replicate R false) AQ (extra C)) ZQ) := by
  have reset:=hp.mask (fun i=>decide (i=src)) (by
    intro i hi;have he : i=src:=of_decide_eq_true hi;subst i;exact hph) hR
  have rh : (fun i=>if decide (i=src) then 0 else JP i)=resetHeads JP src := by
    funext i;simp [resetHeads]
  rw [rh] at reset
  have firstRun:=reset.embed (Fin.addCases HQ (fun _ : Fin 2=>0))
    (Fin.addCases (Function.update AQ dst (List.replicate C false)) (extra C))
  have middle:=transfer src dst (resetHeads JP src) HQ ZP AQ word C R
    (by simp [resetHeads]) hqh hword hinput hC
  have lastRun:=hq.dock (@target t u) target_injective
    (pack (resetHeads JP src) 0 HQ (fun _=>0)) (pack ZP (List.replicate R false) AQ (extra C))
    (by intro i;simp only [target,pack,Fin.addCases_left,Fin.addCases_right])
    (by intro i;simp only [target,pack,Fin.addCases_left,Fin.addCases_right])
  have joined:=(firstRun.seq middle).seq lastRun
  convert joined using 1 <;> first | rfl | omega

end NearCubicWires.P1Closure.HeaderHandoff
