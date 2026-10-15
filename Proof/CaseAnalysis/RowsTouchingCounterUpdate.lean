import Proof.CaseAnalysis.RowsTouchingCounterPred
import Proof.CaseAnalysis.RowsTouchingSingleDock
import Proof.CaseAnalysis.WitnessHeaderSwitch

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.CounterUpdate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (P : ℕ) (nums : Fin 3→ℕ) (flag : Bool) (i : Fin 4):List Bool:=
  Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
    (fun j=>ZeroPadding.pad P (CompareMachine.word (nums j))) (fun _=>[flag]) i
def slots (field : Fin 3):Fin 1→Fin 4:=fun _=>field.castAdd 1
def reduced (nums : Fin 3→ℕ) (field : Fin 3):Fin 3→ℕ:=Function.update nums field (nums field-1)
noncomputable def pred (field : Fin 3):=RecoveryFocus.machine (slots field) CounterPred.machine
noncomputable def positive:=Composition.machine (pred 0) (pred 2)
def probe : Machine 4 1:=⟨0,0,fun _=>true,fun _ _=>none⟩
def mode (bits : Fin 4→Bool):Bool:=bits 3
noncomputable def machine:=CloseoutWitness.HeaderSwitch.machine probe positive (pred 1) (fun _=>true) mode
def after (nums : Fin 3→ℕ) (flag : Bool):Fin 3→ℕ:=
  if flag then reduced (reduced nums 0) 2 else reduced nums 1

theorem data_update (P : ℕ) (nums : Fin 3→ℕ) (flag : Bool) (field : Fin 3):
    Function.update (data P nums flag) (field.castAdd 1)
      (ZeroPadding.pad P (CompareMachine.word (nums field-1)))=data P (reduced nums field) flag:=by
  funext i
  refine Fin.addCases (m:=3) (n:=1) ?_ ?_ i
  · intro j
    have he:(j.castAdd 1=field.castAdd 1)↔j=field:=by
      constructor
      · intro h;exact Fin.ext (congrArg (fun x : Fin 4=>x.val) h)
      · intro h;rw [h]
    simp only [Function.update_apply,data,Fin.addCases_left,reduced,he]
    split <;> rfl
  · intro j
    have hne:j.natAdd 3≠field.castAdd 1:=by
      intro he
      have hv:=congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp only [Function.update_apply,data,Fin.addCases_right,hne,if_false]

theorem pred_run (P : ℕ) (nums : Fin 3→ℕ) (flag : Bool) (field : Fin 3) (hP:nums field+1≤P):
    Step (pred field) (2*nums field+7) (fun _=>0) (data P nums flag)
      (fun _=>0) (data P (reduced nums field) flag):=by
  have actual:=CounterPred.ready_run (nums field) P hP
  have innerStep:Step CounterPred.machine (2*nums field+7) (fun _=>0)
      (fun j=>data P nums flag (slots field j)) (fun _=>0)
      (fun _=>ZeroPadding.pad P (CompareMachine.word (nums field-1))):=by
    exact actual.congr_in rfl (by funext j;simp only [data,slots,Fin.addCases_left])
  have focused:=single_dock CounterPred.machine (slots field)
    (by intro a b _;exact Subsingleton.elim a b) (data P nums flag)
    (fun _=>ZeroPadding.pad P (CompareMachine.word (nums field-1))) 0
    (ZeroPadding.pad P (CompareMachine.word (nums field-1))) innerStep (by intro j;fin_cases j;rfl)
  exact focused.congr rfl (data_update P nums flag field)

theorem probe_run (A : Fin 4→List Bool):Step probe 0 (fun _=>0) A (fun _=>0) A:=by
  obtain ⟨r,run,rf,_⟩:=(Timed.refl probe (⟨0,fun _=>0,A⟩ : Configuration 4 1)).run (by rfl)
  exact Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem update_run (P : ℕ) (nums : Fin 3→ℕ) (flag : Bool) (hP:∀ i,nums i+1≤P):
    Step machine (2*nums 0+2*nums 1+2*nums 2+17) (fun _=>0) (data P nums flag)
      (fun _=>0) (data P (after nums flag) flag):=by
  obtain ⟨prior,hprior,ph,pt,_⟩:=probe_run (data P nums flag)
  have bit:mode prior.final.scanned=flag:=by
    change readTapeBit (prior.final.tapes 3) (prior.final.heads 3)=flag
    rw [ph,pt]
    rfl
  cases flag with
  | false=>
    obtain ⟨last,hl,lh,lt,_⟩:=pred_run P nums false 1 (hP 1)
    obtain ⟨r,run,rs,rh,rt⟩:=CloseoutWitness.HeaderSwitch.accepted probe positive (pred 1)
      (fun _=>true) mode 2 (Or.inr rfl) 0 (2*nums 1+7) (fun _=>0) (data P nums false)
      prior last hprior (by rw [ph,pt];exact hl) rfl (by rw [bit];rfl)
    have result:Step machine (0+1+(2*nums 1+7)+1) (fun _=>0) (data P nums false)
        (fun _=>0) (data P (after nums false) false):=⟨r,run,rh.trans lh,rt.trans lt,rs⟩
    exact result.enlarge (by omega)
  | true=>
    have h2:(reduced nums 0) 2=nums 2:=by simp [reduced]
    have first:=pred_run P nums true 0 (hP 0)
    have second:=pred_run P (reduced nums 0) true 2 (by rw [h2];exact hP 2)
    obtain ⟨last,hl,lh,lt,_⟩:=first.seq second
    obtain ⟨r,run,rs,rh,rt⟩:=CloseoutWitness.HeaderSwitch.accepted probe positive (pred 1)
      (fun _=>true) mode 1 (Or.inl rfl) 0 ((2*nums 0+7)+1+(2*(reduced nums 0) 2+7))
      (fun _=>0) (data P nums true) prior last hprior (by rw [ph,pt];exact hl) rfl (by rw [bit];rfl)
    have result:Step machine (0+1+((2*nums 0+7)+1+(2*(reduced nums 0) 2+7))+1)
        (fun _=>0) (data P nums true) (fun _=>0) (data P (after nums true) true):=
      ⟨r,run,rh.trans lh,rt.trans lt,rs⟩
    exact result.enlarge (by rw [h2];omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.CounterUpdate
