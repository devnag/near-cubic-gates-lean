import Proof.CaseAnalysis.RecoveryGrammarNodeRow
import Proof.PCP.PCPUnaryCopy
import Proof.MachineModel.ClockUnarySum

/-! Paid in-place addition of two retained unary grammar scalars. The
existing sum, erase and copy machines restore all heads and both logs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarScalarAdd
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def unary (B n : ℕ):=ZeroPadding.pad B (List.replicate n true)
def sumInput (a b B : ℕ) : Fin 4→List Bool:=
  ![unary B a,unary B b,List.replicate B false,List.replicate B false]
def sumOutput (a b B : ℕ) : Fin 4→List Bool:=
  ![unary B a,unary B b,unary B (a+b),List.replicate B false]

theorem padded_sum (a b B : ℕ) (hB : a+b+2≤B) :
    ClockJoin.ReadyRun ClockUnarySum.machine (2*(a+b)+6) (sumInput a b B) (sumOutput a b B) := by
  obtain ⟨r,rr,rt,rh,rs⟩:=ClockUnarySum.sum_ready a b
  let caps : Fin 4→ℕ:=fun _=>B
  obtain ⟨s,sr,st,ss,_⟩:=ZeroPadding.run_config ClockUnarySum.machine caps _ _ r rr
  have initial : ZeroPadding.config caps (initialConfiguration ClockUnarySum.machine
      ![List.replicate a true,List.replicate b true,[],[]])=
      initialConfiguration ClockUnarySum.machine (sumInput a b B) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  rw [initial] at sr
  refine ⟨s,sr,?_,?_,ss.le.trans rs⟩
  · rw [st]
    change (fun i=>ZeroPadding.pad (caps i) (r.final.tapes i))=_
    rw [rt]
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change ZeroPadding.pad B (List.replicate (a+b+2) false)=List.replicate B false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · intro i
    rw [st]
    exact rh i

def sumSlots : Fin 4→Fin 6:=![0,1,2,3]
def eraseSlots (target : Fin 3) : Fin 3→Fin 6:=![target.castAdd 3,4,5]
def copySlots : Fin 3→Fin 6:=![2,0,3]
noncomputable def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def erase (target : Fin 3):=RecoveryFocus.machine (eraseSlots target) (RecoveryScratchErase.resetMachine 1)
noncomputable def copy:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine sum (erase 0)) copy) (erase 2)
def input (a b B : ℕ) : Fin 6→List Bool:=
  ![unary B a,unary B b,List.replicate B false,List.replicate B false,List.replicate B true,List.replicate (B+1) false]
def summed (a b B : ℕ) : Fin 6→List Bool:=
  ![unary B a,unary B b,unary B (a+b),List.replicate B false,List.replicate B true,List.replicate (B+1) false]
def erased (a b B : ℕ) : Fin 6→List Bool:=
  ![List.replicate B false,unary B b,unary B (a+b),List.replicate B false,List.replicate B true,List.replicate (B+1) false]
def copied (a b B : ℕ) : Fin 6→List Bool:=
  ![unary B (a+b),unary B b,unary B (a+b),List.replicate B false,List.replicate B true,List.replicate (B+1) false]
def budget (a b B : ℕ):=4*(a+b)+4*B+21

theorem erase_ready (bits : List Bool) (B : ℕ) (h : bits.length≤B) :
    ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 1) (2*B+4)
      ![bits,List.replicate B true,List.replicate (B+1) false]
      ![List.replicate B false,List.replicate B true,List.replicate (B+1) false] := by
  obtain ⟨r,rr,rt,rh,rs⟩:=RecoveryScratchErase.erase_ready B (B+1) (fun _ : Fin 1=>bits) (by intro i;exact h)
  have hi : (Fin.addCases (m:=2) (n:=1) (motive:=fun _ : Fin 3=>List Bool)
      (Fin.addCases (m:=1) (n:=1) (motive:=fun _ : Fin 2=>List Bool)
        (fun _ : Fin 1=>bits) (fun _ : Fin 1=>List.replicate B true))
      (fun _ : Fin 1=>List.replicate (B+1) false))=![bits,List.replicate B true,List.replicate (B+1) false] := by
    funext i;fin_cases i <;> rfl
  rw [hi] at rr
  refine ⟨r,rr,?_,rh,rs.le⟩
  rw [rt,Nat.max_self]
  funext i;fin_cases i <;> rfl

theorem ready (a b B : ℕ) (hB : a+b+2≤B) :
    ClockJoin.ReadyRun machine (budget a b B) (input a b B) (input (a+b) b B) := by
  have h0:=(padded_sum a b B hB).focus sumSlots (by decide) (input a b B) (by intro i;fin_cases i <;> rfl)
  have e0 : install sumSlots (input a b B) (sumOutput a b B)=summed a b B := by
    funext i;fin_cases i <;> first
    | exact install_slot sumSlots (by decide) _ _ 0
    | exact install_slot sumSlots (by decide) _ _ 1
    | exact install_slot sumSlots (by decide) _ _ 2
    | exact install_slot sumSlots (by decide) _ _ 3
    | exact install_other sumSlots _ _ _ (by decide)
  rw [e0] at h0
  have h1:=(erase_ready (unary B a) B (by simp only [unary,ZeroPadding.pad_length,List.length_replicate];omega)).focus
    (eraseSlots 0) (by decide) (summed a b B) (by intro i;fin_cases i <;> rfl)
  have e1 : install (eraseSlots 0) (summed a b B)
      ![List.replicate B false,List.replicate B true,List.replicate (B+1) false]=erased a b B := by
    funext i;fin_cases i <;> first
    | exact install_slot (eraseSlots 0) (by decide) _ _ 0
    | exact install_slot (eraseSlots 0) (by decide) _ _ 1
    | exact install_slot (eraseSlots 0) (by decide) _ _ 2
    | exact install_other (eraseSlots 0) _ _ _ (by decide)
  rw [e1] at h1
  obtain ⟨cr,crun,ct,ch,cs⟩:=PCPUnaryCopy.copy_ready (a+b) B B B
  rw [max_eq_left (by omega : a+b+1≤B)] at ct
  have cp : ClockJoin.ReadyRun PCPUnaryCopy.machine (2*(a+b)+4)
      ![unary B (a+b),List.replicate B false,List.replicate B false]
      ![unary B (a+b),unary B (a+b),List.replicate B false]:=⟨cr,crun,ct,ch,cs.le⟩
  have h2:=cp.focus copySlots (by decide) (erased a b B) (by intro i;fin_cases i <;> rfl)
  have e2 : install copySlots (erased a b B)
      ![unary B (a+b),unary B (a+b),List.replicate B false]=copied a b B := by
    funext i;fin_cases i <;> first
    | exact install_slot copySlots (by decide) _ _ 0
    | exact install_slot copySlots (by decide) _ _ 1
    | exact install_slot copySlots (by decide) _ _ 2
    | exact install_other copySlots _ _ _ (by decide)
  rw [e2] at h2
  have h3:=(erase_ready (unary B (a+b)) B (by simp only [unary,ZeroPadding.pad_length,List.length_replicate];omega)).focus
    (eraseSlots 2) (by decide) (copied a b B) (by intro i;fin_cases i <;> rfl)
  have e3 : install (eraseSlots 2) (copied a b B)
      ![List.replicate B false,List.replicate B true,List.replicate (B+1) false]=input (a+b) b B := by
    funext i;fin_cases i <;> first
    | exact install_slot (eraseSlots 2) (by decide) _ _ 0
    | exact install_slot (eraseSlots 2) (by decide) _ _ 1
    | exact install_slot (eraseSlots 2) (by decide) _ _ 2
    | exact install_other (eraseSlots 2) _ _ _ (by decide)
  rw [e3] at h3
  have joined:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ h0 h1) h2) h3
  have cost : ((2*(a+b)+6+1+(2*B+4))+1+(2*(a+b)+4))+1+(2*B+4)=budget a b B:=by
    unfold budget
    omega
  rw [cost] at joined
  exact joined

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarScalarAdd
