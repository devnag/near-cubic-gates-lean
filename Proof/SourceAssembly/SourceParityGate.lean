import Proof.CaseAnalysis.RowsEstimatorParityCounter
import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock

/-! The physical symmetric bottom writer appends the exact ordinary native gate and declared support. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Gate
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
open CloseoutRowsEstimator RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fragment_run (close : Bool) (bits tail out : List Bool) (C : ℕ) (hC : 2*bits.length+1≤C) :
    Step (Fragment.reusable close) (4*bits.length+4) (![0,out.length,0])
      (![frame bits++tail,out,List.replicate C false]) (![0,(out++Fragment.word close bits).length,0])
      (![frame bits++tail,out++Fragment.word close bits,List.replicate C false]) := by
  have actual:=(Fragment.reusable_run close bits tail out).pad (![0,0,C])
  apply actual.congr_in ?_ ?_ |>.congr ?_ ?_
  · rfl
  · funext i;fin_cases i <;>simp [ZeroPadding.pad]
  · rfl
  · funext i;fin_cases i <;>simp [ZeroPadding.pad,Nat.add_sub_of_le hC]

def finishStrokes : List (Stroke 2):=
  [![some (fun _=>true),none],![some (fun _=>false),none],
   ![some (fun _=>true),none],![some (fun _=>true),none],
   ![some (fun _=>true),none],![some (fun _=>false),none],
   ![some (fun _=>true),none],![some (fun _=>false),none],
   ![some (fun _=>false),some (fun _=>false)]]
def ending : Fin 2→List Bool:=![Fragment.body (bitWeight false)++[false],[false]]
theorem finish_bytes (b : Bool) : (fun i=>word finishStrokes b i)=ending := by
  funext i;fin_cases i <;>rfl

def H (out : Fin 2→List Bool) : Fin 6→ℕ:=![1,1,0,(out 0).length,(out 1).length,0]
def A (q j C : ℕ) (tail : List Bool) (out : Fin 2→List Bool) : Fin 6→List Bool:=
  ![CompareMachine.word q,CompareMachine.word j,frame (natWord q)++tail,out 0,out 1,List.replicate C false]
def firstSlots : Fin 3→Fin 6:=![2,3,5]
def bodySlots : Fin 4→Fin 6:=![0,3,4,1]
def finalSlots : Fin 3→Fin 6:=![0,3,4]
noncomputable def first:=RecoveryFocus.machine firstSlots (Fragment.reusable false)
noncomputable def middle:=RecoveryFocus.machine bodySlots Identity.machine
noncomputable def last:=RecoveryFocus.machine finalSlots (Glyph.machine finishStrokes)
noncomputable def machine:=Composition.machine (Composition.machine first middle) last

theorem first_run (q j C : ℕ) (tail : List Bool) (out : Fin 2→List Bool)
    (hC : 2*(natWord q).length+1≤C) :
    Step first (4*(natWord q).length+4) (H out) (A q j C tail out)
      (H (![out 0++Fragment.body (natWord q),out 1]))
      (A q j C tail (![out 0++Fragment.body (natWord q),out 1])) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (fragment_run false (natWord q) tail (out 0) C hC)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (solve | intro i;fin_cases i <;>simp [H,A,firstSlots,Fragment.word])
  | (intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl))

theorem middle_run (q j C : ℕ) (tail : List Bool) (out : Fin 2→List Bool) (hj : j<q) :
    Step middle (40*q+40) (H out) (A q j C tail out)
      (H (fun i=>out i++Identity.written (Identity.onehot q j) i))
      (A q j C tail (fun i=>out i++Identity.written (Identity.onehot q j) i)) := by
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (Identity.identity_run q j out hj)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro i;fin_cases i <;>rfl)
  | (intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl))

theorem last_run (q j C : ℕ) (tail : List Bool) (out : Fin 2→List Bool) :
    Step last 18 (H out) (A q j C tail out) (H (fun i=>out i++ending i))
      (A q j C tail (fun i=>out i++ending i)) := by
  have raw:=word_run finishStrokes (readTapeBit (CompareMachine.word q) 1) (CompareMachine.word q) 1 out rfl
  simp only [show ∀ i,word finishStrokes (readTapeBit (CompareMachine.word q) 1) i=ending i from
    fun i=>congrFun (finish_bytes _) i] at raw
  refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ raw ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro i;fin_cases i <;>rfl)
  | (intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl))

theorem gate_run (q C : ℕ) (j : Fin q) (tail : List Bool) (out : Fin 2→List Bool)
    (hC : 2*(natWord q).length+1≤C) :
    Step machine (4*(natWord q).length+40*q+64) (H out) (A q j.val C tail out)
      (H (![out 0++frame (CloseoutRowsCircuitBottom.nativeWord (inputBitSupportedGate j)),
        out 1++frame (CloseoutRowsGateSupport.gateMembers (inputBitSupportedGate j).support)]))
      (A q j.val C tail (![out 0++frame (CloseoutRowsCircuitBottom.nativeWord (inputBitSupportedGate j)),
        out 1++frame (CloseoutRowsGateSupport.gateMembers (inputBitSupportedGate j).support)])) := by
  let firstOut : Fin 2→List Bool:=![out 0++Fragment.body (natWord q),out 1]
  let bodyOut : Fin 2→List Bool:=fun i=>firstOut i++Identity.written (Identity.onehot q j.val) i
  have actual:=((first_run q j.val C tail out hC).seq (middle_run q j.val C tail firstOut j.isLt)).seq
    (last_run q j.val C tail bodyOut)
  have time:4*(natWord q).length+4+1+(40*q+40)+1+18=4*(natWord q).length+40*q+64:=by omega
  rw [time] at actual
  have he : (fun i=>bodyOut i++ending i)=
      ![out 0++frame (CloseoutRowsCircuitBottom.nativeWord (inputBitSupportedGate j)),
        out 1++frame (CloseoutRowsGateSupport.gateMembers (inputBitSupportedGate j).support)] := by
    rw [identity_native,identity_support,Identity.identityMask_eq]
    have length : (Identity.onehot q j.val).length=q:=by simp [Identity.onehot];omega
    funext i;fin_cases i
    · change ((out 0++Fragment.body (natWord q))++Identity.written (Identity.onehot q j.val) 0)++
        (Fragment.body (bitWeight false)++[false])=_
      rw [Identity.write_eq]
      simp only [bottomWord,length,Fragment.frame_eq,Fragment.body,List.flatMap_append,List.append_assoc]
      rfl
    · change (out 1++Identity.written (Identity.onehot q j.val) 1)++[false]=_
      rw [Identity.write_eq]
      change (out 1++Fragment.body (Identity.onehot q j.val))++[false]=out 1++frame (Identity.onehot q j.val)
      rw [Fragment.frame_eq,List.append_assoc]
  rw [he] at actual
  exact actual

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Gate
