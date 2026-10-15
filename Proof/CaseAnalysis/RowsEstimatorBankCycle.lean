import Proof.CaseAnalysis.RowsEstimatorBankCycleFields

/-! One actual reusable native call preserves every ambient port outside its bank. -/
namespace NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last:=RecoveryFocus.machine bank BankCount.optional
noncomputable def machine:=Composition.machine NativeBankPosition.machine last
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (ms : List (List ℕ)):=
  1+1+BankCount.optionalBudget gs.length (NativeMeasured.capacity gs Q w) Q w ms

theorem direction_outside (i : Fin 277) (hi : ∀ j,bank j≠i) : NativeBankPosition.directions i=.stay := by
  simp only [NativeBankPosition.directions,Ne.symm (hi 15),Ne.symm (hi 18),Ne.symm (hi 24),
    Ne.symm (hi 35),Ne.symm (hi 37),Ne.symm (hi 38),Ne.symm (hi 45),Ne.symm (hi 46),Ne.symm (hi 112),
    or_self,ite_false]

theorem cycle_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (hh : ∀ i,H (bank i)=NativeInitialize.extraH pre.length out i)
    (ha : ∀ i,A (bank i)=NativeInitializedPorts.word (NativeMaster.words gs Q w)
      (NativeMeasured.capacity gs Q w) (pre++stream (rawIndices ms)++tail) out i) :
    let C:=NativeMeasured.capacity gs Q w
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
      (MatrixScoreBatch.cutWord (NativeWidth.width gs Q))
    ∃ H' A',Step machine (budget gs Q w (rawIndices ms)) H A H' A' ∧
      (∀ i,H' (bank i)=NativeInitialize.extraH (pre.length+(stream (rawIndices ms)).length) word i ∧
        A' (bank i)=NativeInitializedPorts.word (fun _ : Fin 15=>[]) C
          (pre++stream (rawIndices ms)++tail) word i) ∧
      (∀ j,(∀ i,bank i≠j) → H' j=H j ∧ A' j=A j) := by
  dsimp only
  let source:=pre++stream (rawIndices ms)++tail
  let C:=NativeMeasured.capacity gs Q w
  let J : Fin 277→ℕ:=fun i=>(NativeBankPosition.directions i).apply (H i)
  obtain ⟨position,hposition,pfinal,_⟩:=DecompositionCountPosition.move_run NativeBankPosition.directions H A
  have moved : Step NativeBankPosition.machine 1 H A J A:=
    Step.of_run hposition (congrArg Configuration.heads pfinal) (congrArg Configuration.tapes pfinal)
  have jh (i : Fin 128) : J (bank i)=NativeBankPosition.heads pre.length out i:=
    NativeBankPosition.heads_bank H pre.length out hh i
  have hQp : Q ≤ NativeWidth.width gs Q:=by unfold NativeWidth.width;omega
  have hp : RowTupleFixedCapacity.width gs Q ≤ NativeWidth.width gs Q:=by unfold NativeWidth.width;omega
  obtain ⟨result,rr,_rs,nh,nt,sp,st,ch,ct,keep⟩:=BankCount.optional_retained_run gs ms (NativeWidth.width gs Q)
    (NativeAllocation.capacity gs Q) Q w out pre tail hw hQ hQp hp le_rfl (J ∘ bank) (A ∘ bank)
    (by intro i;exact (jh (BankCount.old i)).trans (NativeBankPosition.native_heads pre.length out i))
    (by intro i _h36 h52 h107;exact (ha (BankCount.old i)).trans (NativeBankInputs.base gs Q w source out i h52 h107))
    (by intro j;exact (jh (BankCount.slots j)).trans (NativeBankPosition.count_heads pre.length out j))
    (by intro j;exact (ha (BankCount.slots j)).trans (NativeBankInputs.count_input gs Q w source out j))
    (by intro j;exact (jh (BankCount.rawOld (BankExecution.slots j))).trans (NativeBankPosition.raw_heads pre.length out j))
    (by intro j;exact (ha (BankCount.rawOld (BankExecution.slots j))).trans (NativeBankInputs.raw_input gs Q w source out j))
  have focused:=(Step.of_run rr rfl rfl).dock bank bank_injective J A (fun _=>rfl) (fun _=>rfl)
  have whole:=moved.seq focused
  let Hout:=dockH bank J result.final.heads
  let Aout:=install bank A result.final.tapes
  have oh (i : Fin 128) : Hout (bank i)=result.final.heads i:=dockH_slot bank bank_injective J _ i
  have ot (i : Fin 128) : Aout (bank i)=result.final.tapes i:=install_slot bank bank_injective A _ i
  have field:=cleared (NativeMaster.words gs Q w) C pre.length (pre.length+(stream (rawIndices ms)).length)
    source out _ result.final.heads result.final.tapes nh nt sp (st.trans (ha 113)) ch ct
    (fun i hi=>⟨(keep i hi).1.trans (jh i),(keep i hi).2.trans (ha i)⟩)
  refine ⟨Hout,Aout,whole,?_,?_⟩
  · intro i
    exact ⟨(oh i).trans (field i).1,(ot i).trans (field i).2⟩
  · intro j hj
    refine ⟨?_,install_other bank A result.final.tapes j hj⟩
    rw [show Hout j=J j from dockH_other bank J result.final.heads j hj]
    dsimp [J]
    rw [direction_outside j hj]
    rfl

end NearCubicWires.ExtIncidence.EstimatorBankCycle
