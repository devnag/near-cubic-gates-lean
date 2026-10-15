import Proof.CaseAnalysis.RowsEstimatorBankCycle
import Proof.MachineModel.NativeReloadRetained

/-! The actual polynomial worker and one retained-metadata reload return
the reusable entry bank, ready for the next original raw polynomial. -/
namespace NearCubicWires.ExtIncidence.NativeRound
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bank_source_ne (i : Fin 128) (j : Fin 15) : bank i≠sources j:=by
  have hs : NativeMaster.fields j≠133:=by revert j;decide
  intro h
  have hv:=congrArg (fun a : Fin 277=>a.val) h
  simp only [bank,sources] at hv
  split_ifs at hv with hi
  · apply hs;apply Fin.ext;exact hv.symm
  · simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hb:=(NativeMaster.fields j).isLt
    omega

noncomputable def machine:=Composition.machine EstimatorBankCycle.machine NativeFanoutLayout.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (ms : List (List ℕ)):=
  EstimatorBankCycle.budget gs Q w ms+1+(2*NativeMeasured.capacity gs Q w+4)

theorem round_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (hh : ∀ i,H (bank i)=extraH pre.length out i)
    (ha : ∀ i,A (bank i)=word (NativeMaster.words gs Q w)
      (NativeMeasured.capacity gs Q w) (pre++stream (rawIndices ms)++tail) out i)
    (mh : ∀ j,H (sources j)=0) (ma : ∀ j,A (sources j)=NativeMaster.words gs Q w j) :
    let appended:=out++(CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
      (MatrixScoreBatch.cutWord (NativeWidth.width gs Q))
    ∃ H' A',Step machine (budget gs Q w (rawIndices ms)) H A H' A' ∧
      (∀ i,H' (bank i)=extraH (pre.length+(stream (rawIndices ms)).length) appended i ∧
        A' (bank i)=word (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w)
          (pre++stream (rawIndices ms)++tail) appended i) ∧
      (∀ j,(∀ i,bank i≠j) → H' j=H j ∧ A' j=A j):=by
  dsimp only
  obtain ⟨J,B,run,fields,keep⟩:=EstimatorBankCycle.cycle_run gs ms Q w out pre tail hw hQ H A hh ha
  have jh (j) : J (sources j)=0:=(keep (sources j) (fun i=>bank_source_ne i j)).1.trans (mh j)
  have ba (j) : B (sources j)=NativeMaster.words gs Q w j:=
    (keep (sources j) (fun i=>bank_source_ne i j)).2.trans (ma j)
  obtain ⟨D,reload,df,_ds,dk⟩:=NativeReload.reload_retained_run (NativeMaster.words gs Q w)
    (NativeMeasured.capacity gs Q w) _ _ _ (NativeMaster.words_fit gs Q w) J B jh ba
    (fun i=>(fields i).1) (fun i=>(fields i).2)
  refine ⟨J,D,run.seq reload,fun i=>⟨(fields i).1,df i⟩,?_⟩
  intro j hj
  exact ⟨(keep j hj).1,(dk j hj).trans (keep j hj).2⟩

end NearCubicWires.ExtIncidence.NativeRound
