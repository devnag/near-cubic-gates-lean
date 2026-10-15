import Proof.MachineModel.NativeRound

/-! Canonical reusable states change only the source and append positions.
Every other ambient tape is the same actual initialized workspace. -/
namespace NearCubicWires.ExtIncidence.NativeState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def heads (H : Fin 277→ℕ) (pos : ℕ) (out : List Bool):=
  dockH bank H (extraH pos out)
noncomputable def tapes (A : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C : ℕ) (source out : List Bool):=install bank A (word data C source out)

theorem heads_eq (H J : Fin 277→ℕ) (pos : ℕ) (out : List Bool)
    (hb : ∀ i,J (bank i)=extraH pos out i) (ho : ∀ j,(∀ i,bank i≠j) → J j=H j) :
    J=heads H pos out:=by
  classical
  funext j
  by_cases hit : ∃ i,bank i=j
  · obtain ⟨i,rfl⟩:=hit
    exact (hb i).trans (dockH_slot bank bank_injective H _ i).symm
  · have hn : ∀ i,bank i≠j:=by intro i hi;exact hit ⟨i,hi⟩
    exact (ho j hn).trans (dockH_other bank H _ j hn).symm

theorem tapes_eq (A B : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C : ℕ) (source out : List Bool)
    (hb : ∀ i,B (bank i)=word data C source out i) (ho : ∀ j,(∀ i,bank i≠j) → B j=A j) :
    B=tapes A data C source out:=by
  classical
  funext j
  by_cases hit : ∃ i,bank i=j
  · obtain ⟨i,rfl⟩:=hit
    exact (hb i).trans (install_slot bank bank_injective A _ i).symm
  · have hn : ∀ i,bank i≠j:=by intro i hi;exact hit ⟨i,hi⟩
    exact (ho j hn).trans (install_other bank A _ j hn).symm

theorem round_step {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (mh : ∀ j,H (sources j)=0) (ma : ∀ j,A (sources j)=NativeMaster.words gs Q w j) :
    let source:=pre++stream (rawIndices ms)++tail
    let data:=NativeMaster.words gs Q w
    let C:=NativeMeasured.capacity gs Q w
    let appended:=out++(CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
      (MatrixScoreBatch.cutWord (NativeWidth.width gs Q))
    Step NativeRound.machine (NativeRound.budget gs Q w (rawIndices ms))
      (heads H pre.length out) (tapes A data C source out)
      (heads H (pre.length+(stream (rawIndices ms)).length) appended) (tapes A data C source appended):=by
  dsimp only
  obtain ⟨J,B,run,fields,keep⟩:=NativeRound.round_run gs ms Q w out pre tail hw hQ
    (heads H pre.length out) (tapes A _ _ _ out)
    (fun i=>dockH_slot bank bank_injective H _ i) (fun i=>install_slot bank bank_injective A _ i)
    (by intro j;exact (dockH_other bank H _ (sources j) (fun i=>NativeRound.bank_source_ne i j)).trans (mh j))
    (by intro j;exact (install_other bank A _ (sources j) (fun i=>NativeRound.bank_source_ne i j)).trans (ma j))
  exact run.congr
    (heads_eq H J _ _ (fun i=>(fields i).1) (fun j hj=>(keep j hj).1.trans (dockH_other bank H _ j hj)))
    (tapes_eq A B _ _ _ _ (fun i=>(fields i).2) (fun j hj=>(keep j hj).2.trans (install_other bank A _ j hj)))

end NearCubicWires.ExtIncidence.NativeState
