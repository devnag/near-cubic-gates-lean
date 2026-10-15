import Proof.MachineModel.RoundRun

/-! Actual request transport followed by the same selected constructor. This
is the first composed part of the occurrence body; no source result is input. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

noncomputable def copyHeads (pre size : ℕ) (H : Fin (T a) → ℕ) :=
  dockH (copySlots a) H ![pre+size,0,0]
noncomputable def copyTapes (C : ℕ) (word source : List Bool) (A : Fin (T a) → List Bool) :=
  install (copySlots a) A ![source,ZeroPadding.pad C (frame word),List.replicate C false]
noncomputable def sourceHeads (pre size : ℕ) (H : Fin (T a) → ℕ) (KH : Fin (SB a) → ℕ) :=
  dockH (bk a) (copyHeads a pre size H) KH
noncomputable def sourceTapes (C : ℕ) (word source : List Bool) (A : Fin (T a) → List Bool)
    (K : Fin (SB a) → List Bool) := install (bk a) (copyTapes a C word source A) K
noncomputable def sourceRound:=Composition.machine (stage1 a) (stage2 a)

theorem source_round (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hbankT : ∀ i,A (bk a i)=List.replicate C false)
    (hbankH : ∀ i,H (bk a i)=0)
    (hstrT : A (str a)=pre++frame (nativeWord g)++rest) (hstrH : H (str a)=pre.length)
    (hfcpT : A (fcp a)=List.replicate C false) (hfcpH : H (fcp a)=0)
    (hC : (frame (nativeWord g)).length+Counted.budget a (request g) ≤ C) :
    ∃ (K : Fin (SB a) → List Bool) (KH : Fin (SB a) → ℕ),
      Step (sourceRound a) ((2*(frame (nativeWord g)).length+2)+1+Counted.budget a (request g)) H A
        (sourceHeads a pre.length (frame (nativeWord g)).length H KH)
        (sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K) ∧
      K (Counted.sourceTape a)=ZeroPadding.pad C (exactListWord (children a g)) ∧
      KH (Counted.sourceTape a)=0 ∧
      K (Counted.fresh a 9)=ZeroPadding.pad C (UnaryTemplate.tape (children a g).length) ∧
      KH (Counted.fresh a 9)=1 ∧ KH (Counted.localTape a 14)=0 ∧
      (∀ i,(K i).length ≤ C) := by
  have first:=stage1_step a C q g pre rest H A hbankT hbankH hstrT hstrH hfcpT hfcpH (by omega)
  obtain ⟨K,KH,last,kt,kh,ct,ch,fh,kb⟩:=stage2_step a C q g
    (copyHeads a pre.length (frame (nativeWord g)).length H)
    (copyTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A)
    (stage1_bankT a C q g pre rest A hbankT)
    (stage1_bankH a q g pre.length H hbankH) hC
  exact ⟨K,KH,first.seq last,kt,kh,ct,ch,fh,kb⟩

theorem source_head_bank (pre size : ℕ) (H : Fin (T a) → ℕ) (KH : Fin (SB a) → ℕ) (i : Fin (SB a)) :
    sourceHeads a pre size H KH (bk a i)=KH i :=
  dockH_slot (bk a) (bk_injective a) _ _ i

theorem source_tape_bank (C : ℕ) (word source : List Bool) (A : Fin (T a) → List Bool)
    (K : Fin (SB a) → List Bool) (i : Fin (SB a)) :
    sourceTapes a C word source A K (bk a i)=K i :=
  install_slot (bk a) (bk_injective a) _ _ i

theorem source_head_extra (pre size : ℕ) (H : Fin (T a) → ℕ) (KH : Fin (SB a) → ℕ) (j : Fin 12) :
    sourceHeads a pre size H KH (ex a j)=copyHeads a pre size H (ex a j) :=
  dockH_other (bk a) _ _ _ (fun i=>bk_ne_ex a i j)

theorem source_tape_extra (C : ℕ) (word source : List Bool) (A : Fin (T a) → List Bool)
    (K : Fin (SB a) → List Bool) (j : Fin 12) :
    sourceTapes a C word source A K (ex a j)=copyTapes a C word source A (ex a j) :=
  install_other (bk a) _ _ _ (fun i=>bk_ne_ex a i j)

end NearCubicWires.ExtDecompositionBatch
