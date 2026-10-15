import Proof.CaseAnalysis.RecoverySuppliersProjectionInput

/-! Execute the original projector cold worker after the real capacity
outputs; its original normalized source and exact row bank are unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
open CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def projectionMachine (k d : ℕ):=RecoveryFocus.machine (projectionSlots source k d) RecoveryProjectionCold.machine
def projectionData (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool):=
  install (projectionSlots source k d) (capacityData source k d A C) P

theorem projection_run (k d R Q B : ℕ) (word : List Bool) (W : ℕ) (p : RawProjectionPCP)
    (A : Fin (tapes source k d)→List Bool) (H : Fin (tapes source k d)→ℕ) (C : Fin 49→List Bool)
    (hr : A (rBitsPort source k d)=frame R.bits) (hq : A (qBitsPort source k d)=frame Q.bits)
    (hquery : A (old source k d 106)=QueryBytes.framedCodes (normalizedRows p R Q).flatten)
    (hB : C 45=List.replicate B true)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→ A (old source k d i)=[])
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ A i=input source k d word W i)
    (hheads : ∀ i : Fin 158,H (old source k d i)=0)
    (hhr : H (rBitsPort source k d)=0) (hhq : H (qBitsPort source k d)=0)
    (hfarHeads : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ H i=0) :
    ∃ P r,runFrom (projectionMachine source k d) (RecoveryProjectionCold.budget R Q B)
      ⟨(projectionMachine source k d).start,H,capacityData source k d A C⟩=some r ∧
      r.steps≤RecoveryProjectionCold.budget R Q B ∧ r.final.heads=H ∧
      r.final.tapes=projectionData source k d A C P ∧
      (∀ i,P (RecoveryProjectionCold.bankSlots i)=
        RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B i) ∧
      P 106=RepairSource.VerifierDecoding.CompareMachine.word (2^R) ∧
      P 109=List.replicate R true ∧ P 111=List.replicate Q true ∧ P 104=List.replicate B true:=by
  obtain ⟨P,hp,hbank,_hRows,hRows,hR,hQ,hback⟩:=RecoveryProjectionCold.original_ready p R Q B
  obtain ⟨r,hrun,hh,ht,hs⟩:=hp.focus_at (projectionSlots source k d) (projection_injective source k d)
    H (capacityData source k d A C)
    (projection_input source k d R Q B word _ W A C hr hq hquery hB hblank hfar)
    (projection_heads source k d H hheads hhr hhq hfarHeads)
  exact ⟨P,r,hrun,hs,hh,ht,hbank,hRows,hR,hQ,hback⟩

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
