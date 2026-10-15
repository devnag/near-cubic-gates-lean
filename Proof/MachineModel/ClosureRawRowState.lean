import Proof.MachineModel.ClosureActualRawRow

/-! Normalize the actual raw-row exit at the whole-bank boundary.  This is
the reuse seam required by hrow, not a claim that next-row syntax is supplied.
The output buffer is resident zero padding; every other tape and the growing
raw-output cursor retain their exact identities. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RawRowState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RawRowJoin

theorem exit_heads {t : Nat} (port : Fin t) (out next : List Bool) :
    dockH (slots port) (heads t out) (RowPayloadReusable.heads next) = heads t next := by
  funext i
  refine Fin.addCases (m:=t+1) (n:=2) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=t) (n:=1) (fun k => ?_) (fun k => ?_) j
    · by_cases hk : k=port
      · subst k
        simpa [heads,RowPayloadReusable.heads,slots] using
          dockH_slot (slots port) (injective port) (heads t out) (RowPayloadReusable.heads next) 0
      · have off : ∀ z, slots port z ≠ (k.castAdd 1).castAdd 2 := by
          intro z he
          have hv := congrArg Fin.val he
          have ht := k.isLt
          fin_cases z <;> simp [slots] at hv
          · exact hk (Fin.ext hv.symm)
          all_goals omega
        rw [dockH_other _ _ _ _ off]
        simp only [heads,Fin.addCases_left]
    · have hz : k=0 := Subsingleton.elim _ _
      subst k
      simpa [heads,RowPayloadReusable.heads,slots] using
        dockH_slot (slots port) (injective port) (heads t out) (RowPayloadReusable.heads next) 2
  · fin_cases j
    · simpa [heads,RowPayloadReusable.heads,slots] using
        dockH_slot (slots port) (injective port) (heads t out) (RowPayloadReusable.heads next) 1
    · simpa [heads,RowPayloadReusable.heads,slots] using
        dockH_slot (slots port) (injective port) (heads t out) (RowPayloadReusable.heads next) 3

theorem exit_tapes {t : Nat} (port : Fin t) (B R : Nat)
    (Z : Fin t → List Bool) (out next : List Bool) :
    install (slots port) (bank (padded port B Z) R B out)
        (RowPayloadReusable.input [] next B R) =
      bank (padded port B (Function.update Z port [])) R B next := by
  funext i
  refine Fin.addCases (m:=t+1) (n:=2) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=t) (n:=1) (fun k => ?_) (fun k => ?_) j
    · by_cases hk : k=port
      · subst k
        have h := install_slot (slots port) (injective port)
          (bank (padded port B Z) R B out) (RowPayloadReusable.input [] next B R) 0
        simpa [slots,RowPayloadReusable.input,padded,caps,bank] using h
      · have off : ∀ z, slots port z ≠ (k.castAdd 1).castAdd 2 := by
          intro z he
          have hv := congrArg Fin.val he
          have ht := k.isLt
          fin_cases z <;> simp [slots] at hv
          · exact hk (Fin.ext hv.symm)
          all_goals omega
        rw [install_other _ _ _ _ off]
        simp only [bank,Fin.addCases_left,padded,Function.update_of_ne hk]
    · have hz : k=0 := Subsingleton.elim _ _
      subst k
      simpa [bank,RowPayloadReusable.input,slots] using
        install_slot (slots port) (injective port) (bank (padded port B Z) R B out)
          (RowPayloadReusable.input [] next B R) 2
  · fin_cases j
    · simpa [bank,RowPayloadReusable.input,slots] using
        install_slot (slots port) (injective port) (bank (padded port B Z) R B out)
          (RowPayloadReusable.input [] next B R) 1
    · simpa [bank,RowPayloadReusable.input,slots] using
        install_slot (slots port) (injective port) (bank (padded port B Z) R B out)
          (RowPayloadReusable.input [] next B R) 3

theorem run {t s : Nat} (p : Machine t s) (port : Fin t)
    (fuel b B R : Nat) (q : CompetitorValidity.Estimate) (count den : Nat)
    (A Z : Fin t → List Bool) (H : Fin t → Nat) (out : List Bool)
    (printed : Step p fuel (fun _ => 0) A H Z)
    (hword : Z port = CloseoutRowsEstimatorCoefficients.Stream.recordWord b q count den)
    (hf : fuel ≤ R) (hb : RowPayload.budget b ≤ B) (hR : B+1 ≤ R) :
    Step (machine p port) (budget fuel b B)
      (heads t out) (bank (padded port B A) R B out)
      (heads t (out++SignedSortKey.binary b count))
      (bank (padded port B (Function.update Z port [])) R B
        (out++SignedSortKey.binary b count)) := by
  have h := RawRowJoin.run p port fuel b B R q count den A Z H out printed hword hf hb hR
  exact h.congr (exit_heads port out _) (exit_tapes port B R Z out _)

end NearCubicWires.P1Closure.RawRowState
