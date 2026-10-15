import Proof.Amplification.RecoveryPCPFormulaResumeCountCold
import Proof.Amplification.RecoveryPaddedCopyWhole
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! The physical first randomness field comes from the retained R driver
and blank input. The existing width-controlled copier writes every frame
marker, every zero bit and the closing delimiter, including width zero. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRandomCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem zero_data (R : Nat) : RecoveryColdPaddedCopy.data [] R=List.replicate R false := by
  have hz : readTapeBit ([] : List Bool)=(fun _=>false) := by funext i; rfl
  have hm (xs : List Nat) : xs.map (fun _=>false)=List.replicate xs.length false := by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simp only [List.map_cons,List.length_cons,List.replicate_succ,ih]
  simpa only [RecoveryColdPaddedCopy.data,hz,List.length_range] using hm (List.range R)

def input (R : Nat) : Fin 4→List Bool := ![[],[],CompareMachine.word R,[]]
theorem random_ready (R : Nat) : ∃ out,
    ClockJoin.ReadyRun RecoveryColdPaddedCopy.machine (4*R+8) (input R) out ∧
      out 1=frame (List.replicate R false) ∧ out 2=CompareMachine.word R := by
  obtain ⟨base,hbase,bt,bh,bs⟩ := RecoveryColdPaddedCopy.copy_ready [] R
  let caps : Fin 4→Nat := ![1,0,0,0]
  have hin : ZeroPadding.config caps (initialConfiguration RecoveryColdPaddedCopy.machine (input R))=
      initialConfiguration RecoveryColdPaddedCopy.machine ![frame [],[],CompareMachine.word R,[]] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _
  change runFrom RecoveryColdPaddedCopy.machine _ (initialConfiguration _ _)=some base at hbase
  rw [←hin] at hbase
  obtain ⟨r,hrun,rf,rs,_rp⟩ := ZeroPadding.run_unpad RecoveryColdPaddedCopy.machine caps _ _ base hbase
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,by omega⟩,?_,?_⟩
  · intro i
    exact (congrArg (fun c=>c.heads i) rf).trans (bh i)
  · have h:=(congrArg (fun c=>c.tapes 1) rf).trans (congrFun bt 1)
    change ZeroPadding.pad 0 (r.final.tapes 1)=frame (RecoveryColdPaddedCopy.data [] R) at h
    simpa only [ZeroPadding.pad_zero,zero_data] using h
  · have h:=(congrArg (fun c=>c.tapes 2) rf).trans (congrFun bt 2)
    exact (ZeroPadding.pad_zero _).symm.trans h

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRandomCold
