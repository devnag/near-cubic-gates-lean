import Proof.MachineModel.CountIndex
import Proof.MachineModel.BankMetadata
import Proof.CaseAnalysis.RowsProjectionReset

/-! The actual count converter accepts the bank's existing false backing.
Its short counted work never requires a second table-sized allocation. -/
namespace NearCubicWires.ExtIncidence.CountIndex
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padded (C w M : ℕ) (i : Fin 15):=ZeroPadding.pad C (input w M i)

theorem padded_run (C w M : ℕ) (hM : 0<M) (hw : M<2^w)
    (hC : budget w M+1≤C) : ∃ out,
    ClockJoin.ReadyRun machine (budget w M) (padded C w M) out ∧
      out 10=ZeroPadding.pad C (List.replicate w true) ∧
      out 11=ZeroPadding.pad C (frame (binary w (M-1))) ∧
      (∀ i,(out i).length≤C) := by
  obtain ⟨raw,⟨r,hr,rt,rh,rs⟩,_r1,r10,r11⟩:=index_run w M hM hw
  have bound (i : Fin 15) : (raw i).length≤C:=by
    rw [←rt]
    apply CloseoutRowsProjectionReset.scratch_support machine (budget w M) C _ r hr i rfl
    · change (input w M i).length≤C
      have hc:=hC
      unfold budget at hc
      simp only [input]
      split_ifs <;> simp only [List.length_replicate,List.length_nil] <;> omega
    · omega
  obtain ⟨a,ha,af,asteps,_⟩:=ZeroPadding.run_config machine (fun _=>C) _ _ r hr
  refine ⟨fun i=>ZeroPadding.pad C (raw i),⟨a,ha,?_,?_,asteps.le.trans rs⟩,?_,?_,?_⟩
  · rw [af]
    change (fun i=>ZeroPadding.pad C (r.final.tapes i))=_
    rw [rt]
  · intro i;rw [af];exact rh i
  · exact congrArg (ZeroPadding.pad C) r10
  · exact congrArg (ZeroPadding.pad C) r11
  · intro i
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (bound i)

end NearCubicWires.ExtIncidence.CountIndex
