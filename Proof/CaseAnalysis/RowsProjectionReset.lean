import Proof.CaseAnalysis.RowsRawRecord
import Proof.MachineModel.OrdinaryMaskedReset
import Proof.PCP.PCPSerializerTapeSupport
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryRowLookupTapes

/-! Projection contracts suffice for the paid reset/erase boundary. The
actual worker run, initial scratch support and physical drivers remain
premises. No final Williams/table-bank identity is required. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsProjectionReset
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reset_keeps {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool)
    (fuel cap : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source)
    (hstart : ∀ i, selected i = true → c.heads i = 0)
    (hcap : source.steps ≤ cap) :
    ∃ r, runFrom (MaskedReset.machine p selected) (2*source.steps+2)
        (ZeroPadding.config (Rewind.Workspace.capacities t cap)
          (Rewind.recording c 0)) = some r ∧
      r.steps ≤ 2*cap+2 ∧
      (∀ i : Fin t, r.final.tapes (i.castAdd 1) = source.final.tapes i) ∧
      (∀ i : Fin t, r.final.heads (i.castAdd 1) =
        if selected i then 0 else source.final.heads i) ∧
      r.final.tapes ((0 : Fin 1).natAdd t) = List.replicate cap false := by
  obtain ⟨r,rr,rf,rs,_⟩ := MaskedReset.workspace_run p selected fuel cap c source hr hstart hcap
  refine ⟨r,rr,?_,?_,?_,?_⟩
  · omega
  · intro i
    rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · intro i
    rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right]

theorem scratch_support {t s : ℕ} (p : Machine t s) (fuel cap : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source) (i : Fin t)
    (hh : c.heads i = 0) (ht : (c.tapes i).length ≤ cap)
    (hc : source.steps+1 ≤ cap) : (source.final.tapes i).length ≤ cap := by
  have h := PCPSerializerReuse.tape_support p fuel c source hr i cap 0
    (by omega) (ht.trans (Nat.le_max_left _ _))
  simpa only [zero_add,Nat.max_eq_left hc] using h

theorem erase_keeps {t u : ℕ} (slot : Fin (t+1+1) → Fin u)
    (hi : Function.Injective slot) (B : ℕ) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hh : ∀ j, H (slot j) = 0)
    (hb : ∀ i : Fin t, (A (slot ((i.castAdd 1).castAdd 1))).length ≤ B)
    (hd : A (slot (((0 : Fin 1).natAdd t).castAdd 1)) = List.replicate B true)
    (hl : A (slot ((0 : Fin 1).natAdd (t+1))) = List.replicate (B+1) false) :
    ∃ r, runFrom (RecoveryFocus.machine slot (RecoveryScratchErase.resetMachine t))
        (2*B+4) ⟨(RecoveryScratchErase.resetMachine t).start,H,A⟩ = some r ∧
      r.steps ≤ 2*B+4 ∧ r.final.heads = H ∧
      (∀ i : Fin t, r.final.tapes (slot ((i.castAdd 1).castAdd 1)) =
        List.replicate B false) ∧
      (∀ i : Fin u, (∀ j, slot j ≠ i) → r.final.tapes i = A i) := by
  have base := RecoveryScratchErase.erase_ready B (B+1)
    (fun i : Fin t => A (slot ((i.castAdd 1).castAdd 1))) hb
  obtain ⟨r,rr,rh,rt,rs⟩ := base.focus_at slot hi H A (by
    intro j
    refine Fin.addCases (m:=t+1) (n:=1) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m:=t) (n:=1) (fun i => ?_) (fun i => ?_) k
      · simp only [Fin.addCases_left]
      · rw [Subsingleton.elim i (0 : Fin 1)]
        simpa only [Fin.addCases_left,Fin.addCases_right] using hd
    · rw [Subsingleton.elim k (0 : Fin 1)]
      simpa only [Fin.addCases_right] using hl) hh
  refine ⟨r,rr,rs.le,rh,?_,?_⟩
  · intro i
    rw [rt,install_slot _ hi]
    simp only [Fin.addCases_left]
  · intro i hother
    rw [rt,install_other _ _ _ _ hother]

end NearCubicWires.RepairOrdinary.CloseoutRowsProjectionReset
