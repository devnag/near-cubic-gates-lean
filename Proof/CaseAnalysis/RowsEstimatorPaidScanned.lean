import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidWarmRun

/-! The mandatory native rewind/scanner preserves the live scalar cursor
and the already owned seven metadata words in the same physical bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def scanSlots (a : WilliamsAlgorithm) (p : Program) (i : Fin 70) : Fin (tapes a p) :=
  old a p (WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p)))
noncomputable def scanner (a : WilliamsAlgorithm) (p : Program):=RecoveryFocus.machine (scanSlots a p) Scanned.machine
noncomputable def scanEntry (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool):=
  RecoveryFocus.config (scanSlots a p) (heads a p out) (input a p row C fields out) (Scanned.entry row C)

theorem scan_injective (a : WilliamsAlgorithm) (p : Program) : Function.Injective (scanSlots a p) := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin (tapes a p)=>z.val) h)

theorem scan_output (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (i : Fin 70) :
    input a p row C fields out (scanSlots a p i)=Scanned.output row C i := by
  simp only [input,scanSlots,old,Fin.addCases_left,public_old]

theorem scan_heads (a : WilliamsAlgorithm) (p : Program) (out : List Bool) (i : Fin 70) :
    heads a p out (scanSlots a p i)=0 := by
  simp only [scanSlots,heads,old,Fin.addCases_left,WarmPrepare.heads,WarmPrepared.old_ne,ite_false]

def ScanResult {u : ℕ} (slot : Fin 70 → Fin u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (row : EquationRow.Input) (C : ℕ) : Prop := ∃ r,
    runFrom (RecoveryFocus.machine slot Scanned.machine) (Scanned.budget row C)
      (RecoveryFocus.config slot H A (Scanned.entry row C))=some r ∧
      r.final.heads=H ∧ r.final.tapes=A ∧ r.steps ≤ Scanned.budget row C

theorem scan_focus {u : ℕ} (slot : Fin 70 → Fin u) (hi : Function.Injective slot)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (row : EquationRow.Input) (C : ℕ)
    (hC : (Header.stream row).length ≤ C) (hin : ∀ i,A (slot i)=Scanned.output row C i)
    (hh : ∀ i,H (slot i)=0) : ScanResult slot H A row C := by
  obtain ⟨base,hb,bt,bh,bs⟩:=Scanned.run row C hC
  obtain ⟨r,hr,rf,rs⟩:=RecoveryFocus.run_config slot hi Scanned.machine H A _ _ base hb
  refine ⟨r,hr,?_,?_,rs.le.trans bs⟩
  · rw [rf]
    funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he:=RecoveryFocus.slot_of_pick slot hp
      simpa only [RecoveryFocus.config,hp] using (bh j).trans ((hh j).symm.trans (congrArg H he))
  · rw [rf]
    change install slot A base.final.tapes=A
    rw [bt]
    exact install_existing slot A (Scanned.output row C) hin

theorem scan_run (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (hC : (Header.stream row).length ≤ C) :
    ScanResult (scanSlots a p) (heads a p out) (input a p row C fields out) row C :=
  scan_focus (scanSlots a p) (scan_injective a p) (heads a p out) (input a p row C fields out)
    row C hC (scan_output a p row C fields out) (scan_heads a p out)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
