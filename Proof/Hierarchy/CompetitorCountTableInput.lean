import Proof.Hierarchy.CompetitorCountTableLayout

/-! Exact projected final159 input after executing both banks. The native
35 tapes, same bank and U driver are reused in place; only Q/parity occupy
the new retained metadata tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem slot_extra (p : Program) (i : Fin 124) : slot p (i.natAdd 35)=
    if i=0 then old p (CompetitorCountBanks.bank p)
    else if i=2 then old p (CompetitorCountBanks.field p 44) else fresh p i := by
  fin_cases i <;> rfl

theorem prepared_input (p : Program) (q u : ℕ) (odd : Bool) (same : List Bool)
    (a : Fin (CompetitorCountBanks.tapes p) → List Bool)
    (hsame : a (CompetitorCountBanks.bank p)=same)
    (hU : a (CompetitorCountBanks.field p 44)=UnaryTemplate.tape u) :
    ∀ i,extend p q odd a (slot p i)=CompetitorFinalTable.input
      (fun j => a (CompetitorCountBanks.tableNative p j)) same q u odd i := by
  intro i
  refine Fin.addCases (m := 35) (n := 124) ?_ ?_ i <;> intro j
  · simp only [slot_native,extend_old,CompetitorFinalTable.input,Fin.addCases_left]
  · rw [slot_extra]
    by_cases h0 : j=0
    · subst j
      rw [if_pos rfl,extend_old,hsame]
      rfl
    by_cases h2 : j=2
    · subst j
      rw [if_neg (by decide),if_pos rfl,extend_old,hU]
      rfl
    · simp only [h0,h2,↓reduceIte,extend_fresh,metadata,CompetitorFinalTable.input,Fin.addCases_right]

theorem entry_context {n : ℕ} (b w p : ℕ) (state : State n)
    (out : Fin 34 → List Bool) (a : Fin 35 → List Bool)
    (ha : ∀ i,a i=CompetitorPlaneTableEntry.tapes out p i)
    (hc : TableContext b w state out) :
    TableContext b w state (fun i : Fin 34 => a (i.castAdd 1)) := by
  have he : (fun i : Fin 34 => a (i.castAdd 1))=out := by
    funext i
    rw [ha]
    simp only [CompetitorPlaneTableEntry.tapes,Fin.addCases_left]
  rw [he]
  exact hc

end NearCubicWires.RepairOrdinary.CompetitorCountTable
