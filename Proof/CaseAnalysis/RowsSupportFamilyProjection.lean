import Proof.CaseAnalysis.RowsSupportFamilyRun
import Proof.CaseAnalysis.WitnessFamilyLoopData

/-! These equalities concern only the old tape fields of the actual
support-bearing entry. The legacy circuit occurs only in this pure
projection; the support worker supplies the executed run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyWork
open LocalBitMultitape CloseoutWitness
open CloseoutWitness.SupportDock (lift)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem entry_heads {s s' : ℕ} (circuit : Machine 1704 s) (old : Machine 1703 s')
    (P H C T core W L k : ℕ) (q : ℚ) (words : List (List Bool))
    (arity pre tail out native counts supports : List Bool) (word supportWord : List Bool→List Bool)
    (j driver : ℕ) (ambient : Fin 94→List Bool) :
    heads (FamilyLoop.entry circuit P H C T core W L k q words arity pre tail out native counts supports word supportWord j ambient) driver=
      lift (CloseoutWitness.FamilyWork.heads
        (CloseoutWitness.FamilyLoop.entry old P H C T core W L k q words arity pre tail out native counts word j ambient) driver)
        (CloseoutWitness.TermLoop.emitted (FamilyRound.nativeWord supportWord) words supports j).length:=by
  simp only [heads,FamilyWork.core,FamilyLoop.entry,CloseoutWitness.FamilyWork.heads,
    CloseoutWitness.FamilyLoop.entry,lift,Fin.addCases_left]
  rfl

theorem entry_tapes {s s' : ℕ} (circuit : Machine 1704 s) (old : Machine 1703 s')
    (P H C T core W L k : ℕ) (q : ℚ) (words : List (List Bool))
    (arity pre tail out native counts supports : List Bool) (word supportWord : List Bool→List Bool)
    (j total : ℕ) (ambient : Fin 94→List Bool) (extra : Fin 177→List Bool) :
    tapes H total (FamilyLoop.entry circuit P H C T core W L k q words arity pre tail out native counts supports word supportWord j ambient) extra=
      lift (CloseoutWitness.FamilyWork.tapes H total
        (CloseoutWitness.FamilyLoop.entry old P H C T core W L k q words arity pre tail out native counts word j ambient) extra)
        (CloseoutWitness.TermLoop.emitted (FamilyRound.nativeWord supportWord) words supports j):=by
  simp only [tapes,FamilyWork.core,FamilyLoop.entry,CloseoutWitness.FamilyWork.tapes,
    CloseoutWitness.FamilyLoop.entry,lift,Fin.addCases_left]
  rfl

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyWork
