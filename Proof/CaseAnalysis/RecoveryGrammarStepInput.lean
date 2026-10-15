import Proof.CaseAnalysis.RecoveryGrammarBankBounds

/-! One concrete grammar-step configuration joins successive compiled
atoms with the same paid graph, actual count, stack backing and prototype. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (resultHeads resultData)
open RecoveryBoundedGrammarContinue (bank stackCapacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def entry {s : ℕ} (p : Machine 79 s) (fields : Fin 78→List Bool) (node B P : ℕ)
    (out stack packet source : List Bool) : Configuration 79 s:=
  ⟨p.start,resultHeads out.length stack.length,
    bank (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) B P⟩

theorem worker_entry {s : ℕ} (p : Machine 78 s) (driver : Fin 78→Bool)
    (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool) :
    ZeroPadding.config (stackCapacity P)
      (RecoveryBoundedGrammarWorker.entry p driver out stack
        (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) B)=
      entry (RecoveryBoundedGrammarWorker.machine p driver) fields node B P out stack packet source := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,RecoveryBoundedGrammarWorker.entry,Rewind.recording,Rewind.config,
        entry,resultHeads,Fin.addCases_left]
      rfl
    · intro j;fin_cases j;rfl
  · funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,RecoveryBoundedGrammarWorker.entry,Rewind.recording,Rewind.config,
        Rewind.Workspace.capacities,entry,bank,resultData,Fin.addCases_left,ZeroPadding.pad_zero]
    · intro j;fin_cases j
      change ZeroPadding.pad 0 (ZeroPadding.pad B [])=ZeroPadding.pad 0 (List.replicate B false)
      simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

theorem left_entry {s t : ℕ} (p : Machine 79 s) (q : Machine 79 t) (fields : Fin 78→List Bool)
    (node B P : ℕ) (out stack packet source : List Bool) :
    Composition.leftConfig t (entry p fields node B P out stack packet source)=
      entry (Composition.machine p q) fields node B P out stack packet source := rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
