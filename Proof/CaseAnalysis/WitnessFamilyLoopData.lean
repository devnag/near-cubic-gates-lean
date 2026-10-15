import Proof.CaseAnalysis.WitnessFamilyRound

/-! The exact outer list addresses one sum per source variable. Its
invariant carries only the zero accumulator and the three ordered
logical streams. The successor bank is projected from the same receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def entry {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L k : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts : List Bool)
    (word : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  let coeffs:=TermLoop.emitted (FamilyRound.coefficientWord C) words out j
  let natives:=TermLoop.emitted (FamilyRound.nativeWord word) words native j
  let counters:=TermLoop.emitted FamilyRound.countWord words counts j
  (⟨(FamilyRound.machine circuit k q).start,
    FamilyLoad.heads (TermLoop.position words pre j) (SumDock.heads coeffs natives counters),
    FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity coeffs natives counters ambient)
      (pre++words.flatMap frame++tail)⟩ : Configuration 3063 _)

def project (tapes : Fin 3063 → List Bool) (i : Fin 94) :=
  tapes (((((SumFinish.nativeSlots i).castAdd 1705).castAdd 1).castAdd 528).castAdd 2)

theorem project_data (P H b core W L T : ℕ) (arity out native counts source : List Bool)
    (ambient : Fin 94 → List Bool) :
    project (FamilyLoad.data H (SumStorage.data P H b core W L T arity out native counts ambient) source)=ambient := by
  funext i
  simp only [project,FamilyLoad.data,Fin.addCases_left,SumStorage.data,SumDock.coreData,
    TermRound.data,SumFinish.data_native]

def successor {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L k sumCost : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts : List Bool)
    (circuitPass : List Bool → Bool) (word : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  (SumRound.passed C T q (words.getD j []) arity circuitPass,
    match runFrom (FamilyRound.machine circuit k q) sumCost
      (entry circuit P H C T core W L k q words arity pre tail out native counts word j ambient) with
    | none=>ambient
    | some r=>project r.final.tapes)

noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  RepeatMachine.machine (FamilyRound.machine circuit k q) (fun _ bits=>bits 724)
def budget (sumCost V : ℕ):=V*(sumCost+3)+3
def passed (C T : ℕ) (q : ℚ) (words : List (List Bool)) (arity : List Bool) (circuitPass : List Bool → Bool):=
  words.all (fun bits=>SumRound.passed C T q bits arity circuitPass)

theorem successor_flags {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L k sumCost : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts : List Bool)
    (circuitPass : List Bool → Bool) (word : List Bool → List Bool) (ambient : Fin 94 → List Bool) :
    (RepeatMachine.iterate
      (CountedReject.advance (successor circuit P H C T core W L k sumCost q words arity pre tail out native counts circuitPass word))
      words.length (0,ambient)).1=passed C T q words arity circuitPass := by
  rw [TermLoop.iterate_flag _ (fun j=>SumRound.passed C T q (words.getD j []) arity circuitPass)
    (by intro j bank;rfl)]
  exact TermLoop.range_all words (fun bits=>SumRound.passed C T q bits arity circuitPass)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
