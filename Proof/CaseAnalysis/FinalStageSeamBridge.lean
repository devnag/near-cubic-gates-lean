import Proof.CaseAnalysis.FinalStageContracts
import Proof.CaseAnalysis.FinalSupplierStage

namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageSeamBridge

open LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation SourceInterfaces
open SupplierPipeline
open CompetitorRationalGap CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10WorkerChain RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerDockSeam RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10StageSeam
open C10LengthGate C10TailCompose C10BodyWidths C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The two retained width words, on one physical pair of tapes -/

theorem width_of_scratch {e : ℕ} (he : 58 ≤ e) (b : ℕ)
    (bank : Fin 218 → List Bool) (scratch : Fin e → List Bool)
    (h56 : scratch ⟨56, by omega⟩ = List.replicate b true)
    (h57 : scratch ⟨57, by omega⟩ =
      List.replicate (CompetitorRationalDecision.width b) true) :
    ∀ j, Fin.addCases bank scratch (retained e he j) = widthWord b j := by
  have key : ∀ (m : ℕ) (hm : m < 2) (hjv : 56 + m < e),
      Fin.addCases bank scratch (retained e he ⟨m, hm⟩) = scratch ⟨56 + m, hjv⟩ := by
    intro m hm hjv
    have hi : retained e he ⟨m, hm⟩ = (⟨56 + m, hjv⟩ : Fin e).natAdd 218 := by
      apply Fin.ext
      show 274 + m = 218 + (56 + m)
      omega
    rw [hi, Fin.addCases_right]
  rintro ⟨m, hm⟩
  interval_cases m
  · exact (key 0 (by omega) (by omega)).trans h56
  · exact (key 1 (by omega) (by omega)).trans h57

-- `StageData`'s own guard: `Proof/CaseAnalysis/FinalStageContracts.lean` makes the two
-- PCPP abbreviations opaque while the carrier structure is elaborated, and restores them
-- at `:77`.  `Parts` carries the same fields, so it needs the same guard.
attribute [local irreducible] pcppOf Atoms

structure Parts (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) : Type 1 where
  /-- `S.e = 60 + extra`; `extra` is S1's own scratch allowance above tape `277`. -/
  extra : ℕ
  /-- The prologue's state count. -/
  cs : Phase → ℕ
  
  calls : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (cs ph)
  
  callFuel : Phase → ℕ → ℕ
  /-- S-W's entry width. -/
  entryWidth : ℕ → ℕ
  /-- The number of call records the phase emits at length `n`. -/
  callCount : ℕ → ℕ
  /-- S-W's denominator. -/
  denominator : ℕ → ℕ
  /-- The residual length parameter of the `StageData`. -/
  L : ℕ → ℕ
  /-- The whole machine's fuel. -/
  budget : ℕ → ℕ
  /-- The coordinate expansion the exactness family pins. -/
  coordinate : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin ((pcppOf sources k p x bits).systematicBits + (pcppOf sources k p x bits).auxiliaryBits) →
      CircuitPolynomial (Atoms sources k p x bits) 1
  /-- The rational value the supplier answers with. -/
  supplier : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    List (Atoms sources k p x bits) → ℚ
  /-- Its numerator, the printed answer. -/
  answer : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    List (Atoms sources k p x bits) → ℕ
  /-- C.10.2's per-point failure. -/
  failure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  /-- C.10.2's coefficient mass. -/
  mass : (n : ℕ) → BitInput n → List Bool → Phase → ℝ

def stageData_of_parts (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (P : Parts sources k p) : StageData sources k p where
  e := 60 + P.extra
  st := C10SupplierStage.stageStates P.extra P.calls
  stage := C10SupplierStage.stage P.extra P.calls
  stageFuel := C10SupplierStage.stageFuel P.callFuel P.entryWidth P.callCount
  entryWidth := P.entryWidth
  denominator := P.denominator
  coordinate := P.coordinate
  supplier := P.supplier
  answer := P.answer
  failure := P.failure
  mass := P.mass
  L := P.L
  budget := P.budget

attribute [local semireducible] pcppOf Atoms

/-! ## Section 3  The seam -/

theorem stageReady_of_stageRun (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (P : Parts sources k p)
    (he : 58 ≤ (stageData_of_parts sources k p P).e)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (hlen : (records sources k p (stageData_of_parts sources k p P) x bits ph).length
      = P.callCount n)
    (hcalls : C10SupplierStage.CallsReady P.extra (P.calls ph) (P.callFuel ph n)
      (P.entryWidth n) (P.callCount n)
      (CloseoutRowsEstimatorCoefficients.Stream.words (P.entryWidth n)
        (records sources k p (stageData_of_parts sources k p P) x bits ph))
      (List.ofFn x) bits) :
    ∃ (bank : Fin 218 → List Bool) (scratch : Fin (stageData_of_parts sources k p P).e → List Bool),
      StageReady sources k p (stageData_of_parts sources k p P) he x bits ph bank scratch := by
  obtain ⟨bank, scratch, hstep, _h81, _h90, hready, hentry, h0, h1, _h216, hw56, hw57⟩ :=
    C10SupplierStage.stage_run (Atom := Atoms sources k p x bits) P.extra P.calls P.callFuel
      P.entryWidth P.callCount (P.answer n x bits) (P.denominator n) ph
      (pcppOf sources k p x bits) (P.coordinate n x bits) C10TotalDecode.Atom.systematic
      n x bits hlen hcalls
      (worker (Soundness.cutoff (constantsOf sources))
        (Fin.castAdd (60 + P.extra) inputTape) (Fin.castAdd (60 + P.extra) flag)
        (Fin.castAdd (60 + P.extra) result)
        (C10TailComposeUniform.body sources k p (stageData_of_parts sources k p P) ph))
      (by omega)
  refine ⟨bank, scratch, hstep, hready, hentry, h0, h1, rfl, ?_⟩
  have hwidth := width_of_scratch he
    (joinScalarWidth (P.entryWidth n)
      (records sources k p (stageData_of_parts sources k p P) x bits ph).length)
    bank scratch hw56 hw57
  intro j
  rw [hwidth j]
  unfold widthOf
  rw [foldWidth_eq_joinScalarWidth]
  rfl

end
end NearCubicWires.RepairSource.CloseoutFinal.C10StageSeamBridge
