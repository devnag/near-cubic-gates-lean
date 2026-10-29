import SourceAdapters.Proximity.SourceScalars

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact random-bit and at-most-q query-count calls
in the constructor's retained register bank, including every input copy. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg countReg)

def randomReg : Fin VV := 24

def countProgram : Script := SourceScalars.scalarTo countReg [false, true, false] [rowReg]
def randomProgram : Script := SourceScalars.scalarTo randomReg [false, false] []

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem source_count (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk : ℕ) (pre tail : List Bool) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ Wd) (hrow : a.env rowReg = coins.val)
    (hl : a.env SourceRequests.lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hroom : (proofCallInput V (countRequest V ⟨S, coins⟩)).length ≤ Lk)
    (hbudget : budget (countRequest V ⟨S, coins⟩) ≤ Bk)
    (hwidth : ((V S).queryCount coins).bits.length + 1 ≤ Wd) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C countProgram a
      (15 * (sourceCircuitWord S).length + Lk + Bk +
        10 * coins.val.bits.length + 10 * ((V S).queryCount coins).bits.length + 43)
      (fun b => SourceScalars.Retained countReg a b ((V S).queryCount coins)) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  have e := SourceScalars.scalar_to C countReg (by decide) [false, true, false]
    (sourceCircuitWord S) pre tail [rowReg] (countRequest V ⟨S, coins⟩) ((V S).queryCount coins) a hc
    hW (by decide) hl rfl hip hempty
    (by simp only [C, context, callee, count_input, SourceRequests.fieldsWord,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hrow]) hroom hbudget
    (count_output V proofLength honest ⟨S, coins⟩) hwidth
  simp only [SourceRequests.fieldsCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrow,
    List.length_cons, List.length_nil] at e
  exact e.mono (by dsimp only [C, context]; omega) (fun _ h => h)

theorem source_random (S : SourceCircuit) (Wd Lk Bk : ℕ) (pre tail : List Bool)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ Wd)
    (hl : a.env SourceRequests.lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hroom : (proofCallInput V (randomRequest V S)).length ≤ Lk)
    (hbudget : budget (randomRequest V S) ≤ Bk)
    (hwidth : (V S).randomBits.bits.length + 1 ≤ Wd) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C randomProgram a
      (15 * (sourceCircuitWord S).length + Lk + Bk + 10 * (V S).randomBits.bits.length + 34)
      (fun b => SourceScalars.Retained randomReg a b (V S).randomBits) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  have e := SourceScalars.scalar_to C randomReg (by decide) [false, false]
    (sourceCircuitWord S) pre tail [] (randomRequest V S) (V S).randomBits a hc
    hW (by simp) hl rfl hip hempty
    (by simp only [C, context, callee, random_input, SourceRequests.fieldsWord,
      List.flatMap_nil, List.append_nil]) hroom hbudget (random_output V proofLength honest S) hwidth
  simp only [SourceRequests.fieldsCost, List.map_nil, List.sum_nil, List.length_cons, List.length_nil] at e
  exact e.mono (by dsimp only [C, context]; omega) (fun _ h => h)

end NearCubicGates.Adapters.Proximity.SourceCallee
