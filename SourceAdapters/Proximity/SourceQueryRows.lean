import SourceAdapters.Proximity.SourceCallee

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the paid row loop specialized to the actual source
request domain and the proved ordinary dispatcher, with exact padded queries. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State)

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

def context (Wd : ℕ) (input : List Bool) (Lk Bk : ℕ) : Ctx :=
  ⟨Wd, input, callee V proofLength honest budget P, Lk, Bk⟩

theorem source_query_rows (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (m : Fin MM) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ Wd) (hwidth : Λ + 1 ≤ Wd) (hq : q < 2 ^ Wd)
    (hrow : a.env QueryStep.rowReg = coins.val)
    (hcount : a.env QueryStep.countReg = (V S).queryCount coins) (hbound : a.env QueryStep.boundReg = q)
    (hl : a.env SourceRequests.lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hempty : a.kin = []) (hcursor : a.rc m = 0)
    (hrowlen : coins.val.bits.length ≤ Λ) (hjlen : ∀ j < q, j.bits.length ≤ Λ)
    (haddrlen : ∀ i, (addressPair ((V S).query coins i)).2.bits.length ≤ Λ)
    (hroom : ∀ i, (proofCallInput V (queryRequest V ⟨S, coins, i⟩)).length ≤ Lk)
    (hbudget : ∀ i, budget (queryRequest V ⟨S, coins, i⟩) ≤ Bk) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (QueryRows.queryRows m) a
      (q * (15 * (sourceCircuitWord S).length + Lk + Bk + 30 * Λ + 64) + 4)
      (fun b => QueryRows.Loaded m a b (fun i => addressPair ((V S).query coins i)) q) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  have e := QueryRows.query_rows C m (sourceCircuitWord S) pre tail coins.val
    ((V S).queryCount coins) q Λ (fun i => addressPair ((V S).query coins i))
    (fun i => queryRequest V ⟨S, coins, i⟩) a hc hW hwidth hq hrow hcount hbound hl rfl
    hip hempty hcursor hrowlen hjlen haddrlen
    (fun i => query_input V ⟨S, coins, i⟩) hroom hbudget
    (fun i => query_output V proofLength honest ⟨S, coins, i⟩)
  convert e using 1
  simp only [QueryStep.stepCost, C, context]

end NearCubicGates.Adapters.Proximity.SourceCallee
