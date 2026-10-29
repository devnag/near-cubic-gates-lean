import SourceAdapters.Proximity.SourceQueryRows
import SourceAdapters.Proximity.DecisionAssignments

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": every truth-table bit is computed by the actual CW19
source decision program, on its dependent answer domain, in ascending binary
assignment order. The result is the exact input of the finite block compiler. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State)
open DecisionAssignments

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem source_decision_table (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk : ℕ) (pre tail : List Bool) (m : Fin MM) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ Wd) (hrow : a.env QueryStep.rowReg = coins.val)
    (hcount : a.env QueryStep.countReg = (V S).queryCount coins)
    (hl : a.env SourceRequests.lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hempty : a.kin = []) (hcursor : a.rc m = 0)
    (hstore : (a.ram m).length ≤ 2 ^ q)
    (hroom : ∀ bits : BitInput q,
      (proofCallInput V (decisionRequest V ⟨S, coins,
        fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩)).length ≤ Lk)
    (hbudget : ∀ bits : BitInput q, budget (decisionRequest V ⟨S, coins,
        fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩) ≤ Bk) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (DecisionTable.tableProgram m (inputs q)) a
      (2 ^ q * DecisionTable.passCost C (sourceCircuitWord S) coins.val q + 1)
      (fun b => DecisionTable.Tabled m a b [] (a.ram m) (rows (rowPredicate (V S) coins)) ∧
        b.ram m = (List.ofFn (predicateTable (rowPredicate (V S) coins))).map Bool.toNat) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  have e := DecisionTable.table_program C m (sourceCircuitWord S) pre tail coins.val
    ((V S).queryCount coins) q hW rfl (rows (rowPredicate (V S) coins)) a [] (a.ram m)
    hc hrow hcount hl hip hempty rfl hcursor
    (fun r hr => (row_width _ r hr).le) ?_
  · rw [rows_inputs, rows_length] at e
    refine e.mono le_rfl (fun b hb => ⟨hb, ?_⟩)
    rw [hb.ram_eq, Function.update_self, List.nil_append, rows_values, rows_length,
      List.drop_eq_nil_of_le hstore, List.append_nil]
  · intro r hr
    obtain ⟨code, rfl⟩ := List.mem_ofFn.mp hr
    refine ⟨decisionRequest V ⟨S, coins,
      fun i => assignment code (Fin.castLE ((V S).queryCount_le coins) i)⟩, ?_, hroom _, hbudget _, ?_⟩
    · exact source_decision_input V S coins (assignment code)
    · exact source_decision_output V proofLength honest S coins (assignment code)

end NearCubicGates.Adapters.Proximity.SourceCallee
