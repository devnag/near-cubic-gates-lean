import SourceAdapters.Proximity.SourceDecisionTable

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual row truth-table program, including a
paid rewind of its reused store and exact replacement of previous contents. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)

def tableStage (q : ℕ) (m : Fin MM) : Script :=
  .seq (.op (.rwM m)) (DecisionTable.tableProgram m (DecisionAssignments.inputs q))

structure StoredTable (m : Fin MM) (a b : State) (values : List ℕ) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  kin_nil : b.kin = []
  ram_eq : b.ram = Function.update a.ram m values
  cursor_eq : b.rc = Function.update a.rc m values.length
  vars : Fr a b DecisionCalls.scratch

theorem StoredTable.constants {m : Fin MM} {a b : State} {values : List ℕ}
    (h : StoredTable m a b values) (hc : Cst a) : Cst b := Cst.of_fr hc h.vars (by decide)

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem table_stage (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (m : Fin MM) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ Wd) (hrow : a.env QueryStep.rowReg = coins.val)
    (hcount : a.env QueryStep.countReg = (V S).queryCount coins)
    (hl : a.env SourceRequests.lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hempty : a.kin = []) (hcursor : a.rc m ≤ 2 ^ q)
    (hstore : (a.ram m).length ≤ 2 ^ q) (hrowlen : coins.val.bits.length ≤ Λ)
    (hroom : ∀ bits : BitInput q,
      (proofCallInput V (decisionRequest V ⟨S, coins,
        fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩)).length ≤ Lk)
    (hbudget : ∀ bits : BitInput q, budget (decisionRequest V ⟨S, coins,
        fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩) ≤ Bk) :
    let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (tableStage q m) a
      (2 ^ q * (15 * (sourceCircuitWord S).length + 10 * Λ + 6 * q + Lk + Bk + 45) + 3)
      (fun b => StoredTable m a b ((List.ofFn (predicateTable (rowPredicate (V S) coins))).map Bool.toNat)) := by
  dsimp only
  let C := context V proofLength honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  let d := a.rew m
  have er := Ex.op (OpEx.rwM (C := C) m a)
  have hdC : Cst d := ⟨hc.z, hc.one, hc.two⟩
  have e := source_decision_table V proofLength honest budget P S coins Wd Lk Bk pre tail m d hdC
    hW hrow hcount hl hip hempty (by simp [d, DS.rew]) hstore hroom hbudget
  obtain ⟨b, cost, he, hcost, hb, hvalues⟩ := e
  refine ⟨b, a.rc m + 1 + cost + 1, Ex.seq er he, ?_, ?_⟩
  · have hp := Nat.mul_le_mul_left (2 ^ q) (by omega :
      15 * (sourceCircuitWord S).length + 10 * coins.val.bits.length + 6 * q + Lk + Bk + 44 ≤
      15 * (sourceCircuitWord S).length + 10 * Λ + 6 * q + Lk + Bk + 44)
    dsimp only [DecisionTable.passCost, C, context] at hcost
    nlinarith
  · refine ⟨hb.ip_eq, hb.out_eq, hb.kin_nil, ?_, ?_, hb.vars⟩
    · rw [hb.ram_eq, DecisionAssignments.rows_length]
      change Function.update a.ram m ([] ++ DecisionTable.values _ ++ (a.ram m).drop (2 ^ q)) = _
      rw [DecisionAssignments.rows_values, List.drop_eq_nil_of_le hstore]
      simp
    · rw [hb.cursor_eq]
      change Function.update (Function.update a.rc m 0) m (0 + (DecisionAssignments.rows _).length) = _
      rw [Function.update_idem, DecisionAssignments.rows_length]
      simp

end NearCubicGates.Adapters.Proximity.SourceCallee
