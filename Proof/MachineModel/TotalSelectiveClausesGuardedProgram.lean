import Proof.Supplier.SelectiveClausesGuardDispatch

/-!
# Total clauses execution at the published ABI

The guarded stream agrees with the original clauses compiler whenever the
literal arity is positive.  At arity zero it emits exactly the structural
`true` wire required by the source compiler's empty decoded clause list.

`SelectiveClausesProgramRunner` is the smallest program-parametric replacement
for the old hard-wired clauses runner: only the program field is parameterized;
the request and output contracts are unchanged.
-/

namespace NearCubicWires.TotalSelectiveClausesGuardedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces

open private selectiveClausesInput selectiveClausesProgram
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

private theorem decodeThreeCNF_clauses_eq_nil_of_zero (decisionCode : ℕ) :
    (decodeThreeCNF 0 decisionCode).clauses = [] := by
  cases hlist : (decodeThreeCNF 0 decisionCode).clauses with
  | nil => rfl
  | cons clause clauses =>
      have literal := clause (0 : Fin 3)
      cases literal with
      | positive query =>
          have hquery := query.isLt
          exact False.elim (by omega)
      | negative query =>
          have hquery := query.isLt
          exact False.elim (by omega)

/-- The old clauses runner with only its hard-wired program made explicit.
Every request and output field remains the clauses ABI used by the frozen
compiler tower. -/
structure SelectiveClausesProgramRunner
    (program : NPOracleProgram) (n literalArity : ℕ) where
  bits : SelectiveState n → List ℕ → ℕ → ℕ
  fuel : SelectiveState n → List ℕ → ℕ → ℕ
  executes : ∀ (state : SelectiveState n) (values : List ℕ)
      (decisionCode : ℕ), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      totalSelectiveClausesRequest (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode →
    runNPOracleProgram program (bits state values decisionCode)
        (fuel state values decisionCode) entry =
      some
        (selectiveWireCode
          (selectiveCompileClauses state values
            (decodeThreeCNF literalArity decisionCode).clauses))

def totalSelectiveClausesBits {n literalArity : ℕ}
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ) : ℕ :=
  let request :=
    totalSelectiveClausesRequest (selectiveStateCode state) n
      (encodeTaggedList values) literalArity decisionCode
  if hzero : literalArity = 0 then
    max (natBitLength request) (selectiveClausesZeroBits state)
  else
    let runner :=
      selectiveClausesRunner n literalArity (Nat.pos_of_ne_zero hzero)
    max (natBitLength request) (runner.bits state values decisionCode)

def totalSelectiveClausesFuel {n literalArity : ℕ}
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ) : ℕ :=
  if hzero : literalArity = 0 then
    selectiveClausesZeroFuel state + 7
  else
    let runner :=
      selectiveClausesRunner n literalArity (Nat.pos_of_ne_zero hzero)
    runner.fuel state values decisionCode + 7

set_option maxHeartbeats 1600000 in
-- Both branches elaborate the frozen level-10 execution certificates.
theorem run_totalSelectiveClausesProgram {n literalArity : ℕ}
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ)
    (hordered : selectiveStateOrdered state) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        totalSelectiveClausesRequest (selectiveStateCode state) n
          (encodeTaggedList values) literalArity decisionCode) :
    runNPOracleProgram totalSelectiveClausesProgram
        (totalSelectiveClausesBits (literalArity := literalArity) state values
          decisionCode)
        (totalSelectiveClausesFuel (literalArity := literalArity) state values
          decisionCode) entry =
      some
        (selectiveWireCode
          (selectiveCompileClauses state values
            (decodeThreeCNF literalArity decisionCode).clauses)) := by
  by_cases hzero : literalArity = 0
  · subst literalArity
    have hdispatch := run_totalSelectiveClausesProgram_zero_of_run
      (selectiveStateCode state) n (encodeTaggedList values) decisionCode
      (selectiveClausesZeroBits state) (selectiveClausesZeroFuel state)
      (selectiveWireCode
        (selectiveCompileClauses state values
          (decodeThreeCNF 0 decisionCode).clauses))
      entry hentryPc hentryInput
      (by
        intro sourceEntry hsourcePc hsourceInput
        have hsourceInput' :
            sourceEntry.registers 0 =
              selectiveClausesInput (selectiveStateCode state) n
                (encodeTaggedList values) 0 decisionCode := by
          simpa only [totalSelectiveClausesRequest_eq_private] using hsourceInput
        have hrun := run_selectiveClausesZeroProgram state values decisionCode
          hordered sourceEntry hsourcePc hsourceInput'
        simpa [decodeThreeCNF_clauses_eq_nil_of_zero,
          selectiveCompileClauses] using hrun)
    simpa [totalSelectiveClausesBits, totalSelectiveClausesFuel] using hdispatch
  · let harity : 0 < literalArity := Nat.pos_of_ne_zero hzero
    let runner := selectiveClausesRunner n literalArity harity
    have hdispatch := run_totalSelectiveClausesProgram_positive_of_run
      (selectiveStateCode state) n (encodeTaggedList values) literalArity
      decisionCode (runner.bits state values decisionCode)
      (runner.fuel state values decisionCode)
      (selectiveWireCode
        (selectiveCompileClauses state values
          (decodeThreeCNF literalArity decisionCode).clauses))
      harity entry hentryPc hentryInput
      (by
        intro sourceEntry hsourcePc hsourceInput
        have hsourceInput' :
            sourceEntry.registers 0 =
              selectiveClausesInput (selectiveStateCode state) n
                (encodeTaggedList values) literalArity decisionCode := by
          simpa only [totalSelectiveClausesRequest_eq_private] using hsourceInput
        exact runner.executes state values decisionCode hordered sourceEntry
          hsourcePc hsourceInput')
    simpa [totalSelectiveClausesBits, totalSelectiveClausesFuel, hzero,
      runner, harity] using hdispatch

/-- Premise-free clauses family, including literal arity zero. -/
def totalSelectiveClausesRunner (n literalArity : ℕ) :
    SelectiveClausesProgramRunner totalSelectiveClausesProgram n literalArity where
  bits := fun state values decisionCode =>
    totalSelectiveClausesBits (literalArity := literalArity) state values
      decisionCode
  fuel := fun state values decisionCode =>
    totalSelectiveClausesFuel (literalArity := literalArity) state values
      decisionCode
  executes := by
    intro state values decisionCode hordered entry hentryPc hentryInput
    exact run_totalSelectiveClausesProgram state values decisionCode hordered
      entry hentryPc hentryInput

/-- On the positive branch the guarded and original clauses streams are
execution-equivalent at their respective certified resources. -/
theorem totalSelectiveClausesProgram_eq_original_of_pos
    {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ)
    (hordered : selectiveStateOrdered state) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        totalSelectiveClausesRequest (selectiveStateCode state) n
          (encodeTaggedList values) literalArity decisionCode) :
    runNPOracleProgram totalSelectiveClausesProgram
        (totalSelectiveClausesBits (literalArity := literalArity) state values
          decisionCode)
        (totalSelectiveClausesFuel (literalArity := literalArity) state values
          decisionCode) entry =
      runNPOracleProgram selectiveClausesProgram
        ((selectiveClausesRunner n literalArity harity).bits state values
          decisionCode)
        ((selectiveClausesRunner n literalArity harity).fuel state values
          decisionCode) entry := by
  have hentryInput' :
      entry.registers 0 =
        selectiveClausesInput (selectiveStateCode state) n
          (encodeTaggedList values) literalArity decisionCode := by
    simpa only [totalSelectiveClausesRequest_eq_private] using hentryInput
  rw [run_totalSelectiveClausesProgram (literalArity := literalArity) state
    values decisionCode hordered entry hentryPc hentryInput]
  rw [(selectiveClausesRunner n literalArity harity).executes state values
    decisionCode hordered entry hentryPc hentryInput']

end NearCubicWires.TotalSelectiveClausesGuardedProgram
