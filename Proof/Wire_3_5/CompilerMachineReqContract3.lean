import Proof.Wire_3_5.CompilerMachineTopLoad

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation NearCubicWires.SupplierPrinter
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces

variable (a : DecompositionAlgorithm)

def nOut (R : C3Req) : ℕ := 2 * R.dRow

def C3Req.Load (aPar : ℕ) (R : C3Req) : Prop :=
  (Real.logb 2 R.V.length + R.m + Real.logb 2 R.P.Q +
      R.P.Q * R.d * Real.logb 2 ((poolChildren a R.P.gates R.P.flips).length + 1) ≤ (nOut R : ℝ) / 100) ∧
    (R.p ≤ (R.P.n + 1) ^ aPar ∧ R.P.width ≤ (R.P.n + 1) ^ aPar ∧
      (poolChildren a R.P.gates R.P.flips).length ≤ (R.P.n + 1) ^ aPar ∧ R.P.h ≤ (R.P.n + 1) ^ aPar ∧
      R.P.Q ≤ (R.P.n + 1) ^ aPar ∧ R.d ≤ (R.P.n + 1) ^ aPar ∧
      ∀ t ∈ R.V, (Nat.bits t.1.natAbs).length ≤ (R.P.n + 1) ^ aPar) ∧
    R.occBound a ≤ 2 ^ R.psi

/-- **The C3 v3 contract**: C3 v2 with alg:compiler's size hypotheses in the precondition. -/
def c3v3 (E : Envelope) (inputWord : C3Req → List Bool) (coef aPar : ℕ) : MachineContract E :=
  { c3v2 a E inputWord coef with pre := fun R => (R.Pre a ∧ (inputWord R).length ≤ 2 ^ R.psi) ∧ R.Load a aPar }

/-- **The error field holds for the reference** (C3 v2's, `c3v2_err`). -/
theorem c3v3_err (E : Envelope) (inputWord : C3Req → List Bool) (coef aPar : ℕ) :
    ∀ R, (c3v3 a E inputWord coef aPar).pre R →
      (c3v3 a E inputWord coef aPar).errSpec R ((c3v3 a E inputWord coef aPar).ref R) :=
  fun R h => c3v2_err a E inputWord coef R h.1

/-- **The useless inhabitant fails** (C3 v2's error field, `c3v2_not_nil`). -/
theorem c3v3_not_nil (E : Envelope) (inputWord : C3Req → List Bool) (coef aPar : ℕ) :
    ¬ (c3v3 a E inputWord coef aPar).errSpec uselessReq ([], uselessReq) :=
  c3v2_not_nil a E inputWord coef

/-! ## The input word -/

/-- The fields of the machine's input record: `1^{Q'}`, `1^{P_ex}` (the pool shape's label count), `1^m`, `1^h`, `1^{p+1}`, `1^{width}`, C3a's pool
stream (word (1)) and children table (word (2)), the expression, and the two framed header parts. -/
def c3Fields (R : C3Req) : List (List Bool) :=
  [List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true,
    List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true,
    (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame,
    Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) [], R.V.flatMap Poly.termRec ++ [false],
    frame (natWord R.dRow ++ natWord (R.p + 1)),
    frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)]

/-- **The machine's input word**: the load record of the fields. -/
def c3Input (R : C3Req) : List Bool :=
  Top.loadRec (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true)
    (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true)
    (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame)
    (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false])
    (frame (natWord R.dRow ++ natWord (R.p + 1)))
    (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols))

/-- The input word is the fields, framed one after another. -/
theorem c3Input_eq (R : C3Req) : c3Input a R = (c3Fields a R).flatMap frame := by
  simp [c3Input, c3Fields, Top.loadRec]

end NearCubicWires.WireExponent3_5.CompilerMachine.Req
