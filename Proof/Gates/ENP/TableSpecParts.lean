import Proof.Gates.ENP.TableSpec
import Proof.Gates.ENP.TableEval
import Proof.Gates.ENP.TablePrefix
import Proof.Amplification.RecoveryPrefixCanonical
import Proof.Gates.WordPrograms.WMX

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairSource NearCubicWires.Bindings.MW20
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.CircuitInputCNF NearCubicWires.RepairRepresentation
open NearCubicGates.Close.WordPrograms NearCubicWires.SourceInterfaces

/-- The emitter's start state: the raw word (followed by `post`) on stream 0, every other stream empty, every head and
register at `0`. -/
def tStart (w : List Bool) : WState 3 40 where
  sh := fun _ => 0
  st := ![w, [], [], []]
  val := fun _ => 0
  cell := false

/-- The emitter's end states: stream 0 unchanged, stream 1 the marked graph, stream 2 scratch, stream 3 the info word;
every head and register at `0`. -/
def tFinish (w g junk info : List Bool) : WState 3 40 where
  sh := fun _ => 0
  st := ![w, g, junk, info]
  val := fun _ => 0
  cell := false

/-- The info word: the arity `n` and the output index `o` in unary, separated by one `false`. -/
def tInfo (n o : ℕ) : List Bool := List.replicate n true ++ false :: List.replicate o true

def tGraph {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : List Bool :=
  (TCirc.tCircuit C).nodes.flatMap RepairOrdinary.PCPPRequestNodeSchema.native

structure TProg where
  prog : WMX 3 40
  K : ℕ
  e : ℕ
  run : ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool), ∃ cap n junk,
    n ≤ K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ e ∧
    WXExec cap prog (tStart ((OracleOutput.word ⟨ℓ, C⟩) ++ post))
      (tFinish ((OracleOutput.word ⟨ℓ, C⟩) ++ post) (RepairOrdinary.Streaming.marks (tGraph C)) junk
        (tInfo (2 ^ ℓ) (TCirc.tCircuit C).output.val)) n

def TBytesSpec : Prop :=
  ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ),
    (OracleOutput.word ⟨ℓ, C⟩).length ≤
      ((TCirc.start ℓ).flatMap RepairOrdinary.PCPPRequestNodeSchema.native).length +
        ((TCirc.seed C 0).flatMap RepairOrdinary.PCPPRequestNodeSchema.native).length

def TFlagSpec : Prop :=
  ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ),
    RecoveryOracle.correctedSat (RecoveryQuery.code true
      (RecoveryFormulaPrefix.payload (circuitInputFormula (TCirc.tCircuit C))) 0 0) = true ↔
    ∃ t, Transfer.HonestTable C t

def TTableSpec : Prop :=
  ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (first : Transfer.FirstTable C),
    RecoveryPrefixBody.search true (RecoveryFormulaPrefix.payload (circuitInputFormula (TCirc.tCircuit C)))
      (2 ^ ℓ) [] = List.ofFn first.table

def TStageOf : Prop := Nonempty TProg → TFlagSpec → TTableSpec → TStageRuns

end NearCubicGates.Close.ENP
