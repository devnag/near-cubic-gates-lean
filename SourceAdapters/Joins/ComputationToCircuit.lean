import NineInputs

/-!
Bounded short oracle computation to the exact MW20 circuit model.
proof of `thm:short-pcp-ours` compiles the short verifier computation, never the original
long computation. The run budget below is supplied in unary; the consumer
must prove that this short budget is polynomial in n + natBitLength t + 1.
The random-prefix and proof-restriction arguments of proof of `thm:short-pcp-ours` are proved by the consumer, not compiler hypotheses.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.Bindings.MW20

set_option autoImplicit false

/-- proof of `thm:short-pcp-ours`: fixed short data, common seed/address width, and short clock. -/
structure OracleCompilationRequest where
  data : List Bool
  ell : ℕ
  fuel : ℕ

/-- proof of `thm:short-pcp-ours`; proof of `cor:short-pcp-clock`: the short clock is actual compiler input data. -/
def OracleCompilationRequest.word (r : OracleCompilationRequest) : List Bool :=
  RepairOrdinary.frame r.data ++
    RepairOrdinary.frame (List.replicate r.ell true) ++
    RepairOrdinary.frame (List.replicate r.fuel true)

/-- proof of `thm:short-pcp-ours`: all ell random bits are supplied to the short computation. -/
def OracleCompilationRequest.runInput (r : OracleCompilationRequest)
    (z : BitInput r.ell) : List Bool :=
  RepairOrdinary.frame r.data ++ RepairOrdinary.frame (List.ofFn z)

/-- proof of `thm:short-pcp-ours`: an ell-bit address is interpreted in little-endian order.
The consumer proves that meaningful proof reads have addresses below L_pi. -/
def fixedArityOracle {ell : ℕ} (O : BitInput ell → Bool) : ℕ → Bool :=
  fun address => O fun bit => address.testBit bit.val

/-- proof of `thm:short-pcp-ours`: the ordinary cost/size variable for this compiler. -/
def OracleCompilationRequest.measure (r : OracleCompilationRequest) : ℕ :=
  r.data.length + r.ell + r.fuel + 1

/-- X5(a), P06. Exact arities and DAG well-formedness are in `OracleCircuit`.
Every node counts because `OracleCircuit.size` is `nodes.length`.
Quantifiers: the program is fixed before its coefficient and degree; one
compiler handles every data word, width, and supplied short clock.
The source program's input tape contains the outer frame prescribed by
`OrdinaryOracleRuns`, around `runInput`; output is the framed singleton [true].
-/
def ComputationToCircuit : Prop :=
  ∀ p : OrdinaryOracleProgram, ∃ K d : ℕ,
    ∃ circuit : (r : OracleCompilationRequest) → OracleCircuit r.ell r.ell,
      -- proof of `thm:short-pcp-ours`: fixed polynomial coefficient.
      1 ≤ K ∧
      -- proof of `thm:short-pcp-ours`: exact negated bounded verdict, for every oracle and seed.
      (∀ (r : OracleCompilationRequest) (O : BitInput r.ell → Bool)
        (z : BitInput r.ell),
        (circuit r).eval O z = false ↔
          OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput z) [true] r.fuel) ∧
      -- proof of `thm:short-pcp-ours`: all nodes, including constants/input/oracle nodes.
      (∀ r, (circuit r).size ≤ K * r.measure ^ d) ∧
      -- proof of `thm:short-pcp-ours`: writing the precise native output word is charged.
      (∀ r, (OracleOutput.word ⟨r.ell, circuit r⟩).length ≤ K * r.measure ^ d) ∧
      -- proof of `thm:short-pcp-ours`; proof of `cor:short-pcp-clock`: one ordinary, uniformly bounded generator.
      Nonempty (WordFunction OracleCompilationRequest OracleCompilationRequest.word
        (fun r => OracleOutput.word ⟨r.ell, circuit r⟩)
        (fun r => K * r.measure ^ d))

end NearCubicGates.Adapters.Compile
