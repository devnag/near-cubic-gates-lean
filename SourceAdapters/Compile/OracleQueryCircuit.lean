import SourceAdapters.Compile.OracleDAGVector
import SourceAdapters.Compile.OracleQueryAddress

/-!
proof of `thm:short-pcp-ours`, Step 4: a genuine MW20 oracle gate receives the ell address wires
computed from the live framed query. Every address-expression node and the
oracle node itself are counted; no oracle truth table is inserted. This
segment is used in the complete computation compiler supplied by `computationToCircuit` in `OraclePrintMain.lean`.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit
  OracleExecution
set_option autoImplicit false

def compileQuery {n arity : ℕ} (builder : OracleDAGBuilder n arity) (width : ℕ)
    (wires : Fin (queryWordBits width) → LiveWire builder) :
    CompiledWire builder (fun O input => O (fun bit =>
      (queryAddressExpression width bit.val).eval (fun i => (wires i).function O input))) :=
  let addresses := compileVectorOnWires builder wires arity (fun bit => queryAddressExpression width bit.val)
  (compileOracle addresses.final addresses.live).prepend addresses.extension

theorem compileQuery_correct {n arity : ℕ} (builder : OracleDAGBuilder n arity) (width : ℕ)
    (wires : Fin (queryWordBits width) → LiveWire builder)
    (O : BitInput arity → Bool) (input : BitInput n) (bits padding : List Bool)
    (hw : (RepairOrdinary.frame bits++padding).length ≤ width)
    (he : ∀ i, (wires i).function O input=
      queryWordEncoding width (RepairOrdinary.frame bits++padding) i) :
    getElem? ((compileQuery builder width wires).final.values O input)
      (compileQuery builder width wires).output.val =
        some (fixedArityOracle O (CanonicalBinary.bitsValue bits)) := by
  rw [(compileQuery builder width wires).correct]
  have hv : (fun i => (wires i).function O input)=
      queryWordEncoding width (RepairOrdinary.frame bits++padding) := funext he
  rw [hv,queryAddress_oracle O width bits padding hw]

theorem compileQuery_added {n arity : ℕ} (builder : OracleDAGBuilder n arity) (width : ℕ)
    (wires : Fin (queryWordBits width) → LiveWire builder) :
    (compileQuery builder width wires).extension.suffix.length ≤
      arity*(width*(4*width+9)+1)+1 := by
  have h := compileVectorOnWires_added_le arity builder wires
    (fun bit => queryAddressExpression width bit.val) (width*(4*width+9)+1)
    (fun bit => queryAddressExpression_operations width bit.val)
  simpa [compileQuery,CompiledWire.prepend,compileOracle,OracleDAGExtension.trans,
    OracleDAGExtension.single] using Nat.add_le_add_right h 1

end NearCubicGates.Adapters.Compile.OracleExpressions
