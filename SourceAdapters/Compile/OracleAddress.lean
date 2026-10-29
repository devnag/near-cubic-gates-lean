import SourceAdapters.Joins.ComputationToCircuit
import Proof.Gates.Succinct.Points

/-!
proof of `thm:short-pcp-ours`, Step 4: literal ell-bit addresses agree with the ordinary natural-number
query interpretation. This also gives a nonconstant oracle-gate model check.
Little-endian address serialization uses the exact testBit/bitsValue inverse.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.Bindings.MW20

set_option autoImplicit false

/-- proof of `thm:short-pcp-ours`, Step 4: little-endian query serialization preserves every address,
including addresses with leading zeroes and the empty arity-zero address. -/
theorem fixedArityOracle_ofFn {ell : ℕ} (O : BitInput ell → Bool)
    (address : BitInput ell) :
    fixedArityOracle O (CanonicalBinary.bitsValue (List.ofFn address)) = O address := by
  unfold fixedArityOracle
  congr 1
  funext bit
  rw [NearCubicGates.Close.Succinct.testBit_bitsValue]
  simp

/-- proof of `thm:short-pcp-ours`, Step 4: an actual oracle node reads its earlier input wire. -/
def oneBitOracleCircuit : OracleCircuit 1 1 where
  nodes := [.input 0, .oracle (fun _ => 0)]
  output := ⟨1, by decide⟩
  wellFormed := by
    intro index
    fin_cases index <;> simp [OracleNode.WellFormedAt]

theorem oneBitOracleCircuit_eval (O : BitInput 1 → Bool) (input : BitInput 1) :
    oneBitOracleCircuit.eval O input = O input := by
  simp only [oneBitOracleCircuit, OracleCircuit.eval, OracleCircuit.values,
    List.foldl_cons, List.foldl_nil, OracleNode.eval]
  change O (fun _ : Fin 1 => input 0) = O input
  congr 1
  funext bit
  have h : bit = 0 := Fin.eq_zero bit
  subst bit
  rfl

theorem oneBitOracleCircuit_size : oneBitOracleCircuit.size = 2 := rfl

end NearCubicGates.Adapters.Compile
