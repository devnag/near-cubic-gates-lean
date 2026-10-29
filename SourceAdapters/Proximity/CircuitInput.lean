import SourceAdapters.Proximity.CircuitDecoder
import Proof.Gates.Interfaces.WordFn
import Proof.Gates.CheckedPCPP.DescW

/-!
Q01/Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual marked target arity parser. The input
is precisely the Program model's physical frame of Circuit.word. It leaves
the stream head at the circuit-code frame and the arity in a unary register.
This is the first stage of the explicit bank loader, not a complete codec.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.Interfaces

abbrev DecoderLoadState := WState 1 5

def arityParser : WM 1 5 := readNatM true 0 0 1 2 3 4

def arityParsedState (C : Circuit) : DecoderLoadState :=
  ((startState 1 5 C.word).seth 0 (2 * (natWord C.n).length)).setv 2 C.n

def arityParseBudget (C : Circuit) : ℕ :=
  (natBitLength C.n + 2) * (40 * 2 ^ natBitLength C.n + 40)

theorem arity_parser_run (C : Circuit) :
    WExec (8 * (C.word.length + 1)) arityParser (startState 1 5 C.word)
      (arityParsedState C) (arityParseBudget C) := by
  have hm := target_nodes_le_word C
  have hn : C.n ≤ C.m := C.sizeAtLeast
  have hp := NearCubicGates.Close.CheckedPCPP.DescW.pow_bitlen_le C.n
  have hcap : 2 ^ (natBitLength C.n + 1) ≤ 8 * (C.word.length + 1) := by
    rw [pow_succ]
    omega
  have he := readNatM_spec (8 * (C.word.length + 1)) true (0 : Fin 2)
    (0 : Fin 5) 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    C.n [] (frame (decoderBits C)) (startState 1 5 C.word)
    (by change frame (natWord C.n ++ decoderBits C) =
          WireExponent3_5.PrimAsm.ParseNat.enc true (natWord C.n) ++ frame (decoderBits C)
        exact Streaming.frame_append _ _)
    rfl rfl rfl rfl rfl (by simpa [startState] using hcap)
  simpa only [arityParser, arityParsedState, arityParseBudget, stp, if_true,
    List.length_nil, Nat.zero_add, startState] using he

/-- The remaining physical stream is exactly the framed raw balanced code. -/
theorem arity_parser_remainder (C : Circuit) :
    ((arityParsedState C).st 0).drop ((arityParsedState C).sh 0) = frame (decoderBits C) := by
  simp only [arityParsedState, WState.setv_st, WState.seth_st, WState.setv_sh,
    WState.seth_sh, Function.update_self, startState, Fin.val_zero, ↓reduceIte, Circuit.word,
    Streaming.frame_append, decoderBits]
  rw [← Streaming.marks_length (natWord C.n), List.drop_left]

/-- The parsing clock is polynomial in the actual target word length. -/
theorem arity_parser_budget (C : Circuit) :
    arityParseBudget C ≤ 1000 * (C.word.length + 1) ^ 2 := by
  have hm := target_nodes_le_word C
  have hn : C.n ≤ C.m := C.sizeAtLeast
  have hp := NearCubicGates.Close.CheckedPCPP.DescW.pow_bitlen_le C.n
  have hb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le C.n
  have h1 : natBitLength C.n + 2 ≤ 5 * (C.word.length + 1) := by omega
  have h2 : 40 * 2 ^ natBitLength C.n + 40 ≤ 200 * (C.word.length + 1) := by omega
  have hh := Nat.mul_le_mul h1 h2
  unfold arityParseBudget
  nlinarith

end NearCubicGates.Adapters.Proximity
