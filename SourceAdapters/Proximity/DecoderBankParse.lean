import SourceAdapters.Proximity.CircuitInput
import SourceAdapters.Proximity.PrefixSizes
import SourceAdapters.Proximity.PhysicalRepeat
import Proof.Gates.CheckedPCPP.Glue

/-! Q04: actual target-word parsing and balanced-code frame loading. The input
size header is supplied by the already proved ordinary LengthPrefix program. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecoderBank

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.CheckedPCPP

abbrev State := WState 1381 16
abbrev Script := WM 1381 16

def inputWord (C : Circuit) := LengthPrefix.wrapped C.word

def initial (C : Circuit) : State := idealStart 1381 16 (inputWord C) (fun _ => 0)

def cap (C : Circuit) := 1000 * (C.word.length + 1)

def readLength : Script := readNatM true 0 0 1 9 2 3
def readArity : Script := readNatM true 0 0 1 8 2 3

def afterLength (C : Circuit) : State :=
  ((initial C).seth 0 (2 * (natWord C.word.length).length)).setv 9 C.word.length

def prefixLength (C : Circuit) := 2 * (natWord C.word.length).length + 2 * (natWord C.n).length

def afterArity (C : Circuit) : State :=
  ((afterLength C).seth 0 (prefixLength C)).setv 8 C.n

def numberCost (v : ℕ) := (natBitLength v + 2) * (40 * 2 ^ natBitLength v + 40)

theorem arity_bound (C : Circuit) : C.n ≤ 2 * (C.word.length + 1) :=
by
  have hn : C.n ≤ C.m := C.sizeAtLeast
  have hm := target_nodes_le_word C
  omega

theorem number_cap (C : Circuit) (v : ℕ) (hv : v ≤ 2 * (C.word.length + 1)) :
    2 ^ (natBitLength v + 1) ≤ cap C := by
  have h := DescW.pow_bitlen_le v
  rw [pow_succ]
  unfold cap
  omega

theorem read_length (C : Circuit) :
    WExec (cap C) readLength (initial C) (afterLength C) (numberCost C.word.length) := by
  have he := readNatM_spec (cap C) true (0 : Fin 1382) (0 : Fin 16) 1 9 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) C.word.length [] (frame C.word) (initial C)
    (by change frame (natWord C.word.length ++ C.word) = [] ++ enc true (natWord C.word.length) ++ frame C.word
        simpa only [List.nil_append, WireExponent3_5.PrimAsm.ParseNat.enc, if_true] using Streaming.frame_append (natWord C.word.length) C.word)
    rfl rfl rfl rfl rfl (by simpa [initial, idealStart] using number_cap C C.word.length (by omega))
  simpa only [readLength, afterLength, numberCost, stp, if_true, List.length_nil, Nat.zero_add,
    initial, idealStart] using he

theorem read_arity (C : Circuit) :
    WExec (cap C) readArity (afterLength C) (afterArity C) (numberCost C.n) := by
  have he := readNatM_spec (cap C) true (0 : Fin 1382) (0 : Fin 16) 1 8 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) C.n (Streaming.marks (natWord C.word.length))
    (frame (decoderBits C)) (afterLength C)
    (by change frame (natWord C.word.length ++ (natWord C.n ++ decoderBits C)) = _
        rw [Streaming.frame_append, Streaming.frame_append]
        simp only [WireExponent3_5.PrimAsm.ParseNat.enc, if_true, List.append_assoc])
    (by simp [afterLength, Streaming.marks_length])
    (by simp [afterLength, initial, idealStart]) (by simp [afterLength, initial, idealStart])
    (by simp [afterLength, initial, idealStart]) (by simp [afterLength, initial, idealStart])
    (by simpa [afterLength, initial, idealStart] using number_cap C C.n (arity_bound C))
  simpa only [readArity, afterArity, numberCost, stp, if_true, Streaming.marks_length,
    prefixLength, afterLength, WState.setv_val, Function.update_of_ne (show (8 : Fin 16) ≠ 9 by decide),
    WState.seth_val, initial, idealStart, Nat.zero_add] using he

def loadBits : Script := .seq readLength (.seq readArity (Glue.copyFrameW 0 1 7))

def bitsLoaded (C : Circuit) : State :=
  (((afterArity C).sets 1 (frame (decoderBits C))).seth 0 (prefixLength C + 2 * (decoderBits C).length))

def bitsCost (C : Circuit) := numberCost C.word.length + 1 +
  (numberCost C.n + 1 + (32 * (decoderBits C).length + 16))

theorem load_bits (C : Circuit) : WExec (cap C) loadBits (initial C) (bitsLoaded C) (bitsCost C) := by
  let pre := Streaming.marks (natWord C.word.length) ++ Streaming.marks (natWord C.n)
  have hpre : pre.length = prefixLength C := by simp [pre, prefixLength, Streaming.marks_length]
  have hbits : (decoderBits C).length ≤ C.word.length := by
    simp only [Circuit.word, decoderBits, List.length_append]
    omega
  have he := Glue.copyFrameW_spec (cap C) (0 : Fin 1382) 1 (by decide) (7 : Fin 16)
    (decoderBits C) pre [] (afterArity C)
    (by change frame (natWord C.word.length ++ (natWord C.n ++ decoderBits C)) = _
        rw [Streaming.frame_append, Streaming.frame_append]
        simp only [pre, List.append_nil, List.append_assoc])
    (by simp [afterArity, hpre]) (by simp [afterArity, afterLength, initial, idealStart])
    (by simp [afterArity, afterLength, initial, idealStart])
    (by simp [afterArity, afterLength, initial, idealStart]) (by unfold cap; omega)
  have he' : WExec (cap C) (Glue.copyFrameW 0 1 7) (afterArity C) (bitsLoaded C)
      (32 * (decoderBits C).length + 16) := by
    rw [hpre] at he
    exact he.cast (cap C) rfl (by omega)
  exact WExec.seq (read_length C) (WExec.seq (read_arity C) he')

theorem number_cost (C : Circuit) (v : ℕ) (hv : v ≤ 2 * (C.word.length + 1)) :
    numberCost v ≤ 2000 * (C.word.length + 1) ^ 2 := by
  have hbits := NodeEmit.natBitLength_le v
  have hp := DescW.pow_bitlen_le v
  have h1 : natBitLength v + 2 ≤ 5 * (C.word.length + 1) := by omega
  have h2 : 40 * 2 ^ natBitLength v + 40 ≤ 280 * (C.word.length + 1) := by omega
  have hh := Nat.mul_le_mul h1 h2
  unfold numberCost
  nlinarith

theorem bits_cost (C : Circuit) : bitsCost C ≤ 10000 * (C.word.length + 1) ^ 2 := by
  have h1 := number_cost C C.word.length (by omega)
  have h2 := number_cost C C.n (arity_bound C)
  have hbits : (decoderBits C).length ≤ C.word.length := by
    simp only [Circuit.word, decoderBits, List.length_append]
    omega
  unfold bitsCost
  nlinarith

end NearCubicGates.Adapters.Proximity.DecoderBank
