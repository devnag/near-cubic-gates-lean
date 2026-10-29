import SourceAdapters.Code.BinaryParsing
import SourceAdapters.Code.UnaryCopy

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": retaining the allocation prefix, reading the original
message length and computing balanced block sizes for total decoding. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderFront

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing BlockArithmetic

abbrev State := DS 12 0
abbrev Script := St 12 0

def script : Script := .seq (UnaryCopy.script 0 1) (.seq (addConstant 0 3 1)
  (.seq BinaryParsing.script (.seq (.op (.zero 3)) (.seq (addConstant 0 3 3)
    (.seq (addConstant 0 10 1) blockScript)))))

structure Ready (L n : ℕ) (a : State) : Prop where
  zero : a.env 0 = 0
  flag : a.env 1 = 0
  length : a.env 2 = n
  divisor : a.env 3 = 3
  first : a.env 6 = blockSize n 0
  second : a.env 7 = blockSize n 1
  third : a.env 8 = blockSize n 2
  one : a.env 10 = 1
  position : a.ip = L + 1 + (frame n.bits).length
  output : a.out = List.replicate L true ++ [false]
  callInput : a.kin = []
  callOutput : a.kout = []
  callPosition : a.kc = 0

theorem runs (C : Ctx) (L n : ℕ) (tail : List Bool)
    (hin : C.inp = List.replicate L true ++ false :: (frame n.bits ++ tail))
    (hcap : 2 * n + 6 + 2 ^ n.bits.length < 2 ^ C.Wd) :
    ∃ b, Ex C script a0 b (100 * (L + n.bits.length + 1)) ∧ Ready L n b := by
  have hpower : 1 ≤ 2 ^ n.bits.length := Nat.one_le_pow _ _ (by omega)
  have hwpos : 0 < C.Wd := by
    by_contra h
    have h0 : C.Wd = 0 := by omega
    rw [h0] at hcap
    norm_num at hcap
  have e1 := UnaryCopy.runs C (0 : Fin 12) 1 (by decide) (a0 : State) rfl L [] (frame n.bits ++ tail)
    (by simpa using hin) rfl
  let a1 := UnaryCopy.state (1 : Fin 12) (a0 : State) (0 + L + 1) 0 ([] ++ List.replicate L true ++ [false])
  have e2 := add_constant C (0 : Fin 12) 3 (by decide) 1 a1
    (by simp [a1, UnaryCopy.state, DS.set, a0])
    (by simp [a1, UnaryCopy.state, DS.set, a0]; omega)
  let a2 := a1.set 3 (a1.env 3 + 1)
  let pre := List.replicate L true ++ [false]
  have e3 := BinaryParsing.runs C a2 (by simp [a2, a1, UnaryCopy.state, DS.set, a0]) n.bits pre tail
    (by simpa [pre, List.append_assoc] using hin)
    (by simp [a2, a1, UnaryCopy.state, pre])
    (by simp [a2, a1, UnaryCopy.state, DS.set, a0, BinaryParsing.value_bits]; omega)
    (by simp [a2, a1, UnaryCopy.state, DS.set, a0]; omega)
  let a3 := BinaryParsing.state a2 (pre.length + 2 * n.bits.length + 1) 0
    (a2.env 2 + a2.env 3 * BinaryParsing.value n.bits) (a2.env 3 * 2 ^ n.bits.length)
  have e4 := Ex.op (OpEx.zero (C := C) (3 : Fin 12) a3)
  let a4 := a3.set 3 0
  have e5 := add_constant C (0 : Fin 12) 3 (by decide) 3 a4
    (by simp [a4, a3, BinaryParsing.state, a2, a1, UnaryCopy.state, DS.set, a0])
    (by simp [a4]; omega)
  let a5 := a4.set 3 (a4.env 3 + 3)
  have e6 := add_constant C (0 : Fin 12) 10 (by decide) 1 a5
    (by simp [a5, a4, a3, BinaryParsing.state, a2, a1, UnaryCopy.state, DS.set, a0])
    (by simp [a5, a4, a3, BinaryParsing.state, a2, a1, UnaryCopy.state, DS.set, a0]; omega)
  let a6 := a5.set 10 (a5.env 10 + 1)
  have hn : a6.env 2 = n := by
    simp [a6, a5, a4, a3, BinaryParsing.state, a2, a1, UnaryCopy.state, DS.set, a0, BinaryParsing.value_bits]
  have e7 := block_script_exact C a6
    (by simp [a6, a5, a4, a3, BinaryParsing.state, a2, a1, UnaryCopy.state, DS.set, a0])
    (by simp [a6, a5, a4, DS.set]) (by rw [hn]; omega) (by omega)
  refine ⟨_, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6 e7)))))).mono (by omega), ?_⟩
  constructor
  all_goals simp [blockState, quotientState, a6, a5, a4, a3, BinaryParsing.state, a2, a1, UnaryCopy.state,
    DS.set, a0, BinaryParsing.value_bits, pre, frame_length, blockSize]
  omega

end NearCubicGates.Adapters.Code.DecoderFront
