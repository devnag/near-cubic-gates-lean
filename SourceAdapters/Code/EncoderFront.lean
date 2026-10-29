import SourceAdapters.Code.BlockArithmetic

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid message length, balanced block sizes and
input rewind, preparing the actual ordinary encoder's three source calls. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.EncoderFront

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing BlockArithmetic

abbrev State := DS 12 0
abbrev Script := St 12 0

def parseLength : Script := .seq (skipUnary 0 1) (countField 0 1 2)

def script : Script := .seq parseLength (.seq (addConstant 0 3 3) (.seq (addConstant 0 10 1)
  (.seq blockScript (.seq (.op (.copy 9 2)) (.seq (.op (.shl 9))
    (.seq (.op (.inc 9)) (rewindCount 0 10 9)))))))

structure Ready (L n : ℕ) (a : State) : Prop where
  zero : a.env 0 = 0
  flag : a.env 1 = 0
  length : a.env 2 = n
  divisor : a.env 3 = 3
  first : a.env 6 = blockSize n 0
  second : a.env 7 = blockSize n 1
  third : a.env 8 = blockSize n 2
  scratch : a.env 9 = 0
  one : a.env 10 = 1
  position : a.ip = L + 1
  output : a.out = []
  callInput : a.kin = []
  callOutput : a.kout = []
  callPosition : a.kc = 0

theorem runs (C : Ctx) (L : ℕ) (word : List Bool)
    (hin : C.inp = List.replicate L true ++ false :: frame word)
    (hcap : 2 * word.length + 6 < 2 ^ C.Wd) :
    ∃ b, Ex C script (a0 : State) b (100 * (L + word.length + 1)) ∧ Ready L word.length b := by
  have hwpos : 0 < C.Wd := by
    by_contra h
    have h0 : C.Wd = 0 := by omega
    rw [h0] at hcap
    norm_num at hcap
  have e1 := skip_unary C (0 : Fin 12) 1 (by decide) (a0 : State) rfl L [] (frame word)
    (by simpa using hin) rfl
  let a1 := flagged (1 : Fin 12) (a0 : State) (0 + L + 1) 0
  let pre := List.replicate L true ++ [false]
  have e2 := count_field C (0 : Fin 12) 1 2 (by decide) (by decide) (by decide)
    a1 (by simp [a1, flagged, DS.set, a0]) word pre []
    (by simpa [pre, List.append_assoc] using hin) (by simp [a1, flagged, pre])
    (by simp [a1, flagged, DS.set, a0]; omega)
  let a2 := counted (1 : Fin 12) 2 a1 (pre.length + 2 * word.length + 1) 0 (a1.env 2 + word.length)
  have e3 := add_constant C (0 : Fin 12) 3 (by decide) 3 a2
    (by simp [a2, a1, counted, flagged, DS.set, a0])
    (by simp [a2, a1, counted, flagged, DS.set, a0]; omega)
  let a3 := a2.set 3 (a2.env 3 + 3)
  have e4 := add_constant C (0 : Fin 12) 10 (by decide) 1 a3
    (by simp [a3, a2, a1, counted, flagged, DS.set, a0])
    (by simp [a3, a2, a1, counted, flagged, DS.set, a0]; omega)
  let a4 := a3.set 10 (a3.env 10 + 1)
  have e5 := block_script_exact C a4
    (by simp [a4, a3, a2, a1, counted, flagged, DS.set, a0])
    (by simp [a4, a3, a2, a1, counted, flagged, DS.set, a0])
    (by simp [a4, a3, a2, a1, counted, flagged, DS.set, a0]; omega) (by omega)
  let a5 := blockState a4
  have hn5 : a5.env 2 = word.length := by
    simp [a5, blockState, quotientState, a4, a3, a2, a1, counted, flagged, DS.set, a0]
  have e6 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 2 a5 (by decide))
  let a6 := a5.set 9 (a5.env 2)
  have e7 := Ex.op (OpEx.shl (C := C) (9 : Fin 12) a6 (by simp [a6, hn5]; omega))
  let a7 := a6.set 9 (2 * a6.env 9)
  have e8 := Ex.op (OpEx.inc (C := C) (9 : Fin 12) a7 (by simp [a7, a6, hn5]; omega))
  let a8 := a7.set 9 (a7.env 9 + 1)
  have e9 := rewind_count C (0 : Fin 12) 10 9 (by decide) (by decide) a8
    (by simp [a8, a7, a6, a5, blockState, quotientState, a4, a3, a2, a1, counted, flagged, DS.set, a0])
    (by simp [a8, a7, a6, a5, blockState, quotientState, a4, a3, a2, a1, counted, flagged, DS.set, a0])
    (L + 1) (2 * word.length + 1)
  have hi : rewindState (9 : Fin 12) a8 (L + 1 + (2 * word.length + 1)) (2 * word.length + 1) = a8 := by
    apply state_ext
    · funext i
      by_cases h : i = 9
      · subst i; simp [rewindState, a8, a7, a6, DS.set, hn5]
      · simp [rewindState, DS.set, h]
    · simp [rewindState, a8, a7, a6, a5, blockState, quotientState, a4, a3, a2, counted, pre]
      omega
    all_goals rfl
  rw [hi] at e9
  refine ⟨_, (Ex.seq (Ex.seq e1 e2) (Ex.seq e3 (Ex.seq e4
    (Ex.seq e5 (Ex.seq e6 (Ex.seq e7 (Ex.seq e8 e9))))))).mono (by omega), ?_⟩
  constructor
  all_goals simp [rewindState, a8, a7, a6, a5, blockState, quotientState, a4, a3, a2, a1,
    counted, flagged, DS.set, a0, blockSize]

end NearCubicGates.Adapters.Code.EncoderFront
