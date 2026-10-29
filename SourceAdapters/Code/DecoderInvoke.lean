import SourceAdapters.Code.PaddedOutput
import SourceAdapters.Code.DecoderRequest

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": an actual total decoder call from a fully charged packet,
followed by exact message-length normalization of its capped output. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderInvoke

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def script : Script := .seq (.op (.zero 2)) (.seq (countField 0 1 2)
  (.seq (.op (.zero 11)) (.seq (countField 0 1 11) (.seq (.op (.copy 9 11))
    (.seq (.op (.shl 9)) (.seq (.op (.inc 9)) (.seq (rewindCount 0 10 9)
      (.seq (.op (.copy 9 11)) (.seq (sendChunk 0 10 1 9 true false)
        (.seq (.op (.rdI 1)) (.seq (.op .kcall) (.seq (.op (.copy 9 2)) PaddedOutput.script))))))))))))

theorem runs (C : Ctx) (request : C.K.Req) (n : ℕ) (word output pre tail : List Bool) (a : State)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hki : a.kin = [])
    (hin : C.inp = pre ++ frame (List.replicate n true) ++ frame word ++ tail) (hip : a.ip = pre.length)
    (hword : C.K.inw request = word) (hout : C.K.outw request = frame output)
    (hroom : word.length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hcap : 2 * word.length + 2 + n < 2 ^ C.Wd) :
    ∃ b, Ex C script a b (100 * (n + word.length + C.Lk + C.Bk + 1)) ∧
      b.env 0 = 0 ∧ b.env 10 = 1 ∧ b.kin = [] ∧
      b.ip = pre.length + (frame (List.replicate n true)).length + (frame word).length ∧
      b.out = a.out ++ PaddedOutput.resize output n := by
  have e1 := Ex.op (OpEx.zero (C := C) (2 : Fin 12) a)
  let a1 := a.set 2 0
  have e2 := count_field C (0 : Fin 12) 1 2 (by decide) (by decide) (by decide)
    a1 (by simp [a1, DS.set, hz]) (List.replicate n true) pre (frame word ++ tail)
    (by simpa [List.append_assoc] using hin) (by simp [a1, hip]) (by simp [a1]; omega)
  let a2 := counted (1 : Fin 12) 2 a1 (pre.length + 2 * (List.replicate n true).length + 1) 0
    (a1.env 2 + (List.replicate n true).length)
  have e3 := Ex.op (OpEx.zero (C := C) (11 : Fin 12) a2)
  let a3 := a2.set 11 0
  let pre1 := pre ++ frame (List.replicate n true)
  have hi1 : C.inp = pre1 ++ frame word ++ tail := hin
  have e4 := count_field C (0 : Fin 12) 1 11 (by decide) (by decide) (by decide)
    a3 (by simp [a3, a2, a1, counted, DS.set, hz]) word pre1 tail hi1
    (by simp [a3, a2, counted, pre1, frame_length, Nat.add_assoc]) (by simp [a3]; omega)
  let a4 := counted (1 : Fin 12) 11 a3 (pre1.length + 2 * word.length + 1) 0 (a3.env 11 + word.length)
  have e5 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 11 a4 (by decide))
  let a5 := a4.set 9 (a4.env 11)
  have h11 : a4.env 11 = word.length := by simp [a4, a3, counted]
  have e6 := Ex.op (OpEx.shl (C := C) (9 : Fin 12) a5 (by simp [a5, h11]; omega))
  let a6 := a5.set 9 (2 * a5.env 9)
  have e7 := Ex.op (OpEx.inc (C := C) (9 : Fin 12) a6 (by simp [a6, a5, h11]; omega))
  let a7 := a6.set 9 (a6.env 9 + 1)
  have e8 := rewind_count C (0 : Fin 12) 10 9 (by decide) (by decide) a7
    (by simp [a7, a6, a5, a4, a3, a2, a1, counted, DS.set, hz])
    (by simp [a7, a6, a5, a4, a3, a2, a1, counted, DS.set, ho]) pre1.length (2 * word.length + 1)
  have hrew : rewindState (9 : Fin 12) a7 (pre1.length + (2 * word.length + 1)) (2 * word.length + 1) = a7 := by
    apply state_ext
    · funext i
      by_cases h9 : i = 9
      · subst i; simp [rewindState, a7, a6, a5, h11, DS.set]
      · simp [rewindState, DS.set, h9]
    · simp [rewindState, a7, a6, a5, a4, counted]; omega
    all_goals rfl
  rw [hrew] at e8
  let a8 := rewindState (9 : Fin 12) a7 pre1.length 0
  have e9 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 11 a8 (by decide))
  let a9 := a8.set 9 (a8.env 11)
  have e10 := send_chunk C (0 : Fin 12) 10 1 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    true false word pre1 [] tail a9
    (by simp [a9, a8, rewindState, a7, a6, a5, a4, a3, a2, a1, counted, DS.set, hz])
    (by simp [a9, a8, rewindState, a7, a6, a5, a4, a3, a2, a1, counted, DS.set, ho])
    (by simp [a9, a8, rewindState, a7, a6, a5, a4, counted, DS.set])
    (by simp [a9, a8, rewindState, a7, a6, a5, DS.set, h11]) (by simpa using hi1)
    (by simp [a9, a8, rewindState])
    (by intro _; simpa [a9, a8, rewindState, a7, a6, a5, a4, a3, a2, a1, counted, hki, payload] using hroom)
  let a10 := chunkResult (1 : Fin 12) 9 true a9 (pre1.length + 2 * word.length) (word.flatMap (payload false))
  let pre2 := pre1 ++ Streaming.marks word
  have hi2 : C.inp = pre2 ++ false :: tail := by
    simpa only [pre2, NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks, List.append_assoc, List.singleton_append] using hi1
  have e11 := read_at_prefix C (1 : Fin 12) a10 pre2 false tail hi2
    (by simp [a10, chunkResult, pre2, Streaming.marks_length])
  let a11 := readState (1 : Fin 12) a10 false
  have hbits : word.flatMap (payload false) = word := by
    change word.flatMap (fun b => [b]) = word
    simp
  have hkin : a11.kin = C.K.inw request := by
    simp [a11, readState, a10, chunkResult, a9, a8, rewindState, a7, a6, a5, a4, a3, a2, a1, counted, hki, hbits, hword]
  have e12 := Ex.op (OpEx.kcall request a11 hkin hbudget)
  rw [hout] at e12
  let a12 := a11.called (frame output)
  have e13 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 2 a12 (by decide))
  let a13 := a12.set 9 (a12.env 2)
  have ez : a13.env 0 = 0 := by
    simp [a13, a12, DS.called, a11, readState, a10, chunkResult, a9, a8, rewindState,
      a7, a6, a5, a4, a3, a2, a1, counted, DS.set, hz]
  have eo : a13.env 10 = 1 := by
    simp [a13, a12, DS.called, a11, readState, a10, chunkResult, a9, a8, rewindState,
      a7, a6, a5, a4, a3, a2, a1, counted, DS.set, ho]
  have en : a13.env 9 = n := by
    simp [a13, a12, DS.called, a11, readState, a10, chunkResult, a9, a8, rewindState,
      a7, a6, a5, a4, a3, a2, a1, counted, DS.set]
  have e14 := PaddedOutput.runs C a13 ez eo n en output [] []
    (by simp [a13, a12, DS.called]) (by simp [a13, a12, DS.called])
  refine ⟨_, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6
    (Ex.seq e7 (Ex.seq e8 (Ex.seq e9 (Ex.seq e10 (Ex.seq e11 (Ex.seq e12 (Ex.seq e13 e14))))))))))))).mono ?_, ?_⟩
  · simp [payloadCost]
    omega
  · refine ⟨by simp [PaddedOutput.state, ez], by simp [PaddedOutput.state, eo], ?_, ?_, ?_⟩
    · simp [PaddedOutput.state, a13, a12, DS.called]
    · simp [PaddedOutput.state, a13, a12, DS.called, a11, readState, a10, chunkResult, pre1, frame_length]
      omega
    · simp [PaddedOutput.state, a13, a12, DS.called, a11, readState, a10, chunkResult, sent,
        a9, a8, rewindState, a7, a6, a5, a4, a3, a2, a1, counted]

end NearCubicGates.Adapters.Code.DecoderInvoke
