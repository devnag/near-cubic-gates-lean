import SourceAdapters.Code.OutputParsing
import SourceAdapters.Code.EncoderFront

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": an actual ordinary source call on one consecutive
message block, followed by exact framing removal and output concatenation. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.EncoderCall

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def script (size : Fin 12) : Script := .seq (.op (.copy 9 size))
  (.seq (sendChunk 0 10 1 9 true false) (.seq (.op .kcall) (OutputParsing.copyFrame 0 1)))

def result (a : State) (pos : ℕ) (output : List Bool) : State :=
  { (a.set 9 0).set 1 0 with
    ip := pos
    out := a.out ++ output
    kin := []
    kout := frame output
    kc := 2 * output.length + 1 }

theorem runs (C : Ctx) (size : Fin 12) (hs : size ≠ 9) (request : C.K.Req)
    (bits output pre tail suffix : List Bool) (a : State)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hf : a.env 1 = 0) (hlen : a.env size = bits.length)
    (hin : C.inp = pre ++ frame (bits ++ tail) ++ suffix) (hip : a.ip = pre.length) (hki : a.kin = [])
    (hword : C.K.inw request = bits) (hout : C.K.outw request = frame output)
    (hroom : bits.length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk) :
    Ex C (script size) a (result a (pre.length + 2 * bits.length) output)
      (12 * bits.length + 8 * output.length + C.Lk + C.Bk + 11) := by
  have e1 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) size a (Ne.symm hs))
  let a1 := a.set 9 (a.env size)
  have e2 := send_chunk C (0 : Fin 12) 10 1 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    true false bits pre tail suffix a1
    (by simp [a1, DS.set, hz]) (by simp [a1, DS.set, ho]) (by simp [a1, DS.set, hf])
    (by simp [a1, hlen]) hin (by simp [a1, hip])
    (by intro _; simpa [a1, hki, payload] using hroom)
  let a2 := chunkResult (1 : Fin 12) 9 true a1 (pre.length + 2 * bits.length) (bits.flatMap (payload false))
  have hbits : bits.flatMap (payload false) = bits := by
    change bits.flatMap (fun b => [b]) = bits
    simp
  have hkin : a2.kin = C.K.inw request := by simp [a2, a1, chunkResult, hki, hbits, hword]
  have e3 := Ex.op (OpEx.kcall request a2 hkin hbudget)
  rw [hout] at e3
  let a3 := a2.called (frame output)
  have e4 := OutputParsing.copy_frame C (0 : Fin 12) 1 (by decide) a3
    (by simp [a3, a2, a1, DS.called, chunkResult, DS.set, hz]) output [] []
    (by simp [a3, DS.called]) (by simp [a3, DS.called])
  have he := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))
  have hfinal : OutputParsing.positioned (1 : Fin 12) a3 (0 + 2 * output.length + 1) 0 (a3.out ++ output) =
      result a (pre.length + 2 * bits.length) output := by
    apply state_ext
    · funext i
      by_cases h1 : i = 1
      · subst i; simp [OutputParsing.positioned, result, DS.set]
      · by_cases h9 : i = 9
        · subst i; simp [OutputParsing.positioned, a3, a2, a1, DS.called, chunkResult, result, DS.set]
        · simp [OutputParsing.positioned, a3, a2, a1, DS.called, chunkResult, result, DS.set, h1, h9]
    all_goals simp [OutputParsing.positioned, a3, a2, a1, DS.called, chunkResult, sent, result]
  simp only [List.length_nil] at he
  rw [hfinal] at he
  exact he.mono (by simp [payloadCost]; omega)

end NearCubicGates.Adapters.Code.EncoderCall
