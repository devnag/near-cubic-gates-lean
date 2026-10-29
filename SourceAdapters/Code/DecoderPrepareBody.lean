import SourceAdapters.Code.DecoderPrepareCall

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the three paid encoder length queries and request
serializations, plus the finite identity packet. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderPrepareBody

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def large : Script := .seq (DecoderPrepareCall.script 6)
  (.seq (DecoderPrepareCall.script 7) (DecoderPrepareCall.script 8))

def small : Script := .seq (.op (.copy 9 2)) (.seq (sendChunk 0 10 1 9 false true) (.op (.emit false)))

theorem large_runs (C : Ctx) (a : State) (m0 m1 m2 : ℕ) (pre w0 w1 w2 o0 o1 o2 : List Bool)
    (r0 r1 r2 : C.K.Req) (hz : a.env 0 = 0) (ho : a.env 10 = 1)
    (h0 : a.env 6 = m0) (h1 : a.env 7 = m1) (h2 : a.env 8 = m2)
    (hin : C.inp = pre ++ frame (w0 ++ w1 ++ w2)) (hip : a.ip = pre.length) (hki : a.kin = [])
    (hi0 : C.K.inw r0 = List.replicate m0 false) (hi1 : C.K.inw r1 = List.replicate m1 false)
    (hi2 : C.K.inw r2 = List.replicate m2 false)
    (ho0 : C.K.outw r0 = frame o0) (ho1 : C.K.outw r1 = frame o1) (ho2 : C.K.outw r2 = frame o2)
    (hs0 : o0.length = w0.length) (hs1 : o1.length = w1.length) (hs2 : o2.length = w2.length)
    (hl0 : m0 ≤ C.Lk) (hl1 : m1 ≤ C.Lk) (hl2 : m2 ≤ C.Lk)
    (hb0 : C.K.bud r0 ≤ C.Bk) (hb1 : C.K.bud r1 ≤ C.Bk) (hb2 : C.K.bud r2 ≤ C.Bk)
    (hc0 : o0.length + 2 * m0 < 2 ^ C.Wd) (hc1 : o1.length + 2 * m1 < 2 ^ C.Wd)
    (hc2 : o2.length + 2 * m2 < 2 ^ C.Wd) :
    ∃ b, Ex C large a b (22 * (m0 + m1 + m2) + 21 * (w0.length + w1.length + w2.length) +
      3 * (C.Lk + C.Bk) + 116) ∧
      b.out = a.out ++ DecoderRequest.packet m0 w0 ++ DecoderRequest.packet m1 w1 ++ DecoderRequest.packet m2 w2 := by
  have e0 := DecoderPrepareCall.runs C 6 (by decide) (by decide) (by decide) r0 m0 o0 w0 pre (w1 ++ w2) [] a
    hz ho h0 hki hi0 ho0 hs0 hl0 hb0 hc0 (by simpa [List.append_assoc] using hin) hip
  let a1 := DecoderPrepareCall.result a o0 (pre.length + 2 * w0.length) m0 w0
  let pre1 := pre ++ Streaming.marks w0
  have hin1 : C.inp = pre1 ++ frame (w1 ++ w2) := by
    simpa [pre1, List.append_assoc, Streaming.frame_append] using hin
  have e1 := DecoderPrepareCall.runs C 7 (by decide) (by decide) (by decide) r1 m1 o1 w1 pre1 w2 [] a1
    (by simp [a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, DS.set, hz])
    (by simp [a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, DS.set, ho])
    (by simp [a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, DS.set, h1])
    (by simp [a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result]) hi1 ho1 hs1 hl1 hb1 hc1
    (by simpa using hin1)
    (by simp [a1, DecoderPrepareCall.result, DecoderRequest.result, pre1, Streaming.marks_length])
  let a2 := DecoderPrepareCall.result a1 o1 (pre1.length + 2 * w1.length) m1 w1
  let pre2 := pre1 ++ Streaming.marks w1
  have hin2 : C.inp = pre2 ++ frame w2 := by
    simpa [pre2, List.append_assoc, Streaming.frame_append] using hin1
  have e2 := DecoderPrepareCall.runs C 8 (by decide) (by decide) (by decide) r2 m2 o2 w2 pre2 [] [] a2
    (by simp [a2, a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, DS.set, hz])
    (by simp [a2, a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, DS.set, ho])
    (by simp [a2, a1, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, DS.set, h2])
    (by simp [a2, DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result]) hi2 ho2 hs2 hl2 hb2 hc2
    (by simpa using hin2)
    (by simp [a2, DecoderPrepareCall.result, DecoderRequest.result, pre2, Streaming.marks_length])
  refine ⟨_, (Ex.seq e0 (Ex.seq e1 e2)).mono (by omega), ?_⟩
  simp [DecoderPrepareCall.result, DecoderRequest.result, LengthCall.result, a2, a1]

theorem small_runs (C : Ctx) (a : State) (pre bits : List Bool)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hf : a.env 1 = 0) (hlen : a.env 2 = bits.length)
    (hin : C.inp = pre ++ frame bits) (hip : a.ip = pre.length) :
    ∃ b, Ex C small a b (14 * bits.length + 6) ∧ b.out = a.out ++ frame bits := by
  have e1 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 2 a (by decide))
  let a1 := a.set 9 (a.env 2)
  have e2 := send_chunk C (0 : Fin 12) 10 1 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    false true bits pre [] [] a1
    (by simp [a1, DS.set, hz]) (by simp [a1, DS.set, ho]) (by simp [a1, DS.set, hf])
    (by simp [a1, hlen]) (by simpa using hin) (by simp [a1, hip]) (by simp)
  let a2 := chunkResult (1 : Fin 12) 9 false a1 (pre.length + 2 * bits.length) (bits.flatMap (payload true))
  have e3 := Ex.op (OpEx.emit (C := C) false a2)
  have hm : bits.flatMap (payload true) = Streaming.marks bits := by
    change bits.flatMap (fun b => [true, b]) = _
    rfl
  refine ⟨_, (Ex.seq e1 (Ex.seq e2 e3)).mono (by simp [payloadCost]; omega), ?_⟩
  change (a.out ++ bits.flatMap (payload true)) ++ [false] = a.out ++ frame bits
  rw [hm, List.append_assoc, ← NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks]

end NearCubicGates.Adapters.Code.DecoderPrepareBody
