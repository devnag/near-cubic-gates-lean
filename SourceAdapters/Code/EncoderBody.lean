import SourceAdapters.Code.EncoderCall

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": consecutive source calls and the finite
identity branch, with every input, output and call cost charged. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.EncoderBody

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def large : Script := .seq (EncoderCall.script 6)
  (.seq (EncoderCall.script 7) (EncoderCall.script 8))

def small : Script := .seq (.op (.copy 9 2)) (sendChunk 0 10 1 9 false false)

theorem large_runs (C : Ctx) (a : State) (pre w0 w1 w2 o0 o1 o2 : List Bool)
    (r0 r1 r2 : C.K.Req)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hf : a.env 1 = 0)
    (h0 : a.env 6 = w0.length) (h1 : a.env 7 = w1.length) (h2 : a.env 8 = w2.length)
    (hin : C.inp = pre ++ frame (w0 ++ w1 ++ w2)) (hip : a.ip = pre.length) (hki : a.kin = [])
    (hi0 : C.K.inw r0 = w0) (hi1 : C.K.inw r1 = w1) (hi2 : C.K.inw r2 = w2)
    (ho0 : C.K.outw r0 = frame o0) (ho1 : C.K.outw r1 = frame o1) (ho2 : C.K.outw r2 = frame o2)
    (hl0 : w0.length ≤ C.Lk) (hl1 : w1.length ≤ C.Lk) (hl2 : w2.length ≤ C.Lk)
    (hb0 : C.K.bud r0 ≤ C.Bk) (hb1 : C.K.bud r1 ≤ C.Bk) (hb2 : C.K.bud r2 ≤ C.Bk) :
    ∃ b, Ex C large a b (12 * (w0.length + w1.length + w2.length) +
      8 * (o0.length + o1.length + o2.length) + 3 * (C.Lk + C.Bk) + 35) ∧
      b.out = a.out ++ o0 ++ o1 ++ o2 := by
  have e0 := EncoderCall.runs C 6 (by decide) r0 w0 o0 pre (w1 ++ w2) [] a
    hz ho hf h0 (by simpa [List.append_assoc] using hin) hip hki hi0 ho0 hl0 hb0
  let a1 := EncoderCall.result a (pre.length + 2 * w0.length) o0
  let pre1 := pre ++ Streaming.marks w0
  have hin1 : C.inp = pre1 ++ frame (w1 ++ w2) := by
    simpa [pre1, List.append_assoc, Streaming.frame_append] using hin
  have e1 := EncoderCall.runs C 7 (by decide) r1 w1 o1 pre1 w2 [] a1
    (by simp [a1, EncoderCall.result, DS.set, hz])
    (by simp [a1, EncoderCall.result, DS.set, ho])
    (by simp [a1, EncoderCall.result, DS.set])
    (by simp [a1, EncoderCall.result, DS.set, h1])
    (by simpa using hin1) (by simp [a1, EncoderCall.result, pre1, Streaming.marks_length])
    (by simp [a1, EncoderCall.result]) hi1 ho1 hl1 hb1
  let a2 := EncoderCall.result a1 (pre1.length + 2 * w1.length) o1
  let pre2 := pre1 ++ Streaming.marks w1
  have hin2 : C.inp = pre2 ++ frame w2 := by
    simpa [pre2, List.append_assoc, Streaming.frame_append] using hin1
  have e2 := EncoderCall.runs C 8 (by decide) r2 w2 o2 pre2 [] [] a2
    (by simp [a2, a1, EncoderCall.result, DS.set, hz])
    (by simp [a2, a1, EncoderCall.result, DS.set, ho])
    (by simp [a2, EncoderCall.result, DS.set])
    (by simp [a2, a1, EncoderCall.result, DS.set, h2])
    (by simpa using hin2) (by simp [a2, EncoderCall.result, pre2, Streaming.marks_length])
    (by simp [a2, EncoderCall.result]) hi2 ho2 hl2 hb2
  refine ⟨_, (Ex.seq e0 (Ex.seq e1 e2)).mono (by omega), ?_⟩
  simp [EncoderCall.result, a2, a1]

theorem small_runs (C : Ctx) (a : State) (pre bits : List Bool)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hf : a.env 1 = 0) (hlen : a.env 2 = bits.length)
    (hin : C.inp = pre ++ frame bits) (hip : a.ip = pre.length) :
    ∃ b, Ex C small a b (12 * bits.length + 4) ∧ b.out = a.out ++ bits := by
  have e1 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 2 a (by decide))
  let a1 := a.set 9 (a.env 2)
  have e2 := send_chunk C (0 : Fin 12) 10 1 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    false false bits pre [] [] a1
    (by simp [a1, DS.set, hz]) (by simp [a1, DS.set, ho]) (by simp [a1, DS.set, hf])
    (by simp [a1, hlen]) (by simpa using hin) (by simp [a1, hip]) (by simp)
  have hbits : bits.flatMap (payload false) = bits := by
    change bits.flatMap (fun b => [b]) = bits
    simp
  refine ⟨_, (Ex.seq e1 e2).mono (by simp [payloadCost]; omega), ?_⟩
  simp [chunkResult, sent, a1, hbits]

end NearCubicGates.Adapters.Code.EncoderBody
