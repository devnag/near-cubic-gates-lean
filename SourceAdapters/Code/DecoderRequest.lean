import SourceAdapters.Code.LengthCall

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": explicit source-decoder tuple construction from one
received interval and its measured source length. All tuple and outer framing
bits are emitted by paid ordinary instructions. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderRequest

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def sourceWord (n : ℕ) (bits : List Bool) : List Bool := List.replicate n true ++ false :: bits

def packet (n : ℕ) (bits : List Bool) : List Bool := frame (List.replicate n true) ++ frame (sourceWord n bits)

def script (size : Fin 12) : Script := .seq (.op (.copy 9 size))
  (.seq (sendUnaryFrame 0 10 9 false) (.seq (.op (.copy 9 size)) (.seq (.op (.shl 9))
    (.seq (RepeatedSending.script 0 10 9 false true) (.seq (.op (.emit true))
      (.seq (.op (.emit false)) (.seq (.op (.copy 9 11))
        (.seq (sendChunk 0 10 1 9 false true) (.op (.emit false))))))))))

def result (a : State) (pos n : ℕ) (bits : List Bool) : State :=
  { (a.set 9 0).set 1 0 with
    ip := pos
    out := a.out ++ packet n bits }

theorem marks_unary (n : ℕ) : Streaming.marks (List.replicate n true) = List.replicate (2 * n) true := by
  induction n with
  | zero => simp [Streaming.marks]
  | succ n ih =>
    unfold Streaming.marks at ih ⊢
    simp [List.replicate_succ, ih, Nat.mul_add]

theorem runs (C : Ctx) (size : Fin 12) (hs : size ≠ 9) (n : ℕ) (bits pre tail suffix : List Bool)
    (a : State) (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hf : a.env 1 = 0)
    (hn : a.env size = n) (hl : a.env 11 = bits.length)
    (hin : C.inp = pre ++ frame (bits ++ tail) ++ suffix) (hip : a.ip = pre.length)
    (hcap : 2 * n < 2 ^ C.Wd) :
    Ex C (script size) a (result a (pre.length + 2 * bits.length) n bits)
      (17 * n + 14 * bits.length + 24) := by
  have e1 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) size a (Ne.symm hs))
  let a1 := a.set 9 (a.env size)
  have e2 := send_unary_frame C (0 : Fin 12) 10 9 (by decide) (by decide) false n a1
    (by simp [a1, DS.set, hz]) (by simp [a1, DS.set, ho]) (by simp [a1, hn]) (by simp)
  let a2 := sent false (a1.set 9 0) (frame (List.replicate n true))
  have e3 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) size a2 (Ne.symm hs))
  let a3 := a2.set 9 (a2.env size)
  have h9 : a3.env 9 = n := by simp [a3, a2, a1, DS.set, hs, hn]
  have e4 := Ex.op (OpEx.shl (C := C) (9 : Fin 12) a3 (by simpa [h9] using hcap))
  let a4 := a3.set 9 (2 * a3.env 9)
  have e5 := RepeatedSending.runs C (0 : Fin 12) 10 9 (by decide) (by decide) false true (2 * n) a4
    (by simp [a4, a3, a2, a1, DS.set, hz]) (by simp [a4, a3, a2, a1, DS.set, ho])
    (by simp [a4, h9]) (by simp)
  let a5 := sent false (a4.set 9 0) (List.replicate (2 * n) true)
  have e6 := Ex.op (OpEx.emit (C := C) true a5)
  let a6 : State := {a5 with out := a5.out ++ [true]}
  have e7 := Ex.op (OpEx.emit (C := C) false a6)
  let a7 : State := {a6 with out := a6.out ++ [false]}
  have e8 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 11 a7 (by decide))
  let a8 := a7.set 9 (a7.env 11)
  have e9 := send_chunk C (0 : Fin 12) 10 1 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    false true bits pre tail suffix a8
    (by simp [a8, a7, a6, a5, a4, a3, a2, a1, DS.set, hz])
    (by simp [a8, a7, a6, a5, a4, a3, a2, a1, DS.set, ho])
    (by simp [a8, a7, a6, a5, a4, a3, a2, a1, DS.set, hf])
    (by simp [a8, a7, a6, a5, a4, a3, a2, a1, DS.set, hl]) hin
    (by simp [a8, a7, a6, a5, a4, a3, a2, a1, sent, hip]) (by simp)
  let a9 := chunkResult (1 : Fin 12) 9 false a8 (pre.length + 2 * bits.length) (bits.flatMap (payload true))
  have e10 := Ex.op (OpEx.emit (C := C) false a9)
  have he := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6
    (Ex.seq e7 (Ex.seq e8 (Ex.seq e9 e10))))))))
  have hm : bits.flatMap (payload true) = Streaming.marks bits := by
    change bits.flatMap (fun b => [true, b]) = _
    rfl
  have hp : packet n bits = frame (List.replicate n true) ++ List.replicate (2 * n) true ++ [true, false] ++
      Streaming.marks bits ++ [false] := by
    simp [packet, sourceWord, Streaming.frame_append, marks_unary, frame,
      ← NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks, List.append_assoc]
  have hfinal : {a9 with out := a9.out ++ [false]} = result a (pre.length + 2 * bits.length) n bits := by
    apply state_ext
    · funext i
      by_cases h1 : i = 1
      · subst i; simp [a9, chunkResult, result, DS.set]
      · by_cases h9 : i = 9
        · subst i; simp [a9, chunkResult, result, DS.set]
        · simp [a9, chunkResult, a8, a7, a6, a5, a4, a3, a2, a1, result, DS.set, h1, h9]
    · simp [a9, chunkResult, sent, result]
    · change (a.out ++ frame (List.replicate n true) ++ List.replicate (2 * n) true ++ [true] ++ [false] ++
        bits.flatMap (payload true)) ++ [false] = a.out ++ packet n bits
      rw [hm, hp]
      simp only [List.append_assoc, List.singleton_append]
    all_goals simp [a9, chunkResult, a8, a7, a6, a5, a4, a3, a2, a1, sent, result]
  rw [hfinal] at he
  exact he.mono (by simp [payloadCost]; omega)

end NearCubicGates.Adapters.Code.DecoderRequest
