import SourceAdapters.Code.OutputCounting
import SourceAdapters.Code.RepeatedSending

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": computing one source codeword length by an actual encoder
call on a zero message and counting its exact framed output. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.LengthCall

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def script (size : Fin 12) : Script := .seq (.op (.copy 9 size))
  (.seq (RepeatedSending.script 0 10 9 true false)
    (.seq (.op .kcall) (.seq (.op (.zero 11)) (OutputCounting.countField 0 1 11))))

def result (a : State) (output : List Bool) : State :=
  { ((a.set 9 0).set 1 0).set 11 output.length with
    kin := []
    kout := frame output
    kc := 2 * output.length + 1 }

theorem runs (C : Ctx) (size : Fin 12) (hs : size ≠ 9) (request : C.K.Req)
    (n : ℕ) (output : List Bool) (a : State)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hlen : a.env size = n) (hki : a.kin = [])
    (hword : C.K.inw request = List.replicate n false) (hout : C.K.outw request = frame output)
    (hroom : n ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk) (hcap : output.length < 2 ^ C.Wd) :
    Ex C (script size) a (result a output)
      (5 * n + 7 * output.length + C.Lk + C.Bk + 13) := by
  have e1 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) size a (Ne.symm hs))
  let a1 := a.set 9 (a.env size)
  have e2 := RepeatedSending.runs C (0 : Fin 12) 10 9 (by decide) (by decide) true false n a1
    (by simp [a1, DS.set, hz]) (by simp [a1, DS.set, ho]) (by simp [a1, hlen])
    (by intro _; simpa [a1, hki] using hroom)
  let a2 := sent true (a1.set 9 0) (List.replicate n false)
  have hkin : a2.kin = C.K.inw request := by simp [a2, a1, hki, hword]
  have e3 := Ex.op (OpEx.kcall request a2 hkin hbudget)
  rw [hout] at e3
  let a3 := a2.called (frame output)
  have e4 := Ex.op (OpEx.zero (C := C) (11 : Fin 12) a3)
  let a4 := a3.set 11 0
  have e5 := OutputCounting.count_field C (0 : Fin 12) 1 11 (by decide) (by decide) (by decide)
    a4 (by simp [a4, a3, a2, a1, DS.called, sent, DS.set, hz]) output [] []
    (by simp [a4, a3, DS.called]) (by simp [a4, a3, DS.called]) (by simpa [a4] using hcap)
  have he := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5)))
  have hfinal : OutputCounting.counted (1 : Fin 12) 11 a4 (0 + 2 * output.length + 1) 0 (a4.env 11 + output.length) =
      result a output := by
    apply state_ext
    · funext i
      by_cases h1 : i = 1
      · subst i; simp [OutputCounting.counted, result, DS.set]
      · by_cases h9 : i = 9
        · subst i; simp [OutputCounting.counted, a4, a3, a2, a1, DS.called, sent, result, DS.set]
        · by_cases h11 : i = 11
          · subst i; simp [OutputCounting.counted, a4, result, DS.set]
          · simp [OutputCounting.counted, a4, a3, a2, a1, DS.called, sent, result, DS.set, h1, h9, h11]
    all_goals simp [OutputCounting.counted, a4, a3, a2, a1, DS.called, sent, result]
  simp only [List.length_nil] at he
  rw [hfinal] at he
  exact he.mono (by omega)

end NearCubicGates.Adapters.Code.LengthCall
