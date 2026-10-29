import SourceAdapters.Code.EncoderBody

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the finite decoder branch copies its arbitrary framed
payload after paid length counting and rewind. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CountedCopy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells CountedParsing

abbrev State := DS 12 0
abbrev Script := St 12 0

def script : Script := .seq (.op (.zero 2)) (.seq (countField 0 1 2) (.seq (.op (.copy 9 2))
  (.seq (.op (.shl 9)) (.seq (.op (.inc 9)) (.seq (rewindCount 0 10 9) EncoderBody.small)))))

theorem runs (C : Ctx) (a : State) (pre bits : List Bool) (hz : a.env 0 = 0) (ho : a.env 10 = 1)
    (hin : C.inp = pre ++ frame bits) (hip : a.ip = pre.length) (hcap : 2 * bits.length + 2 < 2 ^ C.Wd) :
    ∃ b, Ex C script a b (100 * (bits.length + 1)) ∧ b.out = a.out ++ bits := by
  have e1 := Ex.op (OpEx.zero (C := C) (2 : Fin 12) a)
  let a1 := a.set 2 0
  have e2 := count_field C (0 : Fin 12) 1 2 (by decide) (by decide) (by decide)
    a1 (by simp [a1, DS.set, hz]) bits pre [] (by simpa using hin) (by simp [a1, hip])
    (by simp [a1]; omega)
  let a2 := counted (1 : Fin 12) 2 a1 (pre.length + 2 * bits.length + 1) 0 (a1.env 2 + bits.length)
  have hn : a2.env 2 = bits.length := by simp [a2, a1, counted]
  have e3 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 2 a2 (by decide))
  let a3 := a2.set 9 (a2.env 2)
  have e4 := Ex.op (OpEx.shl (C := C) (9 : Fin 12) a3 (by simp [a3, hn]; omega))
  let a4 := a3.set 9 (2 * a3.env 9)
  have e5 := Ex.op (OpEx.inc (C := C) (9 : Fin 12) a4 (by simp [a4, a3, hn]; omega))
  let a5 := a4.set 9 (a4.env 9 + 1)
  have e6 := rewind_count C (0 : Fin 12) 10 9 (by decide) (by decide) a5
    (by simp [a5, a4, a3, a2, a1, counted, DS.set, hz])
    (by simp [a5, a4, a3, a2, a1, counted, DS.set, ho]) pre.length (2 * bits.length + 1)
  have hrew : rewindState (9 : Fin 12) a5 (pre.length + (2 * bits.length + 1)) (2 * bits.length + 1) = a5 := by
    apply state_ext
    · funext i
      by_cases h9 : i = 9
      · subst i; simp [rewindState, a5, a4, a3, hn, DS.set]
      · simp [rewindState, DS.set, h9]
    · simp [rewindState, a5, a4, a3, a2, counted]; omega
    all_goals rfl
  rw [hrew] at e6
  let a6 := rewindState (9 : Fin 12) a5 pre.length 0
  obtain ⟨b, e7, hout⟩ := EncoderBody.small_runs C a6 pre bits
    (by simp [a6, rewindState, a5, a4, a3, a2, a1, counted, DS.set, hz])
    (by simp [a6, rewindState, a5, a4, a3, a2, a1, counted, DS.set, ho])
    (by simp [a6, rewindState, a5, a4, a3, a2, counted, DS.set])
    (by simp [a6, rewindState, a5, a4, a3, DS.set, hn]) hin (by simp [a6, rewindState])
  refine ⟨b, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6 e7)))))).mono (by omega), ?_⟩
  simpa [a6, rewindState, a5, a4, a3, a2, a1, counted] using hout

end NearCubicGates.Adapters.Code.CountedCopy
