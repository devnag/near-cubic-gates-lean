import SourceAdapters.Proximity.TrimHonestQuerySetup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the complete paid source-query answer program, including
rewinds and replacement of a preceding row's answer vector. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def answerProgram : St VV MM := .seq answerSetup answerLoop

theorem answer_program {n N : ℕ} (input : BitInput n) (proof : BitInput N)
    (ps : List (Bool × ℕ)) (a : DS VV MM) (hc : Cst a) (ready : OracleReady C input proof a)
    (hq : a.ram queryStore = ps.flatMap pairFields)
    (hlen : a.env QueryStep.boundReg = ps.length)
    (hold : (a.ram answerStore).length ≤ ps.length) (hwidth : ps.length < 2 ^ C.Wd) :
    Hs C answerProgram a
      (a.rc queryStore + a.rc answerStore + (6 * (n + N) + 21) * ps.length + 8) (fun b =>
        b.ram answerStore = answerWords input proof ps ∧ b.rc answerStore = ps.length ∧
        b.rc queryStore = 2 * ps.length ∧
        OracleReady C input proof b ∧ QueryFrame answerLoopTemps a b) := by
  have e1 := answer_setup (C := C) a
  have f1 := answer_initial_frame a
  have hram : (answerInitial a).ram = a.ram := rfl
  obtain ⟨b, cost, e2, hcost, bm, ba, bq, rb, fb⟩ :=
    answer_loop input proof ps (answerInitial a) [] [] (a.ram answerStore)
      (f1.constants hc (by decide)) ready.answer_initial
      (by rw [hram]; exact hq)
      (by simp [answerInitial, DS.rew, queryStore, answerStore])
      (by simp [answerInitial])
      (by simpa only [List.length_nil, Nat.zero_add] using
        (f1.env QueryStep.boundReg (by decide)).trans hlen)
      (by rw [hram]; rfl) (by simp [answerInitial, DS.rew]) hold (by simpa using hwidth)
  refine ⟨b, a.rc queryStore + a.rc answerStore + 5 + cost + 1, Ex.seq e1 e2, by omega, ?_⟩
  exact ⟨by simpa using bm, by simpa using ba,
    by simpa [answerInitial, DS.rew, queryStore, answerStore] using bq, rb, f1.trans fb⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
