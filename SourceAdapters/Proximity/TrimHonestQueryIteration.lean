import SourceAdapters.Proximity.TrimHonestQueryStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": a paid answer iteration with its own protected index. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def answerLoopTemps : List (Fin VV) := answerIndex :: answerTemps
def answerIteration : St VV MM := .seq answerStep (.op (.inc answerIndex))

theorem answer_iteration {n N : ℕ} (input : BitInput n) (proof : BitInput N)
    (p : Bool × ℕ) (a : DS VV MM) (hc : Cst a) (ready : OracleReady C input proof a)
    (queryTail previous oldTail : List ℕ)
    (hread : (a.ram queryStore).drop (a.rc queryStore) = pairFields p ++ queryTail)
    (hanswer : a.ram answerStore = previous ++ oldTail) (hcursor : a.rc answerStore = previous.length)
    (hwidth : a.env answerIndex + 1 < 2 ^ C.Wd) :
    Hs C answerIteration a (6 * (n + N) + 19) (fun b =>
      b.ram answerStore = previous ++ (answerValue input proof p).toNat :: oldTail.drop 1 ∧
      b.rc answerStore = previous.length + 1 ∧ b.rc queryStore = a.rc queryStore + 2 ∧
      b.env answerIndex = a.env answerIndex + 1 ∧
      OracleReady C input proof b ∧ QueryFrame answerLoopTemps a b) := by
  obtain ⟨b, cost, eb, hb, bm, ba, bq, rb, fb⟩ :=
    answer_step input proof p a hc ready queryTail previous oldTail hread hanswer hcursor
  have bi : b.env answerIndex = a.env answerIndex := fb.env answerIndex (by decide)
  have ei := Ex.op (OpEx.inc (C := C) answerIndex b (by rw [bi]; exact hwidth))
  let d := b.set answerIndex (b.env answerIndex + 1)
  refine ⟨d, cost + 1 + 1, Ex.seq eb ei, by omega, ?_⟩
  exact ⟨bm, ba, bq, by simp [d, bi], rb.set answerIndex _ (by decide) (by decide),
    (fb.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans
      (QueryFrame.set answerLoopTemps b answerIndex _ (by simp [answerLoopTemps]))⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
