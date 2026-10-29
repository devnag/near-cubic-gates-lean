import SourceAdapters.Proximity.TrimHonestQueryIteration

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": all fixed-query answers are computed from the actual
input and source proof, overwriting the preceding row's answer vector. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def answerWords {n N : ℕ} (input : BitInput n) (proof : BitInput N) (ps : List (Bool × ℕ)) : List ℕ :=
  ps.map (fun p => (answerValue input proof p).toNat)
def answerLoop : St VV MM := .loop (.lt answerIndex QueryStep.boundReg) answerIteration

theorem answer_loop {n N : ℕ} (input : BitInput n) (proof : BitInput N) :
    ∀ (ps : List (Bool × ℕ)) (a : DS VV MM) (past previous old : List ℕ),
      Cst a → OracleReady C input proof a → a.ram queryStore = past ++ ps.flatMap pairFields →
      a.rc queryStore = past.length → a.env answerIndex = previous.length →
      a.env QueryStep.boundReg = previous.length + ps.length →
      a.ram answerStore = previous ++ old → a.rc answerStore = previous.length →
      old.length ≤ ps.length → previous.length + ps.length < 2 ^ C.Wd →
      Hs C answerLoop a ((6 * (n + N) + 21) * ps.length + 2) (fun b =>
        b.ram answerStore = previous ++ answerWords input proof ps ∧
        b.rc answerStore = previous.length + ps.length ∧
        b.rc queryStore = a.rc queryStore + 2 * ps.length ∧
        OracleReady C input proof b ∧ QueryFrame answerLoopTemps a b) := by
  intro ps
  induction ps with
  | nil =>
    intro a past previous old _ ready _ _ hi hlen hm hr hold _
    have ho : old = [] := List.length_eq_zero_iff.mp (by simpa using hold)
    refine ⟨a, 2, Ex.loopF (show answerIndex ≠ QueryStep.boundReg by decide)
      (by simp [Cnd.eval, hi, hlen]), by simp, ?_⟩
    exact ⟨by simpa [answerWords, ho] using hm, by simpa using hr, by simp,
      ready, QueryFrame.refl _ _⟩
  | cons p ps ih =>
    intro a past previous old hc ready hq hqc hi hlen hm hr hold hwidth
    have ht : (Cnd.lt answerIndex QueryStep.boundReg).eval a = true := by simp [Cnd.eval, hi, hlen]
    have hread : (a.ram queryStore).drop (a.rc queryStore) = pairFields p ++ ps.flatMap pairFields := by
      rw [hq, hqc, List.drop_left, List.flatMap_cons]
    obtain ⟨b, nb, eb, hb, bm, ba, bq, bi, rb, fb⟩ :=
      answer_iteration input proof p a hc ready (ps.flatMap pairFields) previous old hread hm hr
        (by rw [hi]; simp only [List.length_cons] at hwidth; omega)
    let previous' := previous ++ [(answerValue input proof p).toNat]
    have hpLen : previous'.length = previous.length + 1 := by simp [previous']
    have bqm : b.ram queryStore = (past ++ pairFields p) ++ ps.flatMap pairFields := by
      rw [fb.ram queryStore (by decide), hq, List.flatMap_cons, List.append_assoc]
    have bqr : b.rc queryStore = (past ++ pairFields p).length := by rw [bq, hqc]; simp [pairFields]
    have bindex : b.env answerIndex = previous'.length := by rw [bi, hi]; simp [previous']
    have blen : b.env QueryStep.boundReg = previous'.length + ps.length := by
      rw [fb.env QueryStep.boundReg (by decide), hlen, hpLen]
      simp only [List.length_cons]
      omega
    have bam : b.ram answerStore = previous' ++ old.drop 1 := by
      simpa only [previous', List.append_assoc, List.singleton_append] using bm
    have bar : b.rc answerStore = previous'.length := by simpa [previous'] using ba
    have bold : (old.drop 1).length ≤ ps.length := by
      simp only [List.length_drop]
      simp only [List.length_cons] at hold
      omega
    have bw : previous'.length + ps.length < 2 ^ C.Wd := by
      simp only [previous', List.length_append, List.length_singleton]
      simp only [List.length_cons] at hwidth
      omega
    obtain ⟨d, nd, ed, hd, dm, da, dq, rd, fd⟩ :=
      ih b (past ++ pairFields p) previous' (old.drop 1) (fb.constants hc (by decide)) rb
        bqm bqr bindex blen bam bar bold bw
    refine ⟨d, nb + nd + 2, Ex.loopT (show answerIndex ≠ QueryStep.boundReg by decide) ht eb ed,
      ?_, ?_⟩
    · calc
        nb + nd + 2 ≤ (6 * (n + N) + 19) + ((6 * (n + N) + 21) * ps.length + 2) + 2 := by omega
        _ = _ := by simp only [List.length_cons]; ring
    · refine ⟨?_, ?_, ?_, rd, fb.trans fd⟩
      · simpa [previous', answerWords, List.append_assoc] using dm
      · rw [da, hpLen]
        simp only [List.length_cons]
        omega
      · rw [dq, bq]
        simp only [List.length_cons]
        omega

end NearCubicGates.Adapters.Proximity.TrimHonest
