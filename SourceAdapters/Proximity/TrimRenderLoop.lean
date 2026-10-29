import SourceAdapters.Proximity.TrimRenderStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": every original query is emitted in its original order.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def renderLoop : St VV MM := .loop (.lt renderIndex fieldsReg) renderStep

theorem render_loop {n : ℕ} (V : ThreeQueryVerifier n) :
    ∀ (qs : List (SignedQuery n)) (a : DS VV MM) (past : List ℕ),
      Cst a → a.ram sN = past ++ qs.flatMap trimQueryFields → a.rc sN = past.length →
      a.env renderIndex = past.length → a.env fieldsReg = past.length + 3 * qs.length →
      a.ram distinctStore = trimSortedAddresses ⟨n, V⟩ →
      a.env distinctCountReg = (trimSortedAddresses ⟨n, V⟩).length →
      a.env arityReg = n → a.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length →
      inputSize V + 4 ≤ C.Wd → past.length + 3 * qs.length < 2 ^ C.Wd →
      Hs C renderLoop a ((100 * (inputSize V + 1) + 6) * qs.length + 2) (fun b =>
        b.out = a.out ++ qs.flatMap (literalWord V) ∧ RenderFrame renderStepTemps a b) := by
  intro qs
  induction qs with
  | nil =>
    intro a past _ _ _ hi hlen _ _ _ _ _ _
    refine ⟨a, 2, Ex.loopF (show renderIndex ≠ fieldsReg by decide)
      (by simp [Cnd.eval, hi, hlen]), by simp, ?_⟩
    exact ⟨by simp, RenderFrame.refl _ _⟩
  | cons q qs ih =>
    intro a past hc hsource hcursor hi hlen hm hn harity hrc hW hwidth
    have ht : (Cnd.lt renderIndex fieldsReg).eval a = true := by simp [Cnd.eval, hi, hlen]
    have hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ qs.flatMap trimQueryFields := by
      rw [hsource, hcursor, List.drop_left, List.flatMap_cons]
    obtain ⟨b, nb, eb, hb, bout, bq, bd, bi, bf⟩ :=
      render_step (C := C) V q a hc (qs.flatMap trimQueryFields) hread hm hn harity hrc hW
        (by rw [hi]; simp only [List.length_cons] at hwidth; omega)
    have hbsource : b.ram sN = (past ++ trimQueryFields q) ++ qs.flatMap trimQueryFields := by
      rw [bf.ram, hsource, List.flatMap_cons, List.append_assoc]
    have hbcur : b.rc sN = (past ++ trimQueryFields q).length := by
      rw [bq, hcursor, List.length_append, queryFields_length]
    have hbi : b.env renderIndex = (past ++ trimQueryFields q).length := by
      rw [bi, hi, List.length_append, queryFields_length]
    have hblen : b.env fieldsReg = (past ++ trimQueryFields q).length + 3 * qs.length := by
      rw [bf.env fieldsReg (by decide), hlen]
      simp only [List.length_cons, List.length_append, queryFields_length]
      omega
    have hbw : (past ++ trimQueryFields q).length + 3 * qs.length < 2 ^ C.Wd := by
      simp only [List.length_append, queryFields_length]
      simp only [List.length_cons] at hwidth
      omega
    obtain ⟨d, nd, ed, hd, dout, df⟩ :=
      ih b (past ++ trimQueryFields q) (bf.constants hc (by decide)) hbsource hbcur hbi hblen
        (by rw [bf.ram]; exact hm) ((bf.env distinctCountReg (by decide)).trans hn)
        ((bf.env arityReg (by decide)).trans harity) bd hW hbw
    refine ⟨d, nb + nd + 2, Ex.loopT (show renderIndex ≠ fieldsReg by decide) ht eb ed, ?_, ?_⟩
    · calc
        nb + nd + 2 ≤ (100 * (inputSize V + 1) + 4) +
            ((100 * (inputSize V + 1) + 6) * qs.length + 2) + 2 := by omega
        _ = (100 * (inputSize V + 1) + 6) * (q :: qs).length + 2 := by
          simp only [List.length_cons]
          ring
    · exact ⟨by rw [dout, bout, List.flatMap_cons, List.append_assoc], bf.trans df⟩

end NearCubicGates.Adapters.Proximity.Trim
