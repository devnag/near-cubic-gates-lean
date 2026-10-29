import SourceAdapters.Proximity.TrimCollectStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the address collector visits every query exactly once.
The measure is remaining query records; address magnitudes do not enter it. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def collectSweep : St VV MM := .loop (.lt c0 fieldsReg) collectStep

def CollectLoopPost (a : DS VV MM) (output : List ℕ) (stop : ℕ) (b : DS VV MM) : Prop :=
  b.ram proofStore = output ∧ b.rc proofStore = output.length ∧
  b.env proofCountReg = output.length ∧ b.rc sN = stop ∧ b.env c0 = stop ∧ CollectFrame a b

theorem collect_sweep {n : ℕ} :
    ∀ (qs : List (SignedQuery n)) (a : DS VV MM) (past output : List ℕ),
      Cst a → a.ram sN = past ++ qs.flatMap trimQueryFields → a.rc sN = past.length →
      a.env c0 = past.length → a.env fieldsReg = past.length + 3 * qs.length →
      a.ram proofStore = output → a.rc proofStore = output.length →
      a.env proofCountReg = output.length → output.length ≤ past.length →
      past.length + 3 * qs.length < 2 ^ C.Wd →
      Hs C collectSweep a (16 * qs.length + 2)
        (CollectLoopPost a (output ++ qs.flatMap queryProofValues) (past.length + 3 * qs.length)) := by
  intro qs
  induction qs with
  | nil =>
    intro a past output _ _ hcursor hi hlen hm hrc hn _ _
    refine ⟨a, 2, Ex.loopF (show c0 ≠ fieldsReg by decide)
      (by simp [Cnd.eval, hi, hlen]), by simp, ?_⟩
    simpa [CollectLoopPost, hcursor, hi] using
      (show a.ram proofStore = output ∧ a.rc proofStore = output.length ∧
        a.env proofCountReg = output.length ∧ CollectFrame a a from
        ⟨hm, hrc, hn, DistinctRecords.Frame.refl _ _ _ a⟩)
  | cons q qs ih =>
    intro a past output hc hsource hcursor hi hlen hm hrc hn hcount hwidth
    have ht : (Cnd.lt c0 fieldsReg).eval a = true := by simp [Cnd.eval, hi, hlen]
    have hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ qs.flatMap trimQueryFields := by
      rw [hsource, hcursor, List.drop_left, List.flatMap_cons]
    obtain ⟨b, nb, eb, hb, bm, brc, bn, bsrc, bi, _, bf⟩ :=
      collect_step (C := C) q a hc output (qs.flatMap trimQueryFields) hread hm hrc hn
        (by simp only [List.length_cons] at hwidth; omega)
        (by rw [hi]; simp only [List.length_cons] at hwidth; omega)
    have hbsource : b.ram sN = (past ++ trimQueryFields q) ++ qs.flatMap trimQueryFields := by
      rw [bf.ramSource, hsource, List.flatMap_cons, List.append_assoc]
    have hbcur : b.rc sN = (past ++ trimQueryFields q).length := by
      rw [bsrc, hcursor, List.length_append, queryFields_length]
    have hbi : b.env c0 = (past ++ trimQueryFields q).length := by
      rw [bi, hi, List.length_append, queryFields_length]
    have hblen : b.env fieldsReg = (past ++ trimQueryFields q).length + 3 * qs.length := by
      rw [bf.env fieldsReg (by decide), hlen]
      simp only [List.length_cons, List.length_append, queryFields_length]
      omega
    have hq : (queryProofValues q).length ≤ 1 := by
      cases h : q.address <;> simp [queryProofValues, h]
    have hbc : (output ++ queryProofValues q).length ≤ (past ++ trimQueryFields q).length := by
      simp only [List.length_append, queryFields_length]
      omega
    have hbw : (past ++ trimQueryFields q).length + 3 * qs.length < 2 ^ C.Wd := by
      simp only [List.length_append, queryFields_length]
      simp only [List.length_cons] at hwidth
      omega
    obtain ⟨d, nd, ed, hd, dm, drc, dn, dsrc, di, df⟩ :=
      ih b (past ++ trimQueryFields q) (output ++ queryProofValues q)
        (bf.cst collectRegisters_valid hc) hbsource hbcur hbi hblen bm brc bn hbc hbw
    refine ⟨d, nb + nd + 2, Ex.loopT (show c0 ≠ fieldsReg by decide) ht eb ed, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, bf.trans df⟩
      · simpa only [List.flatMap_cons, List.append_assoc] using dm
      · simpa only [List.flatMap_cons, List.append_assoc] using drc
      · simpa only [List.flatMap_cons, List.append_assoc] using dn
      · simp only [List.length_append, queryFields_length, List.length_cons] at dsrc ⊢
        omega
      · simp only [List.length_append, queryFields_length, List.length_cons] at di ⊢
        omega

end NearCubicGates.Adapters.Proximity.Trim
