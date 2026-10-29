import SourceAdapters.Code.DistinctRecordsStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the scan iterates once per input record, never per value. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

def sweep (r : Registers) (source destination : Fin MM) : St VV MM :=
  .loop (.lt c0 r.length) (step r source destination)

def LoopPost (r : Registers) (source destination : Fin MM) (a : DS VV MM)
    (output : List ℕ) (stop : ℕ) (b : DS VV MM) : Prop :=
  b.ram destination = output ∧ b.rc destination = output.length ∧ b.env r.count = output.length ∧
  b.rc source = stop ∧ b.env c0 = stop ∧ Frame r source destination a b

theorem sweep_spec (C : Ctx) (r : Registers) (hv : r.Valid)
    (source destination : Fin MM) (hsd : source ≠ destination) :
    ∀ (records : List ℕ) (a : DS VV MM) (past output : List ℕ) (previous : Option ℕ),
      Cst a → a.ram source = past ++ records → a.rc source = past.length →
      a.env c0 = past.length → a.env r.length = past.length + records.length →
      a.ram destination = output → a.rc destination = output.length → a.env r.count = output.length →
      History r a previous → output.length ≤ past.length → past.length + records.length < 2 ^ C.Wd →
      Hs C (sweep r source destination) a (15 * records.length + 2)
        (LoopPost r source destination a (output ++ scan previous records) (past.length + records.length)) := by
  have hcl : c0 ≠ r.length := by
    intro he
    apply (List.nodup_cons.mp hv.1).1
    simp [scratch, ← he]
  intro records
  induction records with
  | nil =>
    intro a past output previous _ _ hcursor hi hlen hm hrc hn _ _ _
    refine ⟨a, 2, Ex.loopF hcl (by simp [Cnd.eval, hi, hlen]), by simp, ?_⟩
    simpa [LoopPost, scan, hcursor, hi] using
      (show a.ram destination = output ∧ a.rc destination = output.length ∧
        a.env r.count = output.length ∧ Frame r source destination a a from
        ⟨hm, hrc, hn, Frame.refl r source destination a⟩)
  | cons value records ih =>
    intro a past output previous hc hsource hcursor hi hlen hm hrc hn hh hcount hwidth
    have ht : (Cnd.lt c0 r.length).eval a = true := by simp [Cnd.eval, hi, hlen]
    have hread : a.rc source < (a.ram source).length := by simp [hsource, hcursor]
    have hvalue : (a.ram source).getD (a.rc source) 0 = value := by
      rw [hsource, hcursor]
      simp
    have hs := step_spec C r hv source destination hsd a hc output value previous hm hrc hn hh hread hvalue
      (by simp only [List.length_cons] at hwidth; omega)
      (by rw [hi]; simp only [List.length_cons] at hwidth; omega)
    obtain ⟨b, n, he, hcost, bm, brc, bn, bp, bs, bsource, bi, bf⟩ := hs
    have hbsource : b.ram source = (past ++ [value]) ++ records := by
      rw [bf.ramSource, hsource]
      simp
    have hbcur : b.rc source = (past ++ [value]).length := by
      rw [bsource, hcursor]
      simp
    have hbi : b.env c0 = (past ++ [value]).length := by
      rw [bi, hi]
      simp
    have hblen : b.env r.length = (past ++ [value]).length + records.length := by
      rw [bf.length_env hv, hlen]
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    have hbh : History r b (some value) := by
      refine ⟨bs, ?_⟩
      intro v heq
      cases heq
      exact bp
    have hbc : (output ++ emitted previous value).length ≤ (past ++ [value]).length := by
      have h := emitted_length previous value
      simp only [List.length_append, List.length_singleton]
      omega
    have hbw : (past ++ [value]).length + records.length < 2 ^ C.Wd := by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hwidth
      omega
    obtain ⟨d, k, hek, hkc, dm, drc, dn, dsource, di, df⟩ :=
      ih b (past ++ [value]) (output ++ emitted previous value) (some value)
        (bf.cst hv hc) hbsource hbcur hbi hblen bm brc bn hbh hbc hbw
    refine ⟨d, n + k + 2, Ex.loopT hcl ht he hek, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, bf.trans df⟩
      · simpa [scan, List.append_assoc] using dm
      · simpa [scan, List.append_assoc] using drc
      · simpa [scan, List.append_assoc] using dn
      · simp only [List.length_append, List.length_cons, List.length_nil] at dsource ⊢
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil] at di ⊢
        omega

end NearCubicGates.Adapters.Code.DistinctRecords
