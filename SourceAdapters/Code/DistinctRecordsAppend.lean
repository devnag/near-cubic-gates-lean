import SourceAdapters.Code.DistinctRecordsFrame
import SourceAdapters.Code.DistinctRecordsRegisters

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid retention of one new distinct record. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

def keep (r : Registers) (destination : Fin MM) : St VV MM :=
  .seq (.op (.wrM destination r.current)) (.seq (.op (.copy r.previous r.current))
    (.seq (.op (.inc r.count)) (.op (.copy r.started v1))))

def kept (r : Registers) (destination : Fin MM) (a : DS VV MM) : DS VV MM :=
  (((a.put destination (a.env r.current)).set r.previous (a.env r.current)).set r.count
    (a.env r.count + 1)).set r.started 1

theorem keep_runs (C : Ctx) (r : Registers) (hv : r.Valid) (destination : Fin MM)
    (a : DS VV MM) (hc : Cst a) (hcursor : a.rc destination ≤ (a.ram destination).length)
    (hwidth : a.env r.count + 1 < 2 ^ C.Wd) :
    Ex C (keep r destination) a (kept r destination a) 7 := by
  obtain ⟨_, _, hcp, _, _, _, hpn, _⟩ := r.separations hv
  have h1p : v1 ≠ r.previous := by intro he; apply hv.2.2.1; simp [scratch, he]
  have h1n : v1 ≠ r.count := by intro he; apply hv.2.2.1; simp [scratch, he]
  have hs1 : r.started ≠ v1 := by intro he; apply hv.2.2.1; simp [scratch, he]
  let a1 := a.put destination (a.env r.current)
  let a2 := a1.set r.previous (a.env r.current)
  let a3 := a2.set r.count (a.env r.count + 1)
  have e1 := Ex.op (OpEx.wrM (C := C) destination r.current a hcursor)
  have e2 : Ex C (.op (.copy r.previous r.current)) a1 a2 1 :=
    Ex.op (OpEx.copy r.previous r.current a1 (Ne.symm hcp))
  have e3 : Ex C (.op (.inc r.count)) a2 a3 1 := by
    have hn : a2.env r.count = a.env r.count := by simp [a2, a1, DS.put, Ne.symm hpn]
    have e := Ex.op (OpEx.inc (C := C) r.count a2 (by rw [hn]; exact hwidth))
    simpa only [hn] using e
  have e4 : Ex C (.op (.copy r.started v1)) a3 (a3.set r.started 1) 1 := by
    have h1 : a3.env v1 = 1 := by simp [a3, a2, a1, DS.put, h1p, h1n, hc.one]
    simpa only [h1] using Ex.op (OpEx.copy (C := C) r.started v1 a3 hs1)
  exact Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))

theorem keep_frame (r : Registers) (source destination : Fin MM) (hsd : source ≠ destination)
    (a : DS VV MM) : Frame r source destination a (kept r destination a) := by
  exact (Frame.put r source destination hsd a _).trans
    ((Frame.set r source destination _ r.previous _ (by simp [scratch])).trans
      ((Frame.set r source destination _ r.count _ (by simp [scratch])).trans
        (Frame.set r source destination _ r.started _ (by simp [scratch]))))

end NearCubicGates.Adapters.Code.DistinctRecords
