import SourceAdapters.Code.DistinctRecordsLoop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": a paid linear scan removes adjacent duplicates from sorted
record stores, preserving all input contents and unrelated live state. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

def setup (r : Registers) : St VV MM :=
  .seq (.op (.zero r.count)) (.seq (.op (.zero r.started)) (.op (.zero c0)))

def initial (r : Registers) (a : DS VV MM) : DS VV MM :=
  ((a.set r.count 0).set r.started 0).set c0 0

def script (r : Registers) (source destination : Fin MM) : St VV MM :=
  .seq (setup r) (sweep r source destination)

theorem setup_runs (C : Ctx) (r : Registers) (a : DS VV MM) :
    Ex C (setup r) a (initial r a) 5 :=
  Ex.seq (Ex.op (OpEx.zero r.count a))
    (Ex.seq (Ex.op (OpEx.zero r.started _)) (Ex.op (OpEx.zero c0 _)))

theorem setup_frame (r : Registers) (source destination : Fin MM) (a : DS VV MM) :
    Frame r source destination a (initial r a) :=
  (Frame.set r source destination a r.count 0 (by simp [scratch])).trans
    ((Frame.set r source destination _ r.started 0 (by simp [scratch])).trans
      (Frame.set r source destination _ c0 0 (by simp [scratch])))

/-- The full ordinary Cells contract. It includes empty inputs, duplicate zero
records, and arbitrary width-fitting record values without iterating to them. -/
theorem script_contract (r : Registers) (source destination : Fin MM) :
    Contract r source destination (script r source destination) := by
  intro hv hsd C a records hc hsorted hsource hcursor hempty hdcursor hlen hwidth _
  obtain ⟨h0, _, _, _, _, _, _, hsn⟩ := r.separations hv
  have h0n : r.count ≠ c0 := by intro he; apply h0; simp [he]
  have h0s : r.started ≠ c0 := by intro he; apply h0; simp [he]
  let a0 := initial r a
  have hf : Frame r source destination a a0 := setup_frame r source destination a
  have hn : a0.env r.count = 0 := by simp [a0, initial, DS.set, h0n, Ne.symm hsn]
  have hh : History r a0 none := by simp [History, a0, initial, DS.set, h0s]
  have hl := sweep_spec C r hv source destination hsd records a0 [] [] none (hf.cst hv hc)
    (by simpa [a0, initial] using hsource) hcursor (by simp [a0, initial])
    (by simpa [hf.length_env hv] using hlen) hempty hdcursor hn hh (by simp) (by simpa using hwidth)
  obtain ⟨b, n, he, hcost, bm, brc, bn, bs, bi, bf⟩ := hl
  have hall := hf.trans bf
  have hd : scan none records = records.dedup := scan_eq_dedup records hsorted
  refine ⟨b, 5 + n + 1, Ex.seq (setup_runs C r a) he, ?_, ?_⟩
  · change n ≤ 15 * records.length + 2 at hcost
    omega
  · refine ⟨?_, hall.ramSource.trans hsource, ?_, (hall.length_env hv).trans hlen,
      ?_, ?_, hall.cst hv hc, hall.ip, hall.out, hall.kin, hall.kout, hall.kc, hall.other, hall.env⟩
    · simpa [hd] using bm
    · simpa [hd] using bn
    · simpa using bs
    · simpa [hd] using brc

/-- The contract's list is exactly the increasing list of distinct values. -/
theorem dedup_eq_sort (records : List ℕ) (h : records.Pairwise (· ≤ ·)) :
    records.dedup = records.toFinset.sort (· ≤ ·) := by
  have hp : records.dedup.Pairwise (· ≤ ·) := h.sublist (List.dedup_sublist records)
  have hs := (List.toFinset_sort (r := (· ≤ ·)) (List.nodup_dedup records)).2 hp
  have hf : records.dedup.toFinset = records.toFinset := by ext value; simp
  rw [hf] at hs
  exact hs.symm

end NearCubicGates.Adapters.Code.DistinctRecords
