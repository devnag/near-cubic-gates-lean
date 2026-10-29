import SourceAdapters.Proximity.TrimCollect
import SourceAdapters.Code.DistinctRecords

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid numeric sorting followed by exact adjacent deduplication.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
variable {C : Ctx}

def distinctCountReg : Fin VV := 48

def dedupRegisters : DistinctRecords.Registers :=
  ⟨proofCountReg, distinctCountReg, 49, 50, 51⟩

theorem dedupRegisters_valid : dedupRegisters.Valid := by
  unfold DistinctRecords.Registers.Valid
  decide

def sortUniqueProgram : St VV MM := .seq (.op (.rwM proofStore))
  (.seq (.op (.srtM proofStore)) (DistinctRecords.script dedupRegisters proofStore distinctStore))

def UniquePost (a : DS VV MM) (records : List ℕ) (b : DS VV MM) : Prop :=
  b.ram distinctStore = records.toFinset.sort (· ≤ ·) ∧
  b.env distinctCountReg = records.toFinset.card ∧ b.rc distinctStore = records.toFinset.card ∧
  b.ram proofStore = records.insertionSort (· ≤ ·) ∧ b.rc proofStore = records.length ∧
  b.env proofCountReg = records.length ∧ Cst b ∧
  b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
  (∀ m, m ≠ proofStore → m ≠ distinctStore → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
  Fr a b (DistinctRecords.scratch dedupRegisters)

theorem sort_unique_program (a : DS VV MM) (hc : Cst a) (records : List ℕ)
    (hm : a.ram proofStore = records) (hlen : a.env proofCountReg = records.length)
    (hempty : a.ram distinctStore = []) (hcursor : a.rc distinctStore = 0)
    (hwidth : records.length < 2 ^ C.Wd) (hvalues : ∀ v ∈ records, v < 2 ^ C.Wd) :
    Hs C sortUniqueProgram a (a.rc proofStore + 22 * (records.length + 1) + 5)
      (UniquePost a records) := by
  let sorted := records.insertionSort (· ≤ ·)
  let b := (a.rew proofStore).srt proofStore
  have hsort : sorted.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hfin : sorted.toFinset = records.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    exact (List.perm_insertionSort _ _).mem_iff
  have hd : sorted.dedup = records.toFinset.sort (· ≤ ·) := by
    rw [DistinctRecords.dedup_eq_sort sorted hsort, hfin]
  have hdlen : sorted.dedup.length = records.toFinset.card := by rw [hd]; simp
  have hbsource : b.ram proofStore = sorted := by simp [b, DS.srt, DS.rew, hm, sorted]
  obtain ⟨d, nd, ed, hcost, dm, ds, dn, dl, dsrc, drc, dc, dip, dout, dkin, dkout, dkc, dother, dvars⟩ :=
    DistinctRecords.script_contract dedupRegisters proofStore distinctStore
      dedupRegisters_valid (by decide) C b sorted (by exact ⟨hc.z, hc.one, hc.two⟩) hsort hbsource
      (by simp [b, DS.srt, DS.rew])
      (by simpa [b, DS.srt, DS.rew, distinctStore, proofStore] using hempty)
      (by simpa [b, DS.srt, DS.rew, distinctStore, proofStore] using hcursor)
      (by simpa only [b, DS.srt, DS.rew, dedupRegisters, sorted, List.length_insertionSort] using hlen)
      (by simpa only [sorted, List.length_insertionSort] using hwidth)
      (fun v hv => hvalues v ((List.perm_insertionSort _ _).mem_iff.mp hv))
  have esort := Ex.op (OpEx.srtM (C := C) proofStore (a.rew proofStore)
    (by simp [DS.rew]))
  refine ⟨d, _, Ex.seq (Ex.op (OpEx.rwM proofStore a)) (Ex.seq esort ed), ?_, ?_⟩
  · change a.rc proofStore + 1 + ((a.ram proofStore).length + 1 + nd + 1) + 1 ≤ _
    rw [hm]
    simp only [sorted, List.length_insertionSort] at hcost
    omega
  · refine ⟨?_, ?_, ?_, ds, ?_, ?_, dc, dip, dout, dkin, dkout, dkc, ?_, ?_⟩
    · exact dm.trans hd
    · exact dn.trans hdlen
    · exact drc.trans hdlen
    · simpa only [sorted, List.length_insertionSort] using dsrc
    · simpa only [dedupRegisters, sorted, List.length_insertionSort] using dl
    · intro m hp hd'
      obtain ⟨hm', hr'⟩ := dother m hp hd'
      constructor
      · simpa only [b, DS.srt, DS.rew, Function.update_of_ne hp] using hm'
      · simpa only [b, DS.srt, DS.rew, Function.update_of_ne hp] using hr'
    · exact dvars

end NearCubicGates.Adapters.Proximity.Trim
