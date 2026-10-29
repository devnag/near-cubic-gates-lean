import SourceAdapters.Proximity.TrimUnique
import SourceAdapters.Proximity.TrimAddressBounds

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": preparation composes paid parsing, proof-address collection,
numeric sorting and distinct-address extraction on the same machine state. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def prepareProgram : St VV MM := .seq loadProgram (.seq collectProgram sortUniqueProgram)

def prepareTemps : List (Fin VV) := loadTemps ++
  DistinctRecords.scratch collectRegisters ++ DistinctRecords.scratch dedupRegisters

structure Prepared (a b : DS VV MM) {n : ℕ} (V : ThreeQueryVerifier n) : Prop where
  arity : b.env arityReg = n
  randomness : b.env randomReg = V.randomBits
  rows : b.env rowsReg = 2 ^ V.randomBits
  fieldsCount : b.env fieldsReg = (fields V).length
  proofCount : b.env proofCountReg = (proofValues V).length
  distinctCount : b.env distinctCountReg = (usedProofAddresses V).card
  queryRAM : b.ram sN = fields V
  proofRAM : b.ram proofStore = (proofValues V).insertionSort (· ≤ ·)
  distinctRAM : b.ram distinctStore = trimSortedAddresses ⟨n, V⟩
  queryCursor : b.rc sN = (fields V).length
  proofCursor : b.rc proofStore = (proofValues V).length
  distinctCursor : b.rc distinctStore = (usedProofAddresses V).card
  other : ∀ m, m ≠ sN → m ≠ proofStore → m ≠ distinctStore →
    b.ram m = a.ram m ∧ b.rc m = a.rc m
  input : b.ip = a.ip + (trimRequestWord ⟨n, V⟩).length
  output : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  constants : Cst b
  vars : Fr a b prepareTemps

theorem prepare_program {n : ℕ} (V : ThreeQueryVerifier n) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = trimRequestWord ⟨n, V⟩)
    (hq : a.ram sN = []) (hqrc : a.rc sN = 0)
    (hp : a.ram proofStore = []) (hprc : a.rc proofStore = 0)
    (hu : a.ram distinctStore = []) (hurc : a.rc distinctStore = 0)
    (hW : inputSize V + 2 ≤ C.Wd) :
    Hs C prepareProgram a (500 * (inputSize V + 1) ^ 2) (fun b => Prepared a b V) := by
  obtain ⟨b, nb, eb, hb, lb⟩ := load_program (C := C) V a hc hin (by rw [hqrc, hq]; rfl) hW
  have bm : ∀ m, m ≠ sN → b.ram m = a.ram m := by
    intro m hm
    rw [lb.ram, Function.update_of_ne hm]
  have br : ∀ m, m ≠ sN → b.rc m = a.rc m := by
    intro m hm
    rw [lb.cursor, Function.update_of_ne hm]
  have bq : b.ram sN = fields V := by rw [lb.ram, Function.update_self, hq]; simp
  have bqr : b.rc sN = (fields V).length := by rw [lb.cursor, Function.update_self, hq]; simp
  have hfieldFit : (fields V).length < 2 ^ C.Wd := by
    have hl := fields_count_le V
    exact lt_of_lt_of_le (by omega : (fields V).length < C.Wd) (Nat.lt_two_pow_self).le
  obtain ⟨c, nc, ec, hcCost, cm, crc, cn, cqrc, ci, cf⟩ :=
    collect_program (C := C) (queries V) b (lb.constants hc) bq
      ((bm proofStore (by decide)).trans hp) ((br proofStore (by decide)).trans hprc)
      lb.count hfieldFit
  have cu : c.ram distinctStore = [] :=
    ((cf.other distinctStore (by decide) (by decide)).1.trans (bm distinctStore (by decide))).trans hu
  have cur : c.rc distinctStore = 0 :=
    ((cf.other distinctStore (by decide) (by decide)).2.trans (br distinctStore (by decide))).trans hurc
  obtain ⟨d, nd, ed, hdCost, ud, udn, udrc, up, uprc, upn, dc,
      dip, dout, dkin, dkout, dkc, dother, dvars⟩ :=
    sort_unique_program (C := C) c (cf.cst collectRegisters_valid (lb.constants hc))
      (proofValues V) cm cn cu cur (proofValues_count_fit V hW)
      (fun v hv => proofValues_fit V hW hv)
  have hfl := fields_count_le V
  have hpl := proofValues_length_le V
  have hql : (queries V).length ≤ inputSize V := by
    have h := hfl
    rw [fields, flatFields_length] at h
    omega
  have hcol : nc ≤ (fields V).length + 16 * (queries V).length + 8 := by
    simpa only [bqr] using hcCost
  have hunique : nd ≤ (proofValues V).length + 22 * ((proofValues V).length + 1) + 5 := by
    simpa only [crc, proofValues] using hdCost
  have lob := lb.other
  simp only [Prod.mk.injEq] at lob
  refine ⟨d, nb + (nc + nd + 1) + 1, Ex.seq eb (Ex.seq ec ed), by nlinarith, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, upn, ?_, ?_, up, ?_, ?_, uprc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dc, ?_⟩
  · rw [dvars arityReg (by decide), cf.env arityReg (by decide)]
    exact lb.arity
  · rw [dvars randomReg (by decide), cf.env randomReg (by decide)]
    exact lb.randomness
  · rw [dvars rowsReg (by decide), cf.env rowsReg (by decide)]
    exact lb.rows
  · rw [dvars fieldsReg (by decide), cf.env fieldsReg (by decide)]
    exact lb.count
  · simpa only [proofValues_toFinset] using udn
  · rw [(dother sN (by decide) (by decide)).1, cf.ramSource]
    exact bq
  · rw [← proofValues_sorted V]
    exact ud
  · rw [(dother sN (by decide) (by decide)).2, cqrc]
    exact (flatFields_length (queries V)).symm
  · simpa only [proofValues_toFinset] using udrc
  · intro m hmq hmp hmu
    obtain ⟨dm, dr⟩ := dother m hmp hmu
    obtain ⟨cm', cr'⟩ := cf.other m hmq hmp
    exact ⟨dm.trans (cm'.trans (bm m hmq)), dr.trans (cr'.trans (br m hmq))⟩
  · exact dip.trans (cf.ip.trans lb.input)
  · exact dout.trans (cf.out.trans lob.1)
  · exact dkin.trans (cf.kin.trans lob.2.1)
  · exact dkout.trans (cf.kout.trans lob.2.2.1)
  · exact dkc.trans (cf.kc.trans lob.2.2.2)
  · exact Fr.trans (lb.vars.weaken (by intro x hx; simp [prepareTemps, hx]))
      (Fr.trans (cf.env.weaken (by intro x hx; simp [prepareTemps, hx]))
        (dvars.weaken (by intro x hx; simp [prepareTemps, hx])))

end NearCubicGates.Adapters.Proximity.Trim
