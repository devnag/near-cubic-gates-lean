import SourceAdapters.Code.RecordLookup
import SourceAdapters.Code.BitLookup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid dictionary lookup through a first-occurrence record
index and a guarded bit-store fetch. Missing keys return false. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DictionaryBitLookup

open NearCubicGates.Close.Cells

def script (keysStore valuesStore : Fin MM) (target len rank result : Fin VV) : St VV MM :=
  .seq (RecordLookup.script keysStore target len rank) (BitLookup.script valuesStore rank len result)

/-- The numeric target is only compared. Both scans have a stored-length
bound, and an absent target reaches the guarded default-false branch. -/
theorem runs (C : Ctx) (keysStore valuesStore : Fin MM) (target len rank result : Fin VV)
    (hstores : keysStore ≠ valuesStore)
    (ht : target ∉ [c0, vJ, rank, result]) (hl : len ∉ [c0, vJ, rank, result])
    (hr : rank ∉ [c0, vJ, result])
    (hcst : vZ ∉ [c0, vJ, rank, result] ∧ v1 ∉ [c0, vJ, rank, result] ∧
      v2 ∉ [c0, vJ, rank, result])
    (a : DS VV MM) (hc : Cst a) (keys : List ℕ) (bits : List Bool)
    (hsame : bits.length = keys.length)
    (hkeys : a.ram keysStore = keys) (hbits : a.ram valuesStore = bits.map Bool.toNat)
    (hlen : a.env len = keys.length) (hcursor : a.rc valuesStore ≤ keys.length)
    (hwidth : keys.length < 2 ^ C.Wd) :
    Hs C (script keysStore valuesStore target len rank result) a
      (a.rc keysStore + 15 * keys.length + 19) (fun b =>
      b.env result = (bits.getD (keys.idxOf (a.env target)) false).toNat ∧
      b.env target = a.env target ∧ b.env len = keys.length ∧ Cst b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      b.rc keysStore = keys.length ∧ b.rc valuesStore ≤ keys.length ∧
      (∀ q, q ≠ keysStore → q ≠ valuesStore → b.rc q = a.rc q) ∧
      Fr a b [c0, vJ, rank, result]) := by
  have sub1 : [c0, vJ, rank] ⊆ [c0, vJ, rank, result] := by
    intro i hi
    simp only [List.mem_cons] at hi ⊢
    tauto
  have sub2 : [c0, vJ, result] ⊆ [c0, vJ, rank, result] := by
    intro i hi
    simp only [List.mem_cons] at hi ⊢
    tauto
  have hr0 : rank ≠ c0 := by intro he; apply hr; simp [he]
  have hrj : rank ≠ vJ := by intro he; apply hr; simp [he]
  have hrl : rank ≠ len := by intro he; apply hl; simp [← he]
  have first := RecordLookup.runs C keysStore target len rank
    (fun hi => ht (sub1 hi)) (fun hi => hl (sub1 hi)) hr0 hrj
    ⟨fun hi => hcst.1 (sub1 hi), fun hi => hcst.2.1 (sub1 hi), fun hi => hcst.2.2 (sub1 hi)⟩
    a hc keys hkeys hlen hwidth
  refine Hs.mono (Hs.seq (t2 := 6 * keys.length + 10) first (fun b hb => ?_)) (by omega)
    (fun _ h => h)
  rcases hb with ⟨brank, _, blen, bc, bi, bo, bm, bkey, bothers, bki, bko, bkc, bf⟩
  have second := BitLookup.runs C valuesStore rank len result hrl hr
    (fun hi => hl (sub2 hi))
    ⟨fun hi => hcst.1 (sub2 hi), fun hi => hcst.2.1 (sub2 hi), fun hi => hcst.2.2 (sub2 hi)⟩
    b bc bits (by rw [bm, hbits]) (blen.trans hsame.symm)
    (by rw [bothers valuesStore hstores.symm, hsame]; exact hcursor)
    (by rw [hsame]; exact hwidth)
  refine Hs.mono second (by rw [hsame]) ?_
  rintro d ⟨dresult, _, dlen, dc, di, dout, dm, dki, dko, dkc, dothers, dvalue, df⟩
  have af : Fr a d [c0, vJ, rank, result] := (bf.weaken sub1).trans (df.weaken sub2)
  refine ⟨?_, af target ht, dlen.trans hsame, dc, di.trans bi, dout.trans bo, dm.trans bm,
    dki.trans bki, dko.trans bko, dkc.trans bkc, ?_, ?_, ?_, af⟩
  · simpa only [brank] using dresult
  · exact (dothers keysStore hstores).trans bkey
  · simpa only [hsame] using dvalue
  · intro q hqk hqv
    exact (dothers q hqv).trans (bothers q hqk)

end NearCubicGates.Adapters.Code.DictionaryBitLookup
