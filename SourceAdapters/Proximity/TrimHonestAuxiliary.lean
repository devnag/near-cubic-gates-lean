import SourceAdapters.Proximity.TrimHonestOriginal
import SourceAdapters.Proximity.TrimHonestDictionary

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": an auxiliary proof coordinate is fetched from its actual
finite key and value stores, with exact false semantics for missing keys. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def auxiliaryLookup : St VV MM :=
  DictionaryBitLookup.script keyStore auxiliaryStore addressReg auxiliaryLength rankReg valueReg

theorem auxiliary_lookup_run {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (a : DS VV MM) (hc : Cst a)
    (hkeys : a.ram keyStore = auxKeys (2 ^ V.randomBits) (blockVariableBound q))
    (hbits : a.ram auxiliaryStore = (auxValues V input proof).map Bool.toNat)
    (hlen : a.env auxiliaryLength = (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length)
    (hcursor : a.rc auxiliaryStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length)
    (hwidth : (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length < 2 ^ C.Wd)
    (hodd : a.env addressReg % 2 ≠ 0) :
    Hs C auxiliaryLookup a
      (a.rc keyStore + 15 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 19)
      (fun b => b.env valueReg = (canonicalClauseProof V input proof (a.env addressReg)).toNat ∧
        b.out = a.out ∧ b.rc proofStore = a.rc proofStore ∧
        b.rc auxiliaryStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length ∧
        b.rc keyStore = (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length ∧
        LookupFrame lookupTemps a b) := by
  have he := DictionaryBitLookup.runs C keyStore auxiliaryStore addressReg auxiliaryLength rankReg valueReg
    (by decide) (by decide) (by decide) (by decide) (by decide) a hc
    (auxKeys (2 ^ V.randomBits) (blockVariableBound q)) (auxValues V input proof)
    (by simp [auxValues]) hkeys hbits hlen hcursor hwidth
  refine he.mono le_rfl ?_
  rintro b ⟨bv, _, _, _, bi, bo, bm, bki, bko, bkc, bk, ba, bc, bf⟩
  refine ⟨?_, bo, bc proofStore (by decide) (by decide), ba, bk, ?_⟩
  · simpa only [auxiliary_lookup V input proof (a.env addressReg) hodd] using bv
  · refine ⟨bm, ?_, bi, bki, bko, bkc, bf⟩
    intro m hm
    exact bc m (by intro h; apply hm; simp [lookupStores, h])
      (by intro h; apply hm; simp [lookupStores, h])

end NearCubicGates.Adapters.Proximity.TrimHonest
