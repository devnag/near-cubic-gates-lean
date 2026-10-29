import SourceAdapters.Proximity.TrimHonestFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": guarded lookup of an original finite proof coordinate. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def lookupTemps : List (Fin VV) := [c0, vJ, rankReg, valueReg]
def originalLookup : St VV MM := BitLookup.script proofStore halfReg proofLength valueReg

theorem original_lookup (a : DS VV MM) (hc : Cst a) {N : ℕ} (proof : BitInput N)
    (hm : a.ram proofStore = (List.ofFn proof).map Bool.toNat)
    (hlen : a.env proofLength = N) (hrc : a.rc proofStore ≤ N) (hW : N < 2 ^ C.Wd) :
    Hs C originalLookup a (6 * N + 10) (fun b =>
      b.env valueReg = (finiteProofOracle proof (a.env halfReg)).toNat ∧ b.out = a.out ∧
      b.rc proofStore ≤ N ∧ b.rc auxiliaryStore = a.rc auxiliaryStore ∧
      b.rc keyStore = a.rc keyStore ∧ LookupFrame lookupTemps a b) := by
  have he := HonestLoading.finite_lookup C proofStore halfReg proofLength valueReg
    (by decide) (by decide) (by decide) (by decide) a hc proof hm hlen hrc hW
  refine he.mono le_rfl ?_
  rintro b ⟨bv, _, _, _, bi, bo, bm, bki, bko, bkc, bc, bp, bf⟩
  refine ⟨bv, bo, bp, bc auxiliaryStore (by decide), bc keyStore (by decide), ?_⟩
  refine ⟨bm, ?_, bi, bki, bko, bkc, bf.weaken (by simp [lookupTemps])⟩
  intro m hm
  exact bc m (by intro h; apply hm; simp [lookupStores, h])

end NearCubicGates.Adapters.Proximity.TrimHonest
