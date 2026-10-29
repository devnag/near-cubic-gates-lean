import SourceAdapters.Proximity.TrimHonestAuxiliary
import SourceAdapters.Proximity.TrimHonestAddress

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual parity dispatch between the finite original proof
and the finite auxiliary dictionary. Both branches have paid finite scans. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def chooseLookup : St VV MM := .ite (.eq addressReg evenReg) originalLookup auxiliaryLookup

theorem canonical_even {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (address : ℕ) (h : address % 2 = 0) :
    canonicalClauseProof V input proof address = proof (address / 2) := by
  calc
    canonicalClauseProof V input proof address =
        canonicalClauseProof V input proof (2 * (address / 2)) :=
      congrArg _ ((address_even_iff address).mpr h)
    _ = proof (address / 2) := by simp only [canonicalClauseProof, combineProof_even]

theorem choose_lookup {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) (a : DS VV MM) (hc : Cst a)
    (hm : a.ram proofStore = (List.ofFn proof).map Bool.toNat)
    (hlen : a.env proofLength = N) (hrc : a.rc proofStore ≤ N) (hW : N < 2 ^ C.Wd)
    (hkeys : a.ram keyStore = auxKeys (2 ^ V.randomBits) (blockVariableBound q))
    (hbits : a.ram auxiliaryStore = (auxValues V input (finiteProofOracle proof)).map Bool.toNat)
    (hal : a.env auxiliaryLength = (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length)
    (hac : a.rc auxiliaryStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length)
    (hkc : a.rc keyStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length)
    (haw : (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length < 2 ^ C.Wd)
    (hh : a.env halfReg = a.env addressReg / 2)
    (he : a.env evenReg = 2 * (a.env addressReg / 2)) :
    Hs C chooseLookup a
      (6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 21)
      (fun b => b.env valueReg =
          (canonicalClauseProof V input (finiteProofOracle proof) (a.env addressReg)).toNat ∧
        b.out = a.out ∧ b.rc proofStore ≤ N ∧
        b.rc auxiliaryStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length ∧
        b.rc keyStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length ∧
        LookupFrame lookupTemps a b) := by
  by_cases hp : a.env addressReg % 2 = 0
  · have ht : Cnd.eval a (.eq addressReg evenReg) = true := by
      simp only [Cnd.eval, he]
      exact decide_eq_true ((address_even_iff _).mpr hp)
    have run := Hs.iteT (c := Cnd.eq addressReg evenReg) (u := auxiliaryLookup)
      (show addressReg ≠ evenReg by decide)
      ht (original_lookup (C := C) a hc proof hm hlen hrc hW)
    refine run.mono (by omega) ?_
    rintro b ⟨bv, bo, bp, ba, bk, bf⟩
    exact ⟨by simpa only [canonical_even V input (finiteProofOracle proof) _ hp, hh] using bv,
      bo, bp, by rw [ba]; exact hac, by rw [bk]; exact hkc, bf⟩
  · have ht : Cnd.eval a (.eq addressReg evenReg) = false := by
      simp only [Cnd.eval, he]
      exact decide_eq_false ((address_even_iff _).not.mpr hp)
    have run := Hs.iteF (c := Cnd.eq addressReg evenReg) (s := originalLookup)
      (show addressReg ≠ evenReg by decide)
      ht (auxiliary_lookup_run (C := C) V input (finiteProofOracle proof) a hc
        hkeys hbits hal hac haw hp)
    refine run.mono (by omega) ?_
    rintro b ⟨bv, bo, bp, ba, bk, bf⟩
    exact ⟨bv, bo, by rw [bp]; exact hrc, ba, bk.le, bf⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
