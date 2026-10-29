import SourceAdapters.Proximity.TrimHonestReady

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid address arithmetic followed by exact proof lookup. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def addressTemps : List (Fin VV) := [halfReg, evenReg] ++ lookupTemps
def lookupAddress : St VV MM := .seq splitAddress chooseLookup

theorem lookup_address {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) (a : DS VV MM) (hc : Cst a)
    (ready : Ready C V input proof a) (hwidth : a.env addressReg < 2 ^ C.Wd) :
    Hs C lookupAddress a
      (6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 29)
      (fun b => b.env valueReg =
          (canonicalClauseProof V input (finiteProofOracle proof) (a.env addressReg)).toNat ∧
        b.out = a.out ∧ Ready C V input proof b ∧ LookupFrame addressTemps a b) := by
  let b := (a.set halfReg (a.env addressReg / 2)).set evenReg (2 * (a.env addressReg / 2))
  have e1 := split_address (C := C) a (a.env addressReg) rfl hwidth
  have fb : LookupFrame addressTemps a b :=
    (LookupFrame.set addressTemps a halfReg _ (by simp [addressTemps])).trans
      (LookupFrame.set addressTemps _ evenReg _ (by simp [addressTemps]))
  have rb : Ready C V input proof b :=
    (ready.set halfReg _ (by decide) (by decide)).set evenReg _ (by decide) (by decide)
  have ba : b.env addressReg = a.env addressReg := fb.env _ (by decide)
  have bh : b.env halfReg = b.env addressReg / 2 := by
    rw [ba]
    simp [b, DS.set, halfReg, evenReg]
  have be : b.env evenReg = 2 * (b.env addressReg / 2) := by rw [ba]; simp [b]
  obtain ⟨d, cost, e2, hcost, dv, dout, dp, da, dk, fd⟩ :=
    choose_lookup (C := C) V input proof b (fb.constants hc (by decide))
      rb.proof_ram rb.proof_len rb.proof_cursor rb.proof_width rb.keys_ram rb.values_ram
      rb.aux_len rb.aux_cursor rb.key_cursor rb.aux_width bh be
  have rd := rb.frame fd (by decide) (by decide) dp da dk
  refine ⟨d, 7 + cost + 1, Ex.seq e1 e2, by omega, ?_⟩
  exact ⟨by simpa only [ba] using dv, dout, rd,
    fb.trans (fd.weaken (fun _ hx => List.mem_append_right _ hx))⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
