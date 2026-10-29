import SourceAdapters.Proximity.TrimHonestChoice

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the actual finite proof stores used by restriction. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

structure Ready {n q N : ℕ} (C : Ctx) (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) (a : DS VV MM) : Prop where
  proof_ram : a.ram proofStore = (List.ofFn proof).map Bool.toNat
  proof_len : a.env proofLength = N
  proof_cursor : a.rc proofStore ≤ N
  proof_width : N < 2 ^ C.Wd
  keys_ram : a.ram keyStore = auxKeys (2 ^ V.randomBits) (blockVariableBound q)
  values_ram : a.ram auxiliaryStore = (auxValues V input (finiteProofOracle proof)).map Bool.toNat
  aux_len : a.env auxiliaryLength = (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length
  aux_cursor : a.rc auxiliaryStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length
  key_cursor : a.rc keyStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length
  aux_width : (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length < 2 ^ C.Wd

namespace Ready
variable {n q N : ℕ} {C : Ctx} {V : NonadaptiveVerifier n q}
    {input : BitInput n} {proof : BitInput N} {a b : DS VV MM}

theorem set (h : Ready C V input proof a) (reg : Fin VV) (value : ℕ)
    (hp : proofLength ≠ reg) (ha : auxiliaryLength ≠ reg) :
    Ready C V input proof (a.set reg value) := by
  refine ⟨h.proof_ram, ?_, h.proof_cursor, h.proof_width, h.keys_ram, h.values_ram,
    ?_, h.aux_cursor, h.key_cursor, h.aux_width⟩
  · simpa [DS.set, hp] using h.proof_len
  · simpa [DS.set, ha] using h.aux_len

theorem frame (h : Ready C V input proof a) {T : List (Fin VV)}
    (f : LookupFrame T a b) (hp : proofLength ∉ T) (ha : auxiliaryLength ∉ T)
    (bp : b.rc proofStore ≤ N)
    (ba : b.rc auxiliaryStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length)
    (bk : b.rc keyStore ≤ (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length) :
    Ready C V input proof b := by
  exact ⟨by rw [f.ram]; exact h.proof_ram, (f.env _ hp).trans h.proof_len, bp, h.proof_width,
    by rw [f.ram]; exact h.keys_ram, by rw [f.ram]; exact h.values_ram,
    (f.env _ ha).trans h.aux_len, ba, bk, h.aux_width⟩

end Ready
end NearCubicGates.Adapters.Proximity.TrimHonest
