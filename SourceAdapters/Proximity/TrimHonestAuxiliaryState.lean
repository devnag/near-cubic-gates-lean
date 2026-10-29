import SourceAdapters.Proximity.TrimHonestAppend
import SourceAdapters.Proximity.TrimHonestOutput

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact initial, preserved and complete auxiliary states
connect actual row construction to the checked final restriction program. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

namespace AuxiliaryReady
variable {n q : ℕ} {V : NonadaptiveVerifier n q} {input : BitInput n}
    {proof : ℕ → Bool} {rows : ℕ} {a b : DS VV MM}

theorem set (h : AuxiliaryReady V input proof rows a) (reg : Fin VV) (value : ℕ)
    (hr : auxiliaryLength ≠ reg) : AuxiliaryReady V input proof rows (a.set reg value) :=
  ⟨h.keys, h.values, h.key_cursor, h.value_cursor, by simpa [DS.set, hr] using h.length⟩

theorem preserved (h : AuxiliaryReady V input proof rows a)
    (hk : b.ram keyStore = a.ram keyStore) (hv : b.ram auxiliaryStore = a.ram auxiliaryStore)
    (hkc : b.rc keyStore = a.rc keyStore) (hvc : b.rc auxiliaryStore = a.rc auxiliaryStore)
    (hlen : b.env auxiliaryLength = a.env auxiliaryLength) : AuxiliaryReady V input proof rows b :=
  ⟨hk.trans h.keys, hv.trans h.values, hkc.trans h.key_cursor, hvc.trans h.value_cursor, hlen.trans h.length⟩

theorem zero (V : NonadaptiveVerifier n q) (input : BitInput n) (proof : ℕ → Bool) (a : DS VV MM)
    (hk : a.ram keyStore = []) (hv : a.ram auxiliaryStore = [])
    (hkc : a.rc keyStore = 0) (hvc : a.rc auxiliaryStore = 0) (hlen : a.env auxiliaryLength = 0) :
    AuxiliaryReady V input proof 0 a := by
  exact ⟨by simpa using hk, by simpa [auxiliaryValues] using hv,
    by simpa using hkc, by simpa using hvc, by simpa using hlen⟩

theorem complete {N : ℕ} {C : Ctx} {proof : BitInput N}
    (h : AuxiliaryReady V input (finiteProofOracle proof) (2 ^ V.randomBits) a)
    (horacle : OracleReady C input proof a)
    (hwidth : 2 ^ V.randomBits * blockVariableBound q < 2 ^ C.Wd) : Ready C V input proof a := by
  refine ⟨horacle.proof_ram, horacle.proof_len, horacle.proof_cursor, horacle.proof_width,
    h.keys, h.values, ?_, ?_, ?_, ?_⟩
  · simpa only [auxKeys_length] using h.length
  · simpa only [auxKeys_length] using h.value_cursor.le
  · simpa only [auxKeys_length] using h.key_cursor.le
  · simpa only [auxKeys_length] using hwidth
end AuxiliaryReady

theorem OracleReady.of_append {n N : ℕ} {C : Ctx} {input : BitInput n} {proof : BitInput N}
    {a b : DS VV MM} {T : List (Fin VV)} (h : OracleReady C input proof a)
    (f : AppendFrame T a b) (hi : inputLength ∉ T) (hp : proofLength ∉ T) :
    OracleReady C input proof b := by
  refine ⟨(f.ram inputStore (by decide) (by decide)).trans h.input_ram,
    (f.env inputLength hi).trans h.input_len, ?_, h.input_width,
    (f.ram proofStore (by decide) (by decide)).trans h.proof_ram,
    (f.env proofLength hp).trans h.proof_len, ?_, h.proof_width⟩
  · rw [f.cursor inputStore (by decide) (by decide) (by decide)]
    exact h.input_cursor
  · rw [f.cursor proofStore (by decide) (by decide) (by decide)]
    exact h.proof_cursor

end NearCubicGates.Adapters.Proximity.TrimHonest
