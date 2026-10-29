import SourceAdapters.Proximity.TrimHonestRowValues
import SourceAdapters.Code.PairKeys

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": accumulated auxiliary rows retain exact paired labels,
q-shifted canonical values, and paid end cursors. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

theorem auxiliary_values_length {n q : ℕ} (V : NonadaptiveVerifier n q) (input : BitInput n)
    (proof : ℕ → Bool) (rows : ℕ) :
    (auxiliaryValues V input proof rows).length = rows * blockVariableBound q := by
  simp [auxiliaryValues, auxKeys_length]

structure AuxiliaryReady {n q : ℕ} (V : NonadaptiveVerifier n q) (input : BitInput n)
    (proof : ℕ → Bool) (rows : ℕ) (a : DS VV MM) : Prop where
  keys : a.ram keyStore = auxKeys rows (blockVariableBound q)
  values : a.ram auxiliaryStore = (auxiliaryValues V input proof rows).map Bool.toNat
  key_cursor : a.rc keyStore = rows * blockVariableBound q
  value_cursor : a.rc auxiliaryStore = rows * blockVariableBound q
  length : a.env auxiliaryLength = rows * blockVariableBound q

def pairRegisters : Fin 4 ↪ Fin VV :=
  ⟨![QueryStep.rowReg, localIndex, pairScratch, pairResult], by decide⟩
def keyTemps : List (Fin VV) := [localIndex, pairScratch, pairResult, addressReg]
def valueTemps : List (Fin VV) := [localIndex, c0, vJ, addressReg, valueReg]
def appendTemps : List (Fin VV) := auxiliaryLength :: (keyTemps ++ valueTemps)

structure AppendFrame (T : List (Fin VV)) (a b : DS VV MM) : Prop where
  ram : ∀ m, m ≠ keyStore → m ≠ auxiliaryStore → b.ram m = a.ram m
  cursor : ∀ m, m ≠ keyStore → m ≠ auxiliaryStore → m ≠ rowStore → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : Fr a b T

namespace AppendFrame
variable {T T' : List (Fin VV)} {a b d : DS VV MM}
theorem trans (h : AppendFrame T a b) (k : AppendFrame T b d) : AppendFrame T a d :=
  ⟨fun m hk ha => (k.ram m hk ha).trans (h.ram m hk ha),
    fun m hk ha hr => (k.cursor m hk ha hr).trans (h.cursor m hk ha hr), k.ip.trans h.ip,
    k.out.trans h.out, k.kin.trans h.kin, k.kout.trans h.kout, k.kc.trans h.kc, h.env.trans k.env⟩
theorem weaken (h : AppendFrame T a b) (ht : ∀ x ∈ T, x ∈ T') : AppendFrame T' a b :=
  ⟨h.ram, h.cursor, h.ip, h.out, h.kin, h.kout, h.kc, h.env.weaken ht⟩
theorem set (T : List (Fin VV)) (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ T) :
    AppendFrame T a (a.set x v) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Fr.set a v hx⟩
theorem constants (h : AppendFrame T a b) (hc : Cst a)
    (ht : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.env ht
end AppendFrame

end NearCubicGates.Adapters.Proximity.TrimHonest
