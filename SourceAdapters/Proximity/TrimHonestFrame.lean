import SourceAdapters.Proximity.TrimHonestRegisters

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": lookup preserves all stored source/input/auxiliary data.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicGates.Close.Cells

def lookupStores : List (Fin MM) := [proofStore, inputStore, auxiliaryStore, keyStore]

structure LookupFrame (T : List (Fin VV)) (a b : DS VV MM) : Prop where
  ram : b.ram = a.ram
  cursor : ∀ m, m ∉ lookupStores → b.rc m = a.rc m
  ip : b.ip = a.ip
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : Fr a b T

namespace LookupFrame
variable {T T' : List (Fin VV)} {a b d : DS VV MM}

theorem refl (T : List (Fin VV)) (a : DS VV MM) : LookupFrame T a a :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
theorem trans (h : LookupFrame T a b) (k : LookupFrame T b d) : LookupFrame T a d :=
  ⟨k.ram.trans h.ram, fun m hm => (k.cursor m hm).trans (h.cursor m hm),
    k.ip.trans h.ip, k.kin.trans h.kin, k.kout.trans h.kout, k.kc.trans h.kc, h.env.trans k.env⟩
theorem weaken (h : LookupFrame T a b) (ht : ∀ x ∈ T, x ∈ T') : LookupFrame T' a b :=
  ⟨h.ram, h.cursor, h.ip, h.kin, h.kout, h.kc, h.env.weaken ht⟩
theorem set (T : List (Fin VV)) (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ T) :
    LookupFrame T a (a.set x v) :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Fr.set a v hx⟩
theorem constants (h : LookupFrame T a b) (hc : Cst a)
    (ht : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.env ht

end LookupFrame
end NearCubicGates.Adapters.Proximity.TrimHonest
