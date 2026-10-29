import SourceAdapters.Proximity.TrimPrepare
import SourceAdapters.Proximity.TrimOutputData
import SourceAdapters.Code.RecordLookup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": preservation for the exact verifier-word serializer.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells

def rankReg : Fin VV := 52
def signReg : Fin VV := 53
def codeReg : Fin VV := 54
def renderIndex : Fin VV := 55

structure RenderFrame (T : List (Fin VV)) (a b : DS VV MM) : Prop where
  ram : b.ram = a.ram
  otherCursor : ∀ m, m ≠ sN → m ≠ distinctStore → b.rc m = a.rc m
  ip : b.ip = a.ip
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : Fr a b T

namespace RenderFrame
variable {T T' : List (Fin VV)} {a b d : DS VV MM}

theorem refl (T : List (Fin VV)) (a : DS VV MM) : RenderFrame T a a :=
  ⟨rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩

theorem trans (h : RenderFrame T a b) (k : RenderFrame T b d) : RenderFrame T a d :=
  ⟨k.ram.trans h.ram, fun m hq hd => (k.otherCursor m hq hd).trans (h.otherCursor m hq hd),
    k.ip.trans h.ip, k.kin.trans h.kin, k.kout.trans h.kout, k.kc.trans h.kc, h.env.trans k.env⟩

theorem weaken (h : RenderFrame T a b) (hT : ∀ x ∈ T, x ∈ T') : RenderFrame T' a b :=
  ⟨h.ram, h.otherCursor, h.ip, h.kin, h.kout, h.kc, h.env.weaken hT⟩

theorem set (T : List (Fin VV)) (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ T) :
    RenderFrame T a (a.set x v) :=
  ⟨rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, Fr.set a v hx⟩

theorem afterRead (T : List (Fin VV)) (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ T) :
    RenderFrame T a (Trim.afterRead a x v) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, Fr.set a v hx⟩
  intro m hm _
  simp [Trim.afterRead, DS.adv, hm]

theorem constants (h : RenderFrame T a b) (hc : Cst a)
    (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.env hT

end RenderFrame
end NearCubicGates.Adapters.Proximity.Trim
