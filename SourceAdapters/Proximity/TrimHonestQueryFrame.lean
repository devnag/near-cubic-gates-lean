import SourceAdapters.Proximity.TrimHonestQueryLookup
import Proof.Gates.Cells.Idx

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": evaluating source queries changes only the answer store,
the query/input/proof cursors, and explicitly listed scratch registers. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def queryCursors : List (Fin MM) := [queryStore, inputStore, proofStore, answerStore]
structure QueryFrame (T : List (Fin VV)) (a b : DS VV MM) : Prop where
  ram : ∀ m, m ≠ answerStore → b.ram m = a.ram m
  cursor : ∀ m, m ∉ queryCursors → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : Fr a b T

namespace QueryFrame
variable {T T' : List (Fin VV)} {a b d : DS VV MM}
theorem refl (T : List (Fin VV)) (a : DS VV MM) : QueryFrame T a a :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
theorem trans (h : QueryFrame T a b) (k : QueryFrame T b d) : QueryFrame T a d :=
  ⟨fun m hm => (k.ram m hm).trans (h.ram m hm),
    fun m hm => (k.cursor m hm).trans (h.cursor m hm), k.ip.trans h.ip, k.out.trans h.out,
    k.kin.trans h.kin, k.kout.trans h.kout, k.kc.trans h.kc, h.env.trans k.env⟩
theorem weaken (h : QueryFrame T a b) (ht : ∀ x ∈ T, x ∈ T') : QueryFrame T' a b :=
  ⟨h.ram, h.cursor, h.ip, h.out, h.kin, h.kout, h.kc, h.env.weaken ht⟩
theorem set (T : List (Fin VV)) (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ T) :
    QueryFrame T a (a.set x v) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Fr.set a v hx⟩
theorem advance (T : List (Fin VV)) (a : DS VV MM) : QueryFrame T a (a.adv queryStore) := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  intro m hm
  have hn : m ≠ queryStore := by intro h; apply hm; simp [queryCursors, h]
  simp [DS.adv, hn]
theorem put (T : List (Fin VV)) (a : DS VV MM) (v : ℕ) :
    QueryFrame T a (a.put answerStore v) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  · intro m hm; simp [DS.put, hm]
  · intro m hm
    have hn : m ≠ answerStore := by intro h; apply hm; simp [queryCursors, h]
    simp [DS.put, hn]
theorem constants (h : QueryFrame T a b) (hc : Cst a)
    (ht : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.env ht
theorem of_lookup (h : LookupFrame T a b) (ho : b.out = a.out)
    (hc : ∀ m, m ≠ inputStore → m ≠ proofStore → b.rc m = a.rc m) : QueryFrame T a b := by
  refine ⟨fun m _ => congrFun h.ram m, ?_, h.ip, ho, h.kin, h.kout, h.kc, h.env⟩
  intro m hm
  exact hc m (by intro he; apply hm; simp [queryCursors, he])
    (by intro he; apply hm; simp [queryCursors, he])
end QueryFrame

end NearCubicGates.Adapters.Proximity.TrimHonest
