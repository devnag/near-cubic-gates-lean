import SourceAdapters.Proximity.TrimHonestEmit
import Proof.Gates.Cells.Idx

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": restriction may advance the retained-address cursor and
finite lookup cursors, while preserving all data and source-call channels. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

structure OutputFrame (T : List (Fin VV)) (a b : DS VV MM) : Prop where
  ram : b.ram = a.ram
  cursor : ∀ m, m ∉ scheduleStore :: lookupStores → b.rc m = a.rc m
  ip : b.ip = a.ip
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : Fr a b T

namespace OutputFrame
variable {T T' : List (Fin VV)} {a b d : DS VV MM}
theorem refl (T : List (Fin VV)) (a : DS VV MM) : OutputFrame T a a :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
theorem trans (h : OutputFrame T a b) (k : OutputFrame T b d) : OutputFrame T a d :=
  ⟨k.ram.trans h.ram, fun m hm => (k.cursor m hm).trans (h.cursor m hm),
    k.ip.trans h.ip, k.kin.trans h.kin, k.kout.trans h.kout, k.kc.trans h.kc, h.env.trans k.env⟩
theorem weaken (h : OutputFrame T a b) (ht : ∀ x ∈ T, x ∈ T') : OutputFrame T' a b :=
  ⟨h.ram, h.cursor, h.ip, h.kin, h.kout, h.kc, h.env.weaken ht⟩
theorem set (T : List (Fin VV)) (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ T) :
    OutputFrame T a (a.set x v) :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Fr.set a v hx⟩
theorem of_lookup (h : LookupFrame T a b) : OutputFrame T a b :=
  ⟨h.ram, fun m hm => h.cursor m (fun hx => hm (List.mem_cons_of_mem _ hx)),
    h.ip, h.kin, h.kout, h.kc, h.env⟩
theorem advance (T : List (Fin VV)) (a : DS VV MM) : OutputFrame T a (a.adv scheduleStore) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  intro m hm
  have hn : m ≠ scheduleStore := by intro h; apply hm; simp [h]
  simp [DS.adv, hn]
theorem constants (h : OutputFrame T a b) (hc : Cst a)
    (ht : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.env ht
end OutputFrame

theorem Ready.advance {n q N : ℕ} {C : Ctx} {V : NonadaptiveVerifier n q}
    {input : BitInput n} {proof : BitInput N} {a : DS VV MM} (h : Ready C V input proof a) :
    Ready C V input proof (a.adv scheduleStore) := by
  refine ⟨h.proof_ram, h.proof_len, ?_, h.proof_width, h.keys_ram, h.values_ram,
    h.aux_len, ?_, ?_, h.aux_width⟩
  · simpa [DS.adv, proofStore, scheduleStore] using h.proof_cursor
  · simpa [DS.adv, auxiliaryStore, scheduleStore] using h.aux_cursor
  · simpa [DS.adv, keyStore, scheduleStore] using h.key_cursor

end NearCubicGates.Adapters.Proximity.TrimHonest
