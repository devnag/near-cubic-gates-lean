import Proof.Gates.Cells.Loop
import Mathlib.Data.List.GetD

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": paid two-record lookup in the fixed-query store.
The callee output and its parsing cursor remain intact while the saved query
address is fetched for translation of a local block literal. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.QueryLookup

open NearCubicGates.Close.Cells

def fetchPair (m : Fin MM) (index kind address : Fin VV) : St VV MM :=
  .seq (fetch m index kind) (.op (.rdM m address))

theorem fetch_pair (C : Ctx) (m : Fin MM) (index kind address : Fin VV)
    (hi0 : index ≠ c0) (hiJ : index ≠ vJ) (hka : kind ≠ address)
    (a : DS VV MM) (pre tail : List ℕ) (tag value : ℕ)
    (hstore : a.ram m = pre ++ tag :: value :: tail)
    (hindex : a.env index = pre.length) (hwidth : pre.length < 2 ^ C.Wd) :
    Hs C (fetchPair m index kind address) a (a.rc m + 5 * pre.length + 11) (fun b =>
      b.env kind = tag ∧ b.env address = value ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc m (pre.length + 2) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ, kind, address]) := by
  have ex := fetch_spec (C := C) m index kind hi0 hiJ a
    (by rw [hindex, hstore]; simp) (by rw [hindex]; exact hwidth)
  rw [hindex] at ex
  obtain ⟨b, cost, he, hcost, hb⟩ := ex
  rcases hb with ⟨hk, hip, ho, hm, hrc, hki, hko, hkc, hf⟩
  have htag : b.env kind = tag := by rw [hk, hstore]; simp
  have hread : (b.ram m).getD (b.rc m) 0 = value := by
    rw [hm, hrc, Function.update_self, hstore]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have e2 := Ex.op (OpEx.rdM (C := C) m address b (by
    rw [hm, hrc, Function.update_self, hstore]
    simp))
  rw [hread] at e2
  refine ⟨_, cost + 1 + 1, Ex.seq he e2, by omega, ?_⟩
  refine ⟨?_, by simp [DS.adv], hip, ho, hm, ?_, hki, hko, hkc, ?_⟩
  · change (b.set address value).env kind = tag
    rw [DS.set_env_ne _ _ hka, htag]
  · simp [DS.adv, hrc, Nat.add_assoc]
  · intro x hx
    have hxa : x ≠ address := fun h => hx (by simp [h])
    have hxold : x ∉ [c0, vJ, kind] := fun h => hx (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    change (b.set address value).env x = a.env x
    rw [DS.set_env_ne _ _ hxa, hf x hxold]

end NearCubicGates.Adapters.Proximity.QueryLookup
