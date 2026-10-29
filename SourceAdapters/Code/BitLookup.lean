import Proof.Gates.Cells.Loop
import Mathlib.Data.List.GetD

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid lookup in a stored bit word. The address is tested
against the retained length before a store cursor moves. Missing addresses
return zero in two steps, independently of their numeric value. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.BitLookup

open NearCubicGates.Close.Cells

/-- The guard precedes the paid in-range store scan. -/
def script (m : Fin MM) (x len result : Fin VV) : St VV MM :=
  .ite (.lt x len) (fetch m x result) (.op (.zero result))

/-- An absent address performs no store operation and costs exactly two. -/
theorem absent (C : Ctx) (m : Fin MM) (x len result : Fin VV)
    (hxl : x ≠ len) (a : DS VV MM) (habsent : a.env len ≤ a.env x) :
    Ex C (script m x len result) a (a.set result 0) 2 := by
  exact Ex.iteF (c := .lt x len) hxl (by simp [Cnd.eval]; omega)
    (Ex.op (OpEx.zero result a))

/-- Linear stored-length cost, with retained address, length, constants,
channels, store contents and every other store cursor. Only the three listed
scratch registers may change. No upper bound on an absent address is needed. -/
theorem runs (C : Ctx) (m : Fin MM) (x len result : Fin VV)
    (hxl : x ≠ len) (hx : x ∉ [c0, vJ, result]) (hl : len ∉ [c0, vJ, result])
    (hcst : vZ ∉ [c0, vJ, result] ∧ v1 ∉ [c0, vJ, result] ∧ v2 ∉ [c0, vJ, result])
    (a : DS VV MM) (hc : Cst a) (bits : List Bool)
    (hstore : a.ram m = bits.map Bool.toNat) (hlen : a.env len = bits.length)
    (hcursor : a.rc m ≤ bits.length) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (script m x len result) a (6 * bits.length + 10) (fun b =>
      b.env result = (bits.getD (a.env x) false).toNat ∧
      b.env x = a.env x ∧ b.env len = bits.length ∧ Cst b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ q, q ≠ m → b.rc q = a.rc q) ∧ b.rc m ≤ bits.length ∧
      Fr a b [c0, vJ, result]) := by
  by_cases h : a.env x < bits.length
  · have hx0 : x ≠ c0 := by intro he; apply hx; simp [he]
    have hxJ : x ≠ vJ := by intro he; apply hx; simp [he]
    have hf := fetch_spec (C := C) m x result hx0 hxJ a
      (by simpa only [hstore, List.length_map] using h) (lt_trans h hwidth)
    have ht := Hs.iteT (c := .lt x len) (u := .op (.zero result)) hxl
      (by simp [Cnd.eval, hlen, h]) hf
    refine Hs.mono ht (by omega) ?_
    rintro b ⟨hr, hi, ho, hm, hrc, hki, hko, hkc, hfr⟩
    refine ⟨?_, hfr x hx, (hfr len hl).trans hlen, Cst.of_fr hc hfr hcst,
      hi, ho, hm, hki, hko, hkc, ?_, ?_, hfr⟩
    · rw [hr, hstore]
      exact List.getD_map bits false Bool.toNat
    · intro q hq
      rw [hrc, Function.update_of_ne hq]
    · rw [hrc, Function.update_self]
      omega
  · have hd : bits.getD (a.env x) false = false := List.getD_eq_default bits false (by omega)
    have hfr : Fr a (a.set result 0) [c0, vJ, result] := Fr.set a 0 (by simp)
    refine ⟨a.set result 0, 2, absent C m x len result hxl a (by omega), by omega,
      ?_, hfr x hx, (hfr len hl).trans hlen, Cst.of_fr hc hfr hcst,
      rfl, rfl, rfl, rfl, rfl, rfl, ?_, hcursor, hfr⟩
    · rw [DS.set_env_self, hd]
      rfl
    · intro q _
      rfl

end NearCubicGates.Adapters.Code.BitLookup
