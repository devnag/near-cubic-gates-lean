import SourceAdapters.Code.BitLoading
import SourceAdapters.Code.BitLookup
import NineInputs

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": source honest output is loaded and retained with its
exact finite length, including trailing zeros. Lookup first compares addresses
with that length, so missing large addresses never cause a large tape scan. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestLoading

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity

def callLoad (m : Fin MM) (len : Fin VV) : St VV MM :=
  .seq (.op .kcall) (BitLoading.script m len)

theorem call_load (C : Ctx) (m : Fin MM) (len : Fin VV)
    (hlj : len ≠ vJ) (hlc : len ∉ [vZ, v1, v2]) (request : C.K.Req)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool)
    (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = frame bits) (hempty : a.ram m = [])
    (hcursor : a.rc m = 0) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (callLoad m len) a (C.Lk + C.Bk + 9 * bits.length + 8) (fun b =>
      b.ram m = bits.map Bool.toNat ∧ b.env len = bits.length ∧ b.rc m = bits.length ∧
      b.kc = (frame bits).length ∧ Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.kin = [] ∧ b.kout = frame bits ∧
      (∀ q, q ≠ m → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧ Fr a b [vJ, len]) := by
  have e1 := Ex.op (OpEx.kcall request a hin hbudget)
  rw [hout] at e1
  have e2 := BitLoading.spec C m len hlj hlc (a.called (frame bits)) ⟨hc.z, hc.one, hc.two⟩ bits rfl rfl hempty hcursor hwidth
  obtain ⟨b, cost, he, hcost, hb⟩ := e2
  exact ⟨b, 1 + C.Lk + C.Bk + cost + 1, Ex.seq e1 he, by omega, hb⟩

theorem ofFn_getD {n : ℕ} (proof : BitInput n) (address : ℕ) :
    (List.ofFn proof).getD address false = finiteProofOracle proof address := by
  by_cases h : address < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    simp [finiteProofOracle, h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
    simp [finiteProofOracle, h]

theorem finite_lookup (C : Ctx) (m : Fin MM) (x len result : Fin VV)
    (hxl : x ≠ len) (hx : x ∉ [c0, vJ, result]) (hl : len ∉ [c0, vJ, result])
    (hcst : vZ ∉ [c0, vJ, result] ∧ v1 ∉ [c0, vJ, result] ∧ v2 ∉ [c0, vJ, result])
    (a : DS VV MM) (hc : Cst a) {n : ℕ} (proof : BitInput n)
    (hstore : a.ram m = (List.ofFn proof).map Bool.toNat) (hlen : a.env len = n)
    (hcursor : a.rc m ≤ n) (hwidth : n < 2 ^ C.Wd) :
    Hs C (BitLookup.script m x len result) a (6 * n + 10) (fun b =>
      b.env result = (finiteProofOracle proof (a.env x)).toNat ∧
      b.env x = a.env x ∧ b.env len = n ∧ Cst b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ q, q ≠ m → b.rc q = a.rc q) ∧ b.rc m ≤ n ∧ Fr a b [c0, vJ, result]) := by
  simpa only [List.length_ofFn, ofFn_getD] using BitLookup.runs C m x len result hxl hx hl hcst a hc
    (List.ofFn proof) hstore (by simpa using hlen) (by simpa using hcursor) (by simpa using hwidth)

end NearCubicGates.Adapters.Proximity.HonestLoading
