import SourceAdapters.Proximity.AuxiliaryCase
import SourceAdapters.Proximity.RowLookup

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the complete paid local-address
translation. It uses the saved padded-query row for original variables and
the odd paired namespace for auxiliaries, preserving the block-output cursor. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.AddressTranslation

open NearCubicWires NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (resultReg)
open QueryStep (rowReg boundReg paddedAddress)
open OriginalAddress (kindReg addressReg)

def translatedAddress {N : ℕ} (addresses : Fin N → Bool × ℕ) (row q localIndex : ℕ) : Bool × ℕ :=
  if localIndex < q then
    let a := paddedAddress addresses localIndex
    (a.1, if a.1 then 2 * a.2 else a.2)
  else (true, 2 * Nat.pair row (localIndex - q) + 1)

def scratch : List (Fin VV) := OriginalAddress.scratch ++ AuxiliaryCase.scratch

def translate (m : Fin MM) : Script :=
  .ite (.lt resultReg boundReg) (OriginalAddress.originalProgram m) AuxiliaryCase.auxiliaryCase

structure Translated (m : Fin MM) (q : ℕ) (a b : State) (value : Bool × ℕ) : Prop where
  kind_eq : b.env kindReg = value.1.toNat
  address_eq : b.env addressReg = value.2
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  ram_eq : b.ram = a.ram
  kin_eq : b.kin = a.kin
  kout_eq : b.kout = a.kout
  kc_eq : b.kc = a.kc
  other_cursor : ∀ s, s ≠ m → b.rc s = a.rc s
  cursor_bound : b.rc m ≤ 2 * q
  vars : Fr a b scratch

theorem translate_address (C : Ctx) (m : Fin MM) {N : ℕ} (addresses : Fin N → Bool × ℕ)
    (row q localIndex : ℕ) (a : State) (hc : Cst a)
    (hrow : a.env rowReg = row) (hq : a.env boundReg = q) (hi : a.env resultReg = localIndex)
    (hstore : a.ram m = QueryRows.rowFields addresses q) (hcursor : a.rc m ≤ 2 * q)
    (hpositions : 2 * q ≤ 2 ^ C.Wd)
    (hsource : ∀ j < q, 2 * (paddedAddress addresses j).2 < 2 ^ C.Wd)
    (haux : 2 * Nat.pair row (localIndex - q) + 1 < 2 ^ C.Wd) :
    Hs C (translate m) a (12 * q + 20)
      (fun b => Translated m q a b (translatedAddress addresses row q localIndex)) := by
  by_cases hj : localIndex < q
  · obtain ⟨tail, htail⟩ := QueryRows.rowFields_split addresses q localIndex hj
    have e := OriginalAddress.original_program C m a hc localIndex (paddedAddress addresses localIndex).2
      (paddedAddress addresses localIndex).1 (QueryRows.rowFields addresses localIndex) tail hi
      (QueryRows.rowFields_length _ _) (hstore.trans htail) (by omega) (hsource localIndex hj)
    obtain ⟨b, cost, he, hcost, hb⟩ := e
    rcases hb with ⟨hk, ha, hip, ho, hm, hrc, hki, hko, hkc, hf⟩
    refine ⟨b, cost + 1, Ex.iteT (c := Cnd.lt resultReg boundReg) (by decide : resultReg ≠ boundReg)
      (by simp [Cnd.eval, hi, hq, hj]) he, by omega, ?_⟩
    refine ⟨by simpa [translatedAddress, hj] using hk, by simpa [translatedAddress, hj] using ha,
      hip, ho, hm, hki, hko, hkc, ?_, ?_, hf.weaken (fun _ h => List.mem_append_left _ h)⟩
    · intro s hs
      rw [hrc, Function.update_of_ne hs]
    · rw [hrc, Function.update_self]
      omega
  · have e := AuxiliaryCase.auxiliary_case C a hc row localIndex q hrow hi hq (Nat.le_of_not_gt hj) haux
    obtain ⟨b, cost, he, hcost, hb⟩ := e
    rcases hb with ⟨hk, ha, hs, hf⟩
    refine ⟨b, cost + 1, Ex.iteF (c := Cnd.lt resultReg boundReg) (by decide : resultReg ≠ boundReg)
      (by simp [Cnd.eval, hi, hq, hj]) he, by omega, ?_⟩
    exact ⟨by simpa [translatedAddress, hj] using hk, by simpa [translatedAddress, hj] using ha,
      hs.ip, hs.out, hs.ram, hs.kin, hs.kout, hs.kc,
      fun _ _ => congrFun hs.rc _, by rw [hs.rc]; exact hcursor,
      hf.weaken (fun _ h => List.mem_append_right _ h)⟩

end NearCubicGates.Adapters.Proximity.AddressTranslation
