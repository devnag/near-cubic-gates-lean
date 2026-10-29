import SourceAdapters.Code.OutputCounting
import Proof.Gates.Cells.Loop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": load a raw callee-output word into a bit store using its
retained length. The count, including trailing false bits, controls the loop. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CountedBitLoading

open NearCubicGates.Close.Cells

def body (m : Fin MM) : St VV MM := .seq (.op (.rdK vJ)) (.op (.wrM m vJ))

def script (m : Fin MM) (len : Fin VV) : St VV MM := forS c0 len (body m)

/-- Actual counted loading with exact raw length and only two scratch registers. -/
theorem runs (C : Ctx) (m : Fin MM) (len : Fin VV) (hl0 : len ≠ c0) (hlj : len ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool)
    (hin : a.kout = bits) (hkc : a.kc = 0) (hlen : a.env len = bits.length)
    (hempty : a.ram m = []) (hcursor : a.rc m = 0) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (script m len) a (7 * bits.length + 4) (fun b =>
      b.ram m = bits.map Bool.toNat ∧ b.env len = bits.length ∧ b.rc m = bits.length ∧
      b.kc = bits.length ∧ Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧
      (∀ q, q ≠ m → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧ Fr a b [c0, vJ]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = a.ip ∧ b.out = a.out ∧ b.ram = Function.update a.ram m ((bits.take k).map Bool.toNat) ∧
    b.rc = Function.update a.rc m k ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = k ∧ Fr a b [c0, vJ]
  have hr0 : Function.update a.ram m [] = a.ram := by
    funext q
    by_cases hq : q = m
    · subst q; simpa using hempty.symm
    · simp [hq]
  have hc0 : Function.update a.rc m 0 = a.rc := by
    funext q
    by_cases hq : q = m
    · subst q; simpa using hcursor.symm
    · simp [hq]
  have loopRun := forS_spec' (C := C) c0 len (Ne.symm hl0) (body m) a bits.length hwidth I 3
    (fun k b value ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ =>
      ⟨bi, bo, bm, brc, bki, bko, bkc, bf.trans (Fr.set b value (by simp))⟩)
    ⟨rfl, rfl, by simpa using hr0.symm, hc0.symm, rfl, rfl, hkc, Fr.refl _ _⟩ hlen ?_
  · refine Hs.mono loopRun (by omega) ?_
    rintro b ⟨⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩, _, blen⟩
    refine ⟨?_, blen, ?_, bkc, Cst.of_fr hc bf (by decide), bi, bo, bki, bko, ?_, bf⟩
    · rw [bm, Function.update_self]
      simp
    · rw [brc, Function.update_self]
    · intro q hq
      rw [bm, brc, Function.update_of_ne hq, Function.update_of_ne hq]
      exact ⟨rfl, rfl⟩
  · intro k hk b ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ bindex blen
    have er := OutputCounting.read_bit C vJ b bits[k]
      (by rw [bkc, bko, hin]; exact hk)
      (by rw [bkc, bko, hin]; exact List.getD_eq_getElem bits false hk)
    let d := OutputCounting.readState vJ b bits[k]
    have ew : Ex C (.op (.wrM m vJ)) d (d.put m bits[k].toNat) 1 := by
      have e := OpEx.wrM (C := C) m vJ d (by
        change b.rc m ≤ (b.ram m).length
        rw [brc, bm, Function.update_self, Function.update_self]
        simp [List.length_take, Nat.min_eq_left hk.le])
      simpa [d, OutputCounting.readState] using Ex.op e
    have htake : bits.take (k + 1) = bits.take k ++ [bits[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    refine ⟨d.put m bits[k].toNat, 3, Ex.seq er ew, le_rfl, ?_, ?_, ?_⟩
    · refine ⟨bi, bo, ?_, ?_, bki, bko, ?_, ?_⟩
      · funext q
        by_cases hq : q = m
        · subst q
          simp only [DS.put, Function.update_self]
          change putAt (b.ram m) (b.rc m) bits[k].toNat = (bits.take (k + 1)).map Bool.toNat
          rw [bm, brc, Function.update_self, Function.update_self, htake, List.map_append]
          simp [putAt, List.length_take, Nat.min_eq_left hk.le]
        · simp [d, OutputCounting.readState, DS.put, bm, hq]
      · funext q
        by_cases hq : q = m
        · subst q; simp [d, OutputCounting.readState, DS.put, brc]
        · simp [d, OutputCounting.readState, DS.put, brc, hq]
      · simpa [d, OutputCounting.readState, DS.put] using bkc
      · exact bf.trans (Fr.set b _ (by simp))
    · change (b.set vJ bits[k].toNat).env c0 = k
      rw [DS.set_env_ne _ _ (by decide : c0 ≠ vJ), bindex]
    · change (b.set vJ bits[k].toNat).env len = bits.length
      rw [DS.set_env_ne _ _ hlj, blen]

end NearCubicGates.Adapters.Code.CountedBitLoading
