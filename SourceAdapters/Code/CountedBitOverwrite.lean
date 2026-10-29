import SourceAdapters.Code.CountedBitLoading
import Proof.Gates.Cells.Blk

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": overwrite a reusable store from an exact raw callee word.
The previous store is no longer than the new word, so no stale tail remains. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CountedBitOverwrite

open NearCubicGates.Close.Cells

/-- The existing counted reader overwrites an arbitrary old store of bounded length. -/
theorem runs (C : Ctx) (m : Fin MM) (len : Fin VV) (hl0 : len ≠ c0) (hlj : len ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool) (old : List ℕ)
    (hin : a.kout = bits) (hkc : a.kc = 0) (hlen : a.env len = bits.length)
    (hstore : a.ram m = old) (hold : old.length ≤ bits.length)
    (hcursor : a.rc m = 0) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (CountedBitLoading.script m len) a (7 * bits.length + 4) (fun b =>
      b.ram m = bits.map Bool.toNat ∧ b.env len = bits.length ∧ b.rc m = bits.length ∧
      b.kc = bits.length ∧ Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧
      (∀ q, q ≠ m → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧ Fr a b [c0, vJ]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = a.ip ∧ b.out = a.out ∧ b.ram = Function.update a.ram m ((bits.map Bool.toNat).take k ++ old.drop k) ∧
    b.rc = Function.update a.rc m k ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = k ∧ Fr a b [c0, vJ]
  have hr0 : Function.update a.ram m old = a.ram := by
    funext q
    by_cases hq : q = m
    · subst q; simpa using hstore.symm
    · simp [hq]
  have hc0 : Function.update a.rc m 0 = a.rc := by
    funext q
    by_cases hq : q = m
    · subst q; simpa using hcursor.symm
    · simp [hq]
  have loopRun := forS_spec' (C := C) c0 len (Ne.symm hl0) (CountedBitLoading.body m) a bits.length hwidth I 3
    (fun k b value ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ =>
      ⟨bi, bo, bm, brc, bki, bko, bkc, bf.trans (Fr.set b value (by simp))⟩)
    ⟨rfl, rfl, by simpa using hr0.symm, hc0.symm, rfl, rfl, hkc, Fr.refl _ _⟩ hlen ?_
  · refine Hs.mono loopRun (by omega) ?_
    rintro b ⟨⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩, _, blen⟩
    refine ⟨?_, blen, ?_, bkc, Cst.of_fr hc bf (by decide), bi, bo, bki, bko, ?_, bf⟩
    · rw [bm, Function.update_self]
      simp [List.drop_eq_nil_iff.mpr hold]
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
    refine ⟨d.put m bits[k].toNat, 3, Ex.seq er ew, le_rfl, ?_, ?_, ?_⟩
    · refine ⟨bi, bo, ?_, ?_, bki, bko, ?_, ?_⟩
      · funext q
        by_cases hq : q = m
        · subst q
          simp only [DS.put, Function.update_self]
          change putAt (b.ram m) (b.rc m) bits[k].toNat =
            (bits.map Bool.toNat).take (k + 1) ++ old.drop (k + 1)
          rw [bm, brc, Function.update_self, Function.update_self]
          simp only [← List.map_take]
          have hp := putAt_split ((bits.take k).map Bool.toNat) (old.drop k) bits[k].toNat
          have hpLen : ((bits.take k).map Bool.toNat).length = k := by simp; omega
          rw [hpLen] at hp
          have ht : bits.take (k + 1) = bits.take k ++ [bits[k]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hk]
            rfl
          rw [hp, ht, List.map_append, List.drop_drop]
          simp [List.append_assoc]
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

def rewindScript (m : Fin MM) (len : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (CountedBitLoading.script m len)

/-- Reuse a store at any cursor position, paying for the actual rewind. -/
theorem rewind_runs (C : Ctx) (m : Fin MM) (len : Fin VV) (hl0 : len ≠ c0) (hlj : len ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool) (old : List ℕ)
    (hin : a.kout = bits) (hkc : a.kc = 0) (hlen : a.env len = bits.length)
    (hstore : a.ram m = old) (hold : old.length ≤ bits.length) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (rewindScript m len) a (a.rc m + 7 * bits.length + 6) (fun b =>
      b.ram m = bits.map Bool.toNat ∧ b.env len = bits.length ∧ b.rc m = bits.length ∧
      b.kc = bits.length ∧ Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧
      (∀ q, q ≠ m → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧ Fr a b [c0, vJ]) := by
  have loader := runs C m len hl0 hlj (a.rew m)
    (Cst.of_fr hc (show Fr a (a.rew m) [] from Fr.refl _ _) (by simp)) bits old hin hkc hlen hstore hold
    (by simp [DS.rew]) hwidth
  have allRun := Hs.seq (hs_rwM C m a) (fun b hb => by subst b; exact loader)
  refine Hs.mono allRun (by omega) ?_
  rintro b ⟨bm, bl, br, bk, bc, bi, bo, bki, bko, bother, bf⟩
  refine ⟨bm, bl, br, bk, bc, bi, bo, bki, bko, ?_, bf⟩
  intro q hq
  simpa [DS.rew, hq] using bother q hq

end NearCubicGates.Adapters.Code.CountedBitOverwrite
