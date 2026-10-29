import SourceAdapters.Code.CellSending
import Proof.Gates.Cells.Loop
import Mathlib.Data.List.GetD

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid raw-bit printing from a record store to ordinary output.
The source cursor is rewound, then exactly the retained bit count is sent. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.TriplePreparationBits
open NearCubicGates.Close.Cells
open CellSending

def body (m : Fin MM) : St VV MM :=
  .seq (.op (.rdM m vJ)) (sendReadBit vZ vJ false)

def script (m : Fin MM) (len : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (forS c0 len (body m))

theorem runs (C : Ctx) (m : Fin MM) (len : Fin VV) (hl0 : len ≠ c0) (hlj : len ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool)
    (hstore : a.ram m = bits.map Bool.toNat) (hlen : a.env len = bits.length)
    (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (script m len) a (a.rc m + 8 * bits.length + 6) (fun b =>
      b.out = a.out ++ bits ∧ b.env len = bits.length ∧ Cst b ∧
      b.ip = a.ip ∧ b.kin = a.kin ∧ b.ram = a.ram ∧ b.rc m = bits.length ∧
      (∀ q, q ≠ m → b.rc q = a.rc q) ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = a.ip ∧ b.kin = a.kin ∧ b.ram = a.ram ∧ b.rc = Function.update a.rc m k ∧
    b.out = a.out ++ bits.take k ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ]
  have loopRun := forS_spec' (C := C) c0 len (Ne.symm hl0) (body m) (a.rew m) bits.length hwidth I 4
    (fun k b value ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ =>
      ⟨bi, bo, bm, brc, bki, bko, bkc, bf.trans (Fr.set b value (by simp))⟩)
    (by simpa [I, DS.rew] using
      (show Fr a (a.rew m) [c0, vJ] from fun _ _ => rfl)) hlen ?_
  · have hrun := Hs.seq (hs_rwM C m a) (fun b hb => by subst b; exact loopRun)
    refine Hs.mono hrun (by omega) ?_
    rintro b ⟨⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩, _, _⟩
    refine ⟨by simpa using bki, (bf len (by simp [hl0, hlj])).trans hlen,
      Cst.of_fr hc bf (by decide), bi, bo, bm, ?_, ?_, bko, bkc, bf⟩
    · rw [brc, Function.update_self]
    · intro q hq
      rw [brc, Function.update_of_ne hq]
  · intro k hk b ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ bindex blen
    have hread : b.rc m < (b.ram m).length := by rw [brc, Function.update_self, bm, hstore]; simpa using hk
    have hbit : (b.ram m).getD (b.rc m) 0 = bits[k].toNat := by
      rw [bm, hstore, brc, Function.update_self]
      calc
        (bits.map Bool.toNat).getD k 0 = (bits.getD k false).toNat := List.getD_map bits false Bool.toNat
        _ = bits[k].toNat := congrArg Bool.toNat (List.getD_eq_getElem bits false hk)
    let d := (b.set vJ bits[k].toNat).adv m
    have hr : Hs C (.op (.rdM m vJ)) b 1 (· = d) := by
      simpa only [hbit] using hs_rdM C m vJ b hread
    have hz : d.env vZ = 0 := by
      change (b.set vJ bits[k].toNat).env vZ = 0
      rw [DS.set_env_ne _ _ (by decide : vZ ≠ vJ), bf vZ (by decide), hc.z]
    have hs := send_read_bit C vZ vJ (by decide) false d bits[k] hz (by simp [d, DS.adv]) (by simp)
    have htake : bits.take (k + 1) = bits.take k ++ [bits[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    refine Hs.seq (t2 := 2) hr (fun e he => ?_)
    subst e
    refine ⟨sent false d [bits[k]], 2, hs, le_rfl, ?_, ?_, ?_⟩
    · refine ⟨bi, bo, bm, ?_, ?_, bko, bkc, ?_⟩
      · simp [sent, d, DS.adv, brc]
      · change b.out ++ [bits[k]] = a.out ++ bits.take (k + 1)
        rw [bki, htake, List.append_assoc]
      · intro q hq
        have hqj : q ≠ vJ := by intro heq; apply hq; simp [heq]
        change (b.set vJ bits[k].toNat).env q = a.env q
        rw [DS.set_env_ne _ _ hqj, bf q hq]
    · change (b.set vJ bits[k].toNat).env c0 = k
      rw [DS.set_env_ne _ _ (by decide : c0 ≠ vJ), bindex]
    · change (b.set vJ bits[k].toNat).env len = bits.length
      rw [DS.set_env_ne _ _ hlj, blen]

end NearCubicGates.Adapters.Code.TriplePreparationBits
