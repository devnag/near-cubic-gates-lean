import SourceAdapters.Code.RecordLookupChoice

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid first-occurrence lookup in numeric records. The loop
runs once per record, retaining only the first matching index. Missing values
return the list length; numeric values never determine the iteration count. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.RecordLookup
open NearCubicGates.Close.Cells

def body (m : Fin MM) (target len result : Fin VV) : St VV MM :=
  .seq (.op (.rdM m vJ)) (choose target len result)

def script (m : Fin MM) (target len result : Fin VV) : St VV MM :=
  .seq (.op (.copy result len)) (.seq (.op (.rwM m)) (forS c0 len (body m target len result)))

/-- Exact first index for arbitrary lists, including duplicates and absent values.
All source records and non-scratch state survive; the store cursor ends at length. -/
theorem runs (C : Ctx) (m : Fin MM) (target len result : Fin VV)
    (ht : target ∉ [c0, vJ, result]) (hl : len ∉ [c0, vJ, result])
    (hr0 : result ≠ c0) (hrj : result ≠ vJ)
    (hcst : vZ ∉ [c0, vJ, result] ∧ v1 ∉ [c0, vJ, result] ∧ v2 ∉ [c0, vJ, result])
    (a : DS VV MM) (hc : Cst a) (records : List ℕ)
    (hstore : a.ram m = records) (hlen : a.env len = records.length)
    (hwidth : records.length < 2 ^ C.Wd) :
    Hs C (script m target len result) a (a.rc m + 9 * records.length + 8) (fun b =>
      b.env result = records.idxOf (a.env target) ∧ b.env target = a.env target ∧
      b.env len = records.length ∧ Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc m = records.length ∧ (∀ q, q ≠ m → b.rc q = a.rc q) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ, result]) := by
  have hl0 : len ≠ c0 := by intro he; apply hl; simp [he]
  have hlj : len ≠ vJ := by intro he; apply hl; simp [he]
  have hlr : len ≠ result := by intro he; apply hl; simp [he]
  have htj : target ≠ vJ := by intro he; apply ht; simp [he]
  let a1 := a.set result (a.env len)
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env result = saved records.length (records.idxOf (a.env target)) k ∧
    b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = Function.update a.rc m k ∧
    b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ, result]
  have loopRun := forS_spec' (C := C) c0 len (Ne.symm hl0) (body m target len result)
    (a1.rew m) records.length hwidth I 5
    (fun k b value ⟨bv, bi, bo, bm, brc, bki, bko, bkc, bf⟩ =>
      ⟨by simpa [hr0] using bv, bi, bo, bm, brc, bki, bko, bkc,
        bf.trans (Fr.set b value (by simp))⟩)
    (by
      have hf : Fr a (a1.rew m) [c0, vJ, result] := Fr.set a _ (by simp)
      simpa [I, a1, DS.rew, saved, hlen] using hf)
    (by simpa [a1, DS.rew, hlr] using hlen) ?_
  · have hrun := Hs.seq (hs_copy C result len a (Ne.symm hlr)) (fun b hb => by
      subst b
      exact Hs.seq (hs_rwM C m a1) (fun d hd => by subst d; exact loopRun))
    refine Hs.mono hrun (by dsimp [a1]; omega) ?_
    rintro b ⟨⟨bv, bi, bo, bm, brc, bki, bko, bkc, bf⟩, _, _⟩
    refine ⟨bv.trans (saved_final records (a.env target)), bf target ht, (bf len hl).trans hlen,
      Cst.of_fr hc bf hcst, bi, bo, bm, ?_, ?_, bki, bko, bkc, bf⟩
    · rw [brc, Function.update_self]
    · intro q hq
      rw [brc, Function.update_of_ne hq]
  · intro k hk b ⟨bv, bi, bo, bm, brc, bki, bko, bkc, bf⟩ bindex blen
    have hread : b.rc m < (b.ram m).length := by rw [brc, Function.update_self, bm, hstore]; exact hk
    have hvalue : (b.ram m).getD (b.rc m) 0 = records[k] := by
      rw [bm, hstore, brc, Function.update_self]
      exact List.getD_eq_getElem records 0 hk
    let d := (b.set vJ records[k]).adv m
    have hr : Hs C (.op (.rdM m vJ)) b 1 (· = d) := by
      simpa only [hvalue] using hs_rdM C m vJ b hread
    have dj : d.env vJ = records[k] := by simp [d, DS.adv]
    have dt : d.env target = a.env target := by
      change (b.set vJ records[k]).env target = a.env target
      rw [DS.set_env_ne _ _ htj, bf target ht]
    have dr : d.env result = saved records.length (records.idxOf (a.env target)) k := by
      simpa [d, DS.adv, hrj] using bv
    have dl : d.env len = records.length := by simpa [d, DS.adv, hlj] using blen
    have dc : d.env c0 = k := by simpa [d, DS.adv, (by decide : c0 ≠ vJ)] using bindex
    have hchoice := choose_spec C target len result htj (Ne.symm hlr) hr0 hrj d
    refine Hs.seq (t2 := 3) hr (fun e he => ?_)
    subst e
    refine Hs.mono hchoice le_rfl ?_
    rintro f ⟨fv, fs, ff⟩
    have hfv : f.env result = saved records.length (records.idxOf (a.env target)) (k + 1) := by
      rw [dj, dt, dr, dl, dc] at fv
      exact fv.trans (saved_step records (a.env target) k hk)
    have hbd : Fr b d [c0, vJ, result] := Fr.set b _ (by simp)
    refine ⟨⟨hfv, fs.ip.trans bi, fs.out.trans bo, fs.ram.trans bm, ?_, fs.kin.trans bki,
      fs.kout.trans bko, fs.kc.trans bkc,
      bf.trans (hbd.trans (ff.weaken (fun y hy => List.mem_cons_of_mem c0 hy)))⟩, ?_, ?_⟩
    · rw [fs.rc]
      simp [d, DS.adv, brc]
    · rw [ff c0 (by simp [Ne.symm hr0, (by decide : c0 ≠ vJ)]), dc]
    · rw [ff len (by simp [hlj, hlr]), dl]

end NearCubicGates.Adapters.Code.RecordLookup
