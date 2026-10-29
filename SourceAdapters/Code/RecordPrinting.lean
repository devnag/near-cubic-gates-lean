import Proof.Gates.Cells.Loop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid printing of a RAM list in the natural-word encoding.
The outer loop counts records; each word is printed by the existing routine
with its bit-length bound, retaining an arbitrary output prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.RecordPrinting
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

def scratch : List (Fin VV) := c0 :: vJ :: t3 :: emitNatT

def body (m : Fin MM) : St VV MM := .seq (.op (.rdM m t3)) emitNatO

def script (m : Fin MM) (len : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (forS c0 len (body m))

/-- A record-count scan with an explicit bit-length invoice and live-state frame. -/
theorem runs (C : Ctx) (m : Fin MM) (len : Fin VV) (hl : len ∉ scratch)
    (a : DS VV MM) (hc : Cst a) (records : List ℕ) (Λ : ℕ)
    (hstore : a.ram m = records) (hlen : a.env len = records.length)
    (hwidth : records.length < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hΛ : Λ + 2 < 2 ^ C.Wd) (hfit : ∀ value ∈ records, natBitLength value ≤ Λ) :
    Hs C (script m len) a (a.rc m + records.length * (40 * Λ + 46) + 6) (fun b =>
      b.out = a.out ++ records.flatMap natWord ∧ b.env len = records.length ∧ Cst b ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc m = records.length ∧
      (∀ q, q ≠ m → b.rc q = a.rc q) ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Fr a b scratch) := by
  have hl0 : len ≠ c0 := by intro he; apply hl; simp [scratch, he]
  have hlt : len ≠ t3 := by intro he; apply hl; simp [scratch, he]
  have hle : len ∉ emitNatT := by
    intro he
    exact hl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = a.ip ∧ b.out = a.out ++ (records.take k).flatMap natWord ∧ b.ram = a.ram ∧
    b.rc = Function.update a.rc m k ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b scratch
  have loopRun := forS_spec' (C := C) c0 len (Ne.symm hl0) (body m) (a.rew m) records.length hwidth I
    (40 * Λ + 42)
    (fun k b value ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ =>
      ⟨bi, bo, bm, brc, bki, bko, bkc, bf.trans (Fr.set b value (by simp [scratch]))⟩)
    (by simpa [I, DS.rew] using (show Fr a (a.rew m) scratch from fun _ _ => rfl)) hlen ?_
  · have hrun := Hs.seq (hs_rwM C m a) (fun b hb => by subst b; exact loopRun)
    refine Hs.mono hrun (by apply le_of_eq; ring) ?_
    rintro b ⟨⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩, _, _⟩
    refine ⟨by simpa using bo, (bf len hl).trans hlen, Cst.of_fr hc bf (by decide),
      bi, bm, ?_, ?_, bki, bko, bkc, bf⟩
    · rw [brc, Function.update_self]
    · intro q hq
      rw [brc, Function.update_of_ne hq]
  · intro k hk b ⟨bi, bo, bm, brc, bki, bko, bkc, bf⟩ bindex blen
    have hread : b.rc m < (b.ram m).length := by rw [brc, Function.update_self, bm, hstore]; exact hk
    have hvalue : (b.ram m).getD (b.rc m) 0 = records[k] := by
      rw [bm, hstore, brc, Function.update_self]
      exact List.getD_eq_getElem records 0 hk
    let d := (b.set t3 records[k]).adv m
    have hr : Hs C (.op (.rdM m t3)) b 1 (· = d) := by
      simpa only [hvalue] using hs_rdM C m t3 b hread
    have hbd : Fr b d scratch := Fr.set b _ (by simp [scratch])
    have hdc : Cst d := Cst.of_fr hc (bf.trans hbd) (by decide)
    have hdt : d.env t3 = records[k] := by simp [d, DS.adv]
    have hbits : natBitLength records[k] ≤ Λ := hfit _ (List.getElem_mem hk)
    have hemit := emitNatO_spec (C := C) d hdc hW (by rw [hdt]; omega)
    have hemit' := hemit.mono (show 40 * natBitLength (d.env t3) + 40 ≤ 40 * Λ + 40 by rw [hdt]; omega)
      (fun _ h => h)
    have htake : records.take (k + 1) = records.take k ++ [records[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    refine Hs.mono (Hs.seq (t2 := 40 * Λ + 40) hr (fun e he => ?_)) (by omega) (fun _ h => h)
    subst e
    refine Hs.mono hemit' le_rfl ?_
    rintro f ⟨fo, frest, _, ff⟩
    simp only [Prod.mk.injEq] at frest
    obtain ⟨fi, fm, frc, fki, fko, fkc⟩ := frest
    refine ⟨⟨fi.trans bi, ?_, fm.trans bm, ?_, fki.trans bki, fko.trans bko, fkc.trans bkc,
      bf.trans (hbd.trans (ff.weaken ?_))⟩, ?_, ?_⟩
    · rw [fo, hdt]
      change b.out ++ natWord records[k] = a.out ++ (records.take (k + 1)).flatMap natWord
      rw [bo, htake, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    · rw [frc]
      simp [d, DS.adv, brc]
    · intro q hq
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
    · rw [ff c0 (by decide)]
      change (b.set t3 records[k]).env c0 = k
      rw [DS.set_env_ne _ _ (by decide : c0 ≠ t3), bindex]
    · rw [ff len hle]
      change (b.set t3 records[k]).env len = records.length
      rw [DS.set_env_ne _ _ hlt, blen]

end NearCubicGates.Adapters.Code.RecordPrinting
