import Proof.Gates.CounterMachine.CellTablesLem

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTables

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- Scratch variables of `convP` (all in `scr`). -/
def u0 : Fin VV := ⟨48, by decide⟩   -- row `r`
def u1 : Fin VV := ⟨49, by decide⟩   -- column `j`
def u2 : Fin VV := ⟨50, by decide⟩   -- outer index `i = r + 2^⌈s/2⌉·j`
def u3 : Fin VV := ⟨51, by decide⟩   -- the bit read
def u4 : Fin VV := ⟨52, by decide⟩   -- the entry `v = encS z`
def u5 : Fin VV := ⟨53, by decide⟩   -- `2^k`
def u6 : Fin VV := ⟨54, by decide⟩   -- `|z|`
def u7 : Fin VV := ⟨55, by decide⟩   -- the sign bit
def u8 : Fin VV := ⟨56, by decide⟩   -- the value
def u9 : Fin VV := ⟨57, by decide⟩   -- junk
def u10 : Fin VV := ⟨58, by decide⟩  -- the record

/-- Read one framed record `frame (binary w v)` from `kout` into `u4` (marker-driven: `w` is not given). -/
def rdRec : St VV MM :=
  .seq (.op (.zero u4)) (.seq (.op (.copy u5 v1)) (.seq (.op (.rdK u3))
    (.loop (.eq u3 v1) (.seq (.op (.rdK u3)) (.seq (.ite (.eq u3 v1) (.op (.add u4 u5)) (.op (.zero u9)))
      (.seq (.op (.shl u5)) (.op (.rdK u3))))))))

/-- The value of the entry `u4 = encS z` into `u8`: `(z mod QE).toNat` (residue) or `z.toNat` (moment). -/
def valP : St VV MM :=
  .seq (.op (.dm u4 v2 u6 u7)) (.ite (.eq vRS v1)
    (.seq (.op (.dm u6 vQE u9 u8)) (.ite (.eq u7 v1)
      (.ite (.eq u8 vZ) (.op (.zero u9)) (.seq (.op (.copy u9 vQE)) (.seq (.op (.sub u9 u8)) (.op (.copy u8 u9)))))
      (.op (.zero u9))))
    (.ite (.eq u7 v1) (.op (.zero u8)) (.op (.copy u8 u6))))

/-- Append the record `u2·SH + KY + u8` to `sREC`. -/
def recP : St VV MM :=
  .seq (.op (.mul u2 vSH u10)) (.seq (.op (.add u10 vKY)) (.seq (.op (.add u10 u8)) (.op (.wrM sREC u10))))

/-- One outer index: `i := 2^⌈s/2⌉·j + r`, read the entry, convert, append. -/
def oneP : St VV MM :=
  .seq (.op (.mul vH1 u1 u2)) (.seq (.op (.add u2 u0)) (.seq rdRec (.seq valP recP)))

def convP : St VV MM := forS u0 vH1 (forS u1 vH0 oneP)

/-- Everything but the variables and the call output cursor agrees. -/
structure SameK (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  out : b.out = a.out
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout

theorem SameK.trans {a b d : DS VV MM} (h1 : SameK a b) (h2 : SameK b d) : SameK a d :=
  ⟨h2.ip.trans h1.ip, h2.out.trans h1.out, h2.ram.trans h1.ram, h2.rc.trans h1.rc, h2.kin.trans h1.kin,
    h2.kout.trans h1.kout⟩

theorem SameK.of_same {a b : DS VV MM} (h : Same a b) : SameK a b := ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout⟩

theorem Frame.of_sameK {a b : DS VV MM} {T : List (Fin VV)} (hf : Fr a b T) (hT : ∀ y ∈ T, y ∈ scr)
    (hs : SameK a b) : Frame a b :=
  ⟨Fr.weaken hf hT, hs.ip, hs.kin, hs.kout, fun m _ _ => by rw [hs.ram], fun m _ _ => by rw [hs.rc]⟩

theorem frame_bin_length (w v : ℕ) : (frame (binary w v)).length = 2 * w + 1 := by
  rw [frame_length', binary_length]

/-! ## Reading one record -/

theorem rdRec_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (w v : ℕ) (rest : List Bool)
    (hkd : b.kout.drop b.kc = frame (binary w v) ++ rest) (hv : v < 2 ^ w) (hW : w < C.Wd) :
    Hs C rdRec b (10 * w + 8) (fun d => d.env u4 = v ∧ d.kc = b.kc + (2 * w + 1) ∧
      Fr b d [u3, u4, u5, u9] ∧ SameK b d) := by
  have hlen := frame_bin_length w v
  have hpw : 2 ^ w < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hW
  have mark : ∀ k, k < w → bitOf b.kout (b.kc + 2 * k) = 1 := fun k hk' => by
    rw [bitOf_drop hkd (2 * k) (by omega), frame_getD_even _ k (by rw [binary_length]; exact hk')]; rfl
  have mark_end : bitOf b.kout (b.kc + 2 * w) = 0 := by
    rw [bitOf_drop hkd (2 * w) (by omega)]
    have := frame_getD_end (binary w v); rw [binary_length] at this; rw [this]; rfl
  have dbit : ∀ k, k < w → bitOf b.kout (b.kc + (2 * k + 1)) = v / 2 ^ k % 2 := fun k hk' => by
    rw [bitOf_drop hkd (2 * k + 1) (by omega), frame_getD_odd, binary_getD_bit w v k hk', toNat_bit]
  let I : ℕ → DS VV MM → Prop := fun k d => d.env u4 = v % 2 ^ k ∧ d.env u5 = 2 ^ k ∧
    d.env u3 = bitOf b.kout (b.kc + 2 * k) ∧ d.kc = b.kc + 2 * k + 1 ∧ Fr b d [u3, u4, u5, u9] ∧ SameK b d
  have hloop := Hs.loopN (C := C) (c := .eq u3 v1) (s := .seq (.op (.rdK u3)) (.seq (.ite (.eq u3 v1)
      (.op (.add u4 u5)) (.op (.zero u9))) (.seq (.op (.shl u5)) (.op (.rdK u3))))) (show u3 ≠ v1 by decide)
    I w 8 ?_ ?_
  · refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (1 + (w * (8 + 2) + 2) + 1) + 1) (hs_zero C u4 b)
      (fun b1 hb1 => ?_)) (by omega) (fun _ h => h)
    subst hb1
    refine Hs.seq (t1 := 1) (t2 := 1 + (w * (8 + 2) + 2) + 1) (hs_copy C u5 v1 _ (by decide)) (fun b2 hb2 => ?_)
    subst hb2
    refine Hs.seq (t1 := 1) (t2 := w * (8 + 2) + 2) (hs_rdK C u3 _ (by
      show b.kc < b.kout.length; have := lt_of_drop hkd 0 (by omega); omega)) (fun b3 hb3 => ?_)
    subst hb3
    refine Hs.mono (hloop _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl ?_
    · vsimp [Nat.mod_one]
    · vsimp [hc.one]
    · vsimp []
    · rfl
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      vsimp [Function.update_apply, hy.1, hy.2.1, hy.2.2.1]
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro d ⟨d1, _, _, d4, d5, d6⟩
      refine ⟨by rw [d1, Nat.mod_eq_of_lt hv], by rw [d4]; ring, d5, d6⟩
  · intro k hk d ⟨d1, d2, d3, d4, d5, d6⟩
    have dc : Cst d := Cst.of_fr hc d5 (by decide)
    refine ⟨by simp only [Cnd.eval, d3, mark k hk, dc.one, decide_true], ?_⟩
    have dko : d.kout = b.kout := d6.kout
    refine Hs.seq (t1 := 1) (t2 := 6) (hs_rdK C u3 d (by
      rw [dko, d4]; have := lt_of_drop hkd (2 * k + 1) (by omega); omega)) (fun e1 he1 => ?_)
    subst he1
    set e1 : DS VV MM := { d.set u3 (bitOf d.kout d.kc) with kc := d.kc + 1 } with he1
    have e1b : e1.env u3 = v / 2 ^ k % 2 := by
      rw [he1]; simp only [DS.set_env_self]; rw [dko, d4, show b.kc + 2 * k + 1 = b.kc + (2 * k + 1) by ring]
      exact dbit k hk
    have e1u4 : e1.env u4 = v % 2 ^ k := by rw [he1]; vsimp [d1]
    have e1u5 : e1.env u5 = 2 ^ k := by rw [he1]; vsimp [d2]
    have e1c : Cst e1 := ⟨by rw [he1]; vsimp [dc.z], by rw [he1]; vsimp [dc.one], by rw [he1]; vsimp [dc.two]⟩
    have hmod : v % 2 ^ (k + 1) = v % 2 ^ k + 2 ^ k * (v / 2 ^ k % 2) := Nat.mod_pow_succ
    have hk1 : 2 ^ (k + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hk
    have step2 : Hs C (.ite (.eq u3 v1) (.op (.add u4 u5)) (.op (.zero u9))) e1 2 (fun e2 =>
        e2.env u4 = v % 2 ^ (k + 1) ∧ Fr e1 e2 [u4, u9] ∧ Same e1 e2) := by
      refine Hs.ite (c := .eq u3 v1) (show u3 ≠ v1 by decide) (fun h => ?_) (fun h => ?_)
      · have hb : v / 2 ^ k % 2 = 1 := by simpa [Cnd.eval, e1b, e1c.one] using h
        have hlt : v % 2 ^ k + 2 ^ k < 2 ^ C.Wd := by
          have := Nat.mod_lt v (show 0 < 2 ^ k by positivity)
          have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
          omega
        refine Hs.mono (hs_add C u4 u5 e1 (by decide) (by rw [e1u4, e1u5]; exact hlt)) le_rfl ?_
        rintro e rfl
        exact ⟨by vsimp [e1u4, e1u5, hmod, hb], Fr.set e1 _ (by decide), Same.set _ _ _⟩
      · have hb : v / 2 ^ k % 2 = 0 := by
          have : v / 2 ^ k % 2 ≠ 1 := by simpa [Cnd.eval, e1b, e1c.one] using h
          omega
        refine Hs.mono (hs_zero C u9 e1) le_rfl ?_
        rintro e rfl
        exact ⟨by vsimp [e1u4, hmod, hb], Fr.set e1 _ (by decide), Same.set _ _ _⟩
    refine Hs.seq (t1 := 2) (t2 := 3) step2 (fun e2 ⟨e2a, e2b, e2c⟩ => ?_)
    have e2u5 : e2.env u5 = 2 ^ k := by rw [e2b u5 (by decide), e1u5]
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C u5 e2 (by
      rw [e2u5]; have : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      omega)) (fun e3 he3 => ?_)
    subst he3
    have e3kc : (e2.set u5 (2 * e2.env u5)).kc = b.kc + 2 * k + 2 := by
      simp only [DS.set_kc, e2c.kc, he1, d4]
    have e3ko : (e2.set u5 (2 * e2.env u5)).kout = b.kout := by simp only [DS.set_kout, e2c.kout, he1, dko]
    refine Hs.mono (hs_rdK C u3 _ (by
      rw [e3ko, e3kc]; have := lt_of_drop hkd (2 * k + 2) (by omega); omega)) le_rfl ?_
    rintro e4 rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · vsimp [e2a]
    · vsimp [e2u5]; ring
    · simp only [DS.set_env_self]; rw [e3ko, e3kc]; congr 1
    · simp only [e3kc]; ring
    · intro y hy
      have hy' := hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
      vsimp [Function.update_apply, hy'.1, hy'.2.2.1]
      rw [e2b y (by simp [hy'.2.1, hy'.2.2.2])]
      rw [he1]; vsimp [Function.update_apply, hy'.1]
      exact d5 y hy
    · refine d6.trans (SameK.trans (show SameK d e1 from ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (SameK.trans (SameK.of_same e2c) ?_))
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro d ⟨_, _, d3, _, d5, _⟩
    have dc : Cst d := Cst.of_fr hc d5 (by decide)
    simp only [Cnd.eval, d3, mark_end, dc.one]; rfl

/-! ## The value and the record -/

theorem valP_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (res : Bool) (QE : ℕ)
    (hRS : b.env vRS = if res then 1 else 0) (hQE : b.env vQE = QE) (hQ : res = true → 0 < QE)
    (h2Q : 2 * QE < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C valP b 12 (fun d => d.env u8 = valOf res QE (b.env u4) ∧ Fr b d [u6, u7, u8, u9] ∧ Same b d) := by
  set v := b.env u4 with hv
  have h4 : 2 * 2 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  refine Hs.seq (t1 := 1) (t2 := 10) (hs_dm C u4 v2 u6 u7 b (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hc.two]; norm_num) (by rw [hc.two]; exact h4)) (fun e he => ?_)
  subst he
  rw [hc.two]
  set e := (b.set u6 (v / 2)).set u7 (v % 2) with he
  have e6 : e.env u6 = v / 2 := by rw [he]; vsimp []
  have e7 : e.env u7 = v % 2 := by rw [he]; vsimp []
  have ec : Cst e := ⟨by rw [he]; vsimp [hc.z], by rw [he]; vsimp [hc.one], by rw [he]; vsimp [hc.two]⟩
  have eRS : e.env vRS = if res then 1 else 0 := by rw [he]; vsimp [hRS]
  have eQE : e.env vQE = QE := by rw [he]; vsimp [hQE]
  have efr : Fr b e [u6, u7, u8, u9] := Fr.trans (Fr.set b _ (by decide)) (Fr.set _ _ (by decide))
  have esm : Same b e := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine Hs.ite (c := .eq vRS v1) (show vRS ≠ v1 by decide) (fun h => ?_) (fun h => ?_)
  · have hres : res = true := by
      cases res
      · simp [Cnd.eval, eRS, ec.one] at h
      · rfl
    subst hres
    have hQ0 := hQ rfl
    refine Hs.seq (t1 := 1) (t2 := 7) (hs_dm C u6 vQE u9 u8 e (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [eQE]; exact hQ0) (by rw [eQE]; omega)) (fun f hf => ?_)
    subst hf
    rw [e6, eQE]
    set f := (e.set u9 (v / 2 / QE)).set u8 (v / 2 % QE) with hf
    have f8 : f.env u8 = v / 2 % QE := by rw [hf]; vsimp []
    have f7 : f.env u7 = v % 2 := by rw [hf]; vsimp [e7]
    have fc : Cst f := ⟨by rw [hf]; vsimp [ec.z], by rw [hf]; vsimp [ec.one], by rw [hf]; vsimp [ec.two]⟩
    have fQE : f.env vQE = QE := by rw [hf]; vsimp [eQE]
    have ffr : Fr b f [u6, u7, u8, u9] := Fr.trans efr (Fr.trans (Fr.set e _ (by decide)) (Fr.set _ _ (by decide)))
    have fsm : Same b f := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hmlt : v / 2 % QE < QE := Nat.mod_lt _ hQ0
    refine Hs.ite (c := .eq u7 v1) (show u7 ≠ v1 by decide) (fun h7 => ?_) (fun h7 => ?_)
    · have hs1 : v % 2 = 1 := by simpa [Cnd.eval, f7, fc.one] using h7
      refine Hs.ite (c := .eq u8 vZ) (show u8 ≠ vZ by decide) (fun h8 => ?_) (fun h8 => ?_)
      · have hm : v / 2 % QE = 0 := by simpa [Cnd.eval, f8, fc.z] using h8
        refine Hs.mono (hs_zero C u9 f) (by norm_num) ?_
        rintro g rfl
        refine ⟨?_, Fr.trans ffr (Fr.set f _ (by decide)), fsm.trans (Same.set _ _ _)⟩
        rw [DS.set_env_ne _ _ (by decide), f8]; unfold valOf; simp [hs1, hm]
      · have hm : v / 2 % QE ≠ 0 := by simpa [Cnd.eval, f8, fc.z] using h8
        refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C u9 vQE f (by decide)) (fun g hg => ?_)
        subst hg
        refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C u9 u8 _ (by decide) (by vsimp [f8, fQE]; omega))
          (fun g' hg' => ?_)
        subst hg'
        refine Hs.mono (hs_copy C u8 u9 _ (by decide)) le_rfl ?_
        rintro r rfl
        refine ⟨?_, ?_, ?_⟩
        · vsimp [f8, fQE]; unfold valOf; simp [hs1, hm]
        · exact Fr.trans ffr (Fr.trans (Fr.set f _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
            (Fr.set _ _ (by decide))))
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · have hs1 : v % 2 ≠ 1 := by simpa [Cnd.eval, f7, fc.one] using h7
      refine Hs.mono (hs_zero C u9 f) (by norm_num) ?_
      rintro g rfl
      refine ⟨?_, Fr.trans ffr (Fr.set f _ (by decide)), fsm.trans (Same.set _ _ _)⟩
      rw [DS.set_env_ne _ _ (by decide), f8]; unfold valOf; simp [hs1]
  · have hres : res = false := by
      cases res
      · rfl
      · simp [Cnd.eval, eRS, ec.one] at h
    subst hres
    refine Hs.mono (t := 2) (Hs.ite (c := .eq u7 v1) (show u7 ≠ v1 by decide) (fun h7 => ?_) (fun h7 => ?_))
      (by norm_num) (fun _ h => h)
    · have hs1 : v % 2 = 1 := by simpa [Cnd.eval, e7, ec.one] using h7
      refine Hs.mono (hs_zero C u8 e) le_rfl ?_
      rintro g rfl
      refine ⟨?_, Fr.trans efr (Fr.set e _ (by decide)), esm.trans (Same.set _ _ _)⟩
      vsimp []; unfold valOf; simp [hs1]
    · have hs1 : v % 2 ≠ 1 := by simpa [Cnd.eval, e7, ec.one] using h7
      refine Hs.mono (hs_copy C u8 u6 e (by decide)) le_rfl ?_
      rintro g rfl
      refine ⟨?_, Fr.trans efr (Fr.set e _ (by decide)), esm.trans (Same.set _ _ _)⟩
      vsimp [e6]; unfold valOf; simp [hs1]

theorem recP_spec (C : Ctx) (b : DS VV MM) (R : ℕ) (hR : R = b.env u2 * b.env vSH + b.env vKY + b.env u8)
    (hRW : R < 2 ^ C.Wd) (hrc : b.rc sREC = (b.ram sREC).length) :
    Hs C recP b 7 (fun d => d.ram sREC = b.ram sREC ++ [R] ∧ d.rc sREC = (d.ram sREC).length ∧
      Fr b d [u10] ∧ Frame b d ∧ d.out = b.out ∧ d.kc = b.kc ∧ d.kout = b.kout) := by
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_mul C u2 vSH u10 b (by decide) (by decide) (by decide) (by
    rw [hR] at hRW; omega)) (fun d1 hd1 => ?_)
  subst hd1
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_add C u10 vKY _ (by decide) (by vsimp []; rw [hR] at hRW; omega))
    (fun d2 hd2 => ?_)
  subst hd2
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_add C u10 u8 _ (by decide) (by vsimp []; rw [hR] at hRW; omega))
    (fun d3 hd3 => ?_)
  subst hd3
  set d := ((b.set u10 (b.env u2 * b.env vSH)).set u10 ((b.set u10 (b.env u2 * b.env vSH)).env u10 +
    (b.set u10 (b.env u2 * b.env vSH)).env vKY)) with hd
  set d' := d.set u10 (d.env u10 + d.env u8) with hd'
  have hu : d'.env u10 = R := by rw [hd', hd, hR]; vsimp []
  refine Hs.mono (hs_wrM C sREC u10 d' (by rw [hd', hd]; simp only [DS.set_rc, DS.set_ram, hrc]; rfl)) le_rfl ?_
  rintro e rfl
  have hram : d'.ram sREC = b.ram sREC := rfl
  have hrc' : d'.rc sREC = b.rc sREC := rfl
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [DS.put, Function.update_self, hu, hram, hrc']
    unfold putAt; rw [hrc, if_neg (lt_irrefl _)]
  · simp only [DS.put, Function.update_self, hram, hrc']
    unfold putAt; rw [hrc, if_neg (lt_irrefl _)]; simp
  · intro y hy
    have h10 : y ≠ u10 := fun h => hy (by rw [h]; simp)
    simp only [DS.put, hd', hd, DS.set, Function.update_apply, if_neg h10]
  · refine Frame.trans ?_ (Frame.put _ _)
    exact Frame.trans (Frame.set _ _ _ (by decide)) (Frame.trans (Frame.set _ _ _ (by decide))
      (Frame.set _ _ _ (by decide)))

/-! ## One outer index, and the two loops -/

/-- `ConvSpec`'s hypotheses on the start state `a`. -/
structure CHyp (C : Ctx) (a : DS VV MM) (s w SH KY QE : ℕ) (res : Bool) (z : ℕ → ℤ) : Prop where
  cst : Cst a
  h1 : a.env vH1 = 2 ^ ((s + 1) / 2)
  h0 : a.env vH0 = 2 ^ (s / 2)
  sh : a.env vSH = SH
  ky : a.env vKY = KY
  qe : a.env vQE = QE
  rs : a.env vRS = if res then 1 else 0
  q0 : res = true → 0 < QE
  enc : ∀ i < 2 ^ s, WordPrograms.SInt.encS (z i) < 2 ^ w
  wd : w + s + 2 ≤ C.Wd
  q2 : 2 * QE < 2 ^ C.Wd
  hrec : ∀ i < 2 ^ s, recOf SH KY QE res i (z i) < 2 ^ C.Wd

/-- The state after the first `t` outer indices of the printer order. -/
def CInv (a : DS VV MM) (s w SH KY QE : ℕ) (res : Bool) (z : ℕ → ℤ) (t : ℕ) (d : DS VV MM) : Prop :=
  d.kout.drop d.kc = WordPrograms.recStream (((printerOrder s).drop t).map
      fun i => binary w (WordPrograms.SInt.encS (z i))) ∧
    d.ram sREC = a.ram sREC ++ ((printerOrder s).take t).map (fun i => recOf SH KY QE res i (z i)) ∧
    d.rc sREC = (d.ram sREC).length ∧ d.out = a.out ∧ Frame a d

theorem CInv.set {a d : DS VV MM} {s w SH KY QE : ℕ} {res : Bool} {z : ℕ → ℤ} {t : ℕ}
    (h : CInv a s w SH KY QE res z t d) (x : Fin VV) (v : ℕ) (hx : x ∈ scr) :
    CInv a s w SH KY QE res z t (d.set x v) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans (Frame.set d x v hx)⟩

theorem oneP_spec (C : Ctx) (a : DS VV MM) (s w SH KY QE : ℕ) (res : Bool) (z : ℕ → ℤ)
    (hy : CHyp C a s w SH KY QE res z) (r j : ℕ) (hr : r < 2 ^ ((s + 1) / 2)) (hj : j < 2 ^ (s / 2))
    (d : DS VV MM) (hI : CInv a s w SH KY QE res z (r * 2 ^ (s / 2) + j) d) (hd0 : d.env u0 = r)
    (hd1 : d.env u1 = j) :
    Hs C oneP d (10 * w + 33) (fun e => CInv a s w SH KY QE res z (r * 2 ^ (s / 2) + j + 1) e ∧
      e.env u0 = r ∧ e.env u1 = j) := by
  obtain ⟨hk, hram, hrc, hout, hfr⟩ := hI
  set t := r * 2 ^ (s / 2) + j with ht
  set i := r + 2 ^ ((s + 1) / 2) * j with hi
  set L := printerOrder s with hL
  have hil : i < 2 ^ s := index_lt s r j hr hj
  have hget : L[t]? = some i := printerOrder_getElem? s r j hr hj
  have dc : Cst d := hfr.cst hy.cst
  have dH1 : d.env vH1 = 2 ^ ((s + 1) / 2) := by rw [hfr.env_lo vH1 (by decide)]; exact hy.h1
  have dSH : d.env vSH = SH := by rw [hfr.env_lo vSH (by decide)]; exact hy.sh
  have dKY : d.env vKY = KY := by rw [hfr.env_lo vKY (by decide)]; exact hy.ky
  have dQE : d.env vQE = QE := by rw [hfr.env_lo vQE (by decide)]; exact hy.qe
  have dRS : d.env vRS = if res then 1 else 0 := by rw [hfr.env_lo vRS (by decide)]; exact hy.rs
  have hsW : 2 ^ s < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by have := hy.wd; omega)
  have hW2 : 2 ≤ C.Wd := by have := hy.wd; omega
  have hwW : w < C.Wd := by have := hy.wd; omega
  -- the index
  unfold oneP
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + ((10 * w + 8) + (12 + 7 + 1) + 1) + 1) (hs_mul C vH1 u1 u2 d (by decide) (by decide) (by decide)
    (by rw [dH1, hd1]; omega)) (fun d1 hd1' => ?_)) (by omega) (fun _ h => h)
  subst hd1'
  refine Hs.seq (t1 := 1) (t2 := (10 * w + 8) + (12 + 7 + 1) + 1) (hs_add C u2 u0 _ (by decide) (by vsimp [dH1, hd1, hd0]; omega))
    (fun d2 hd2 => ?_)
  subst hd2
  set d2 := (d.set u2 (d.env vH1 * d.env u1)).set u2 ((d.set u2 (d.env vH1 * d.env u1)).env u2 +
    (d.set u2 (d.env vH1 * d.env u1)).env u0) with hd2
  have d2i : d2.env u2 = i := by rw [hd2]; vsimp [dH1, hd1, hd0]; ring
  have d2c : Cst d2 := ⟨by rw [hd2]; vsimp [dc.z], by rw [hd2]; vsimp [dc.one], by rw [hd2]; vsimp [dc.two]⟩
  have d2fr : Fr d d2 [u2] := Fr.trans (Fr.set d _ (by decide)) (Fr.set _ _ (by decide))
  -- the entry
  have hk2 : d2.kout.drop d2.kc = frame (binary w (WordPrograms.SInt.encS (z i))) ++
      WordPrograms.recStream ((L.drop (t + 1)).map fun i => binary w (WordPrograms.SInt.encS (z i))) := by
    show d.kout.drop d.kc = _
    rw [hk, drop_cons_getElem L t i hget, List.map_cons, recStream_cons]
  refine Hs.seq (t1 := 10 * w + 8) (t2 := 12 + 7 + 1) (rdRec_spec C d2 d2c w _ _ hk2 (hy.enc i hil) hwW)
    (fun d3 ⟨d3a, d3b, d3c, d3d⟩ => ?_)
  have d3c' : Cst d3 := Cst.of_fr d2c d3c (by decide)
  have d3RS : d3.env vRS = if res then 1 else 0 := by rw [d3c vRS (by decide), d2fr vRS (by decide), dRS]
  have d3QE : d3.env vQE = QE := by rw [d3c vQE (by decide), d2fr vQE (by decide), dQE]
  refine Hs.seq (t1 := 12) (t2 := 7) (valP_spec C d3 d3c' res QE d3RS d3QE hy.q0 hy.q2 hW2)
    (fun d4 ⟨d4a, d4b, d4c⟩ => ?_)
  have d4u2 : d4.env u2 = i := by rw [d4b u2 (by decide), d3c u2 (by decide), d2i]
  have d4SH : d4.env vSH = SH := by rw [d4b vSH (by decide), d3c vSH (by decide), d2fr vSH (by decide), dSH]
  have d4KY : d4.env vKY = KY := by rw [d4b vKY (by decide), d3c vKY (by decide), d2fr vKY (by decide), dKY]
  have d4u8 : d4.env u8 = if res then (z i % (QE : ℤ)).toNat else (z i).toNat := by
    rw [d4a, d3a, valOf_encS res QE (z i) hy.q0]
  have hR : recOf SH KY QE res i (z i) = d4.env u2 * d4.env vSH + d4.env vKY + d4.env u8 := by
    rw [d4u2, d4SH, d4KY, d4u8]; rfl
  have d4rc : d4.rc sREC = (d4.ram sREC).length := by
    rw [d4c.rc, d4c.ram, d3d.rc, d3d.ram]; exact hrc
  refine Hs.mono (recP_spec C d4 _ hR (hy.hrec i hil) d4rc) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5, e6, e7⟩
  refine ⟨⟨?_, ?_, e2, ?_, ?_⟩, ?_, ?_⟩
  · rw [e7, e6, d4c.kout, d4c.kc, d3d.kout, d3b]
    have := drop_adv hk2
    rw [frame_bin_length] at this
    exact this
  · rw [e1, d4c.ram, d3d.ram]
    show d.ram sREC ++ _ = _
    rw [hram, take_succ_getElem L t i hget, List.map_append, List.map_singleton, List.append_assoc]
  · rw [e5, d4c.out, d3d.out]; exact hout
  · refine hfr.trans (Frame.trans (Frame.trans (Frame.set _ _ _ (by decide)) (Frame.set _ _ _ (by decide)))
      (Frame.trans (Frame.of_sameK d3c (by decide) d3d) (Frame.trans (Frame.of_sameK d4b (by decide)
        (SameK.of_same d4c)) e4)))
  · rw [e3 u0 (by decide), d4b u0 (by decide), d3c u0 (by decide), d2fr u0 (by decide), hd0]
  · rw [e3 u1 (by decide), d4b u1 (by decide), d3c u1 (by decide), d2fr u1 (by decide), hd1]

theorem convP_spec : ConvSpec convP := by
  intro C a s w SH KY QE res z hv hc _ h1 h0 hsh hky hqe hrs hq0 hk hkc _ henc hwd hq2 hrec hrc
  have hy : CHyp C a s w SH KY QE res z := ⟨hc, h1, h0, hsh, hky, hqe, hrs, hq0, henc, hwd, hq2, hrec⟩
  set H1 := 2 ^ ((s + 1) / 2) with hH1
  set H0 := 2 ^ (s / 2) with hH0
  have hHH : H1 * H0 = 2 ^ s := pow_split s
  have hH0p : 1 ≤ H0 := Nat.one_le_two_pow
  have hN1 : H1 < 2 ^ C.Wd := by rw [← h1]; exact hv.env_lt vH1
  have hN0 : H0 < 2 ^ C.Wd := by rw [← h0]; exact hv.env_lt vH0
  let Io : ℕ → DS VV MM → Prop := fun r e => CInv a s w SH KY QE res z (r * H0) e
  have hl := forS_spec' (C := C) u0 vH1 (by decide) (forS u1 vH0 oneP) a H1 hN1 Io (H0 * (10 * w + 33 + 4) + 4)
    (fun k e v he => he.set u0 v (by decide)) ⟨by simp only [hkc, Nat.zero_mul, List.drop_zero, hk], by simp, hrc, rfl,
      Frame.refl a⟩ h1 ?_
  · refine Hs.mono hl ?_ ?_
    · have : H1 ≤ 2 ^ s := by rw [← hHH]; exact Nat.le_mul_of_pos_right _ hH0p
      have e : H1 * (H0 * (10 * w + 33 + 4) + 4 + 4) = (H1 * H0) * (10 * w + 37) + 8 * H1 := by ring
      rw [e, hHH]; nlinarith
    · rintro b ⟨⟨b1, b2, b3, b4, b5⟩, _, _⟩
      have hlen : (printerOrder s).length ≤ H1 * H0 := by rw [printerOrder_length, hHH]
      refine ⟨by rw [b2, List.take_of_length_le hlen], b3, b4, b5⟩
  · intro r hr e he he0 he1
    let Ii : ℕ → DS VV MM → Prop := fun j f => CInv a s w SH KY QE res z (r * H0 + j) f ∧ f.env u0 = r
    have eH0 : e.env vH0 = H0 := by rw [he.2.2.2.2.env_lo vH0 (by decide)]; exact h0
    have hl2 := forS_spec' (C := C) u1 vH0 (by decide) oneP e H0 hN0 Ii (10 * w + 33)
      (fun k f v ⟨hf, hf0⟩ => ⟨hf.set u1 v (by decide), by rw [DS.set_env_ne _ _ (by decide)]; exact hf0⟩)
      ⟨he, he0⟩ eH0 ?_
    · refine Hs.mono hl2 le_rfl ?_
      rintro f ⟨⟨hf, hf0⟩, _, _⟩
      refine ⟨?_, hf0, ?_⟩
      · show CInv a s w SH KY QE res z ((r + 1) * H0) f
        rw [show (r + 1) * H0 = r * H0 + H0 by ring]; exact hf
      · rw [hf.2.2.2.2.env_lo vH1 (by decide)]; exact h1
    · intro j hj f ⟨hf, hf0⟩ hf1 hfm
      refine Hs.mono (oneP_spec C a s w SH KY QE res z hy r j hr hj f hf hf0 hf1) le_rfl ?_
      rintro g ⟨g1, g2, g3⟩
      exact ⟨⟨g1, g2⟩, g3, by rw [g1.2.2.2.2.env_lo vH0 (by decide)]; exact h0⟩

attribute [irreducible] convP

end NearCubicGates.Close.CounterMachine.CellTables
