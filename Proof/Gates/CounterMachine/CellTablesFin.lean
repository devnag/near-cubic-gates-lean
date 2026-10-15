import Proof.Gates.CounterMachine.CellTablesLem

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTables

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP frame_eq_frameP)

/-- Scratch variables of `finP` (all in `scr`). -/
def f0 : Fin VV := ⟨48, by decide⟩   -- the sentinel `2^RW`
def f1 : Fin VV := ⟨49, by decide⟩   -- bit counter
def f2 : Fin VV := ⟨50, by decide⟩   -- the current record
def f3 : Fin VV := ⟨51, by decide⟩   -- the bits not printed yet
def f4 : Fin VV := ⟨52, by decide⟩   -- quotient
def f5 : Fin VV := ⟨53, by decide⟩   -- the bit

/-- One data bit: the marker, then the low bit of `f3`; `f3` is halved. -/
def bitE : St VV MM :=
  .seq (.op (.emit true)) (.seq (.op (.dm f3 v2 f4 f5)) (.seq (emitV f5) (.op (.copy f3 f4))))

/-- Print `frame (binary RW f2)`. -/
def emRec : St VV MM := .seq (.op (.copy f3 f2)) (.seq (forS f1 vRW bitE) (.op (.emit false)))

def finP : St VV MM :=
  .seq (.op (.copy f0 v1)) (.seq (forS f1 vRW (.op (.shl f0))) (.seq (.op (.wrM sREC f0))
    (.seq (.op (.rwM sREC)) (.seq (.op (.srtM sREC)) (.seq (.op (.rdM sREC f2))
      (.seq (.loop (.lt f2 f0) (.seq emRec (.op (.rdM sREC f2)))) (.op (.emit false))))))))

theorem frameP_append (u v : List Bool) : frameP (u ++ v) = frameP u ++ frameP v := by
  simp [frameP, List.flatMap_append]

theorem bitE_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (hW : 2 ≤ C.Wd) :
    Hs C bitE b 8 (fun d => d.out = b.out ++ [true, decide (b.env f3 % 2 = 1)] ∧ d.env f3 = b.env f3 / 2 ∧
      Fr b d [f3, f4, f5] ∧ SameO b d) := by
  have h4 : 2 * 2 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  refine Hs.seq (t1 := 1) (t2 := 6) (hs_emit C true b) (fun d hd => ?_)
  subst hd
  have dv2 : ({ b with out := b.out ++ [true] } : DS VV MM).env v2 = 2 := hc.two
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_dm C f3 v2 f4 f5 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [dv2]; norm_num) (by rw [dv2]; exact h4)) (fun e he => ?_)
  subst he
  rw [dv2]
  set d : DS VV MM := { b with out := b.out ++ [true] } with hd
  set e := (d.set f4 (d.env f3 / 2)).set f5 (d.env f3 % 2) with he
  have ec : Cst e := ⟨by rw [he]; vsimp [hd, hc.z], by rw [he]; vsimp [hd, hc.one], by rw [he]; vsimp [hd, hc.two]⟩
  refine Hs.seq (t1 := 2) (t2 := 1) (emitV_spec C f5 (by decide) e ec) (fun g hg => ?_)
  subst hg
  refine Hs.mono (hs_copy C f3 f4 _ (by decide)) le_rfl ?_
  rintro r rfl
  have e5 : e.env f5 = b.env f3 % 2 := by rw [he]; vsimp [hd]
  have e4 : e.env f4 = b.env f3 / 2 := by rw [he]; vsimp [hd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [DS.set_out, e5]; rw [he]; simp [hd]
  · vsimp [e4]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h3, h4', h5⟩ := hy
    simp only [DS.set, Function.update_apply, if_neg h3]
    rw [he]; simp only [DS.set, Function.update_apply, if_neg h4', if_neg h5, hd]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem emRec_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (RW : ℕ) (hRW : b.env vRW = RW) (hN : RW < 2 ^ C.Wd)
    (hW : 2 ≤ C.Wd) :
    Hs C emRec b (12 * RW + 8) (fun d => d.out = b.out ++ frame (binary RW (b.env f2)) ∧
      Fr b d [f1, f3, f4, f5] ∧ SameO b d) := by
  set x := b.env f2 with hx
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 12 * RW + 6) (hs_copy C f3 f2 b (by decide)) (fun b1 hb1 => ?_))
    (by omega) (fun _ h => h)
  subst hb1
  let I : ℕ → DS VV MM → Prop := fun k d => d.out = b.out ++ frameP (binary k x) ∧ d.env f3 = x / 2 ^ k ∧
    Fr b d [f1, f3, f4, f5] ∧ SameO b d
  have hl := forS_spec' (C := C) f1 vRW (by decide) bitE (b.set f3 x) RW hN I 8
    (fun k d v ⟨h1, h2, h3, h4⟩ => ⟨h1, by rw [DS.set_env_ne _ _ (by decide)]; exact h2,
      Fr.trans h3 (Fr.set d v (by decide)), h4.trans (SameO.set _ _ _)⟩)
    ⟨by simp [binary, frameP], by simp, Fr.set b x (by decide), SameO.set _ _ _⟩
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hRW) ?_
  · refine Hs.mono (Hs.seq (t1 := RW * (8 + 4) + 4) (t2 := 1) (Hs.mono hl le_rfl (fun _ h => h))
      (fun d ⟨⟨h1, _, h3, h4⟩, _, _⟩ => ?_)) (by omega) (fun _ h => h)
    refine Hs.mono (hs_emit C false d) le_rfl ?_
    rintro e rfl
    refine ⟨?_, h3, h4.trans (SameO.out _ _)⟩
    simp only [h1, frame_eq_frameP, List.append_assoc]
  · intro k hk d ⟨h1, h2, h3, h4⟩ hdk hdm
    have dc : Cst d := Cst.of_fr hc h3 (by decide)
    refine Hs.mono (bitE_spec C d dc hW) le_rfl ?_
    rintro e ⟨e1, e2, e3, e4⟩
    refine ⟨⟨?_, ?_, Fr.trans h3 (Fr.weaken e3 (by decide)), h4.trans e4⟩, ?_, ?_⟩
    · rw [e1, h1, h2, binary_snoc, frameP_append, List.append_assoc]
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [frameP, h]
    · rw [e2, h2, Nat.div_div_eq_div_mul, pow_succ]
    · rw [e3 f1 (by decide)]; exact hdk
    · rw [e3 vRW (by decide)]; exact hdm

theorem finP_spec : FinSpec finP := by
  intro C a RW recs hv hc hRW h1 hWd hram hrc hlt
  have hW : 2 ≤ C.Wd := by omega
  have hpw : 2 ^ (RW + 2) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hWd
  have hS : 2 ^ RW < 2 ^ C.Wd := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) hpw
  have hN : RW < 2 ^ C.Wd := lt_trans Nat.lt_two_pow_self hS
  set S := 2 ^ RW with hSdef
  set sorted := recs.insertionSort (· ≤ ·) with hsorted
  set L := sorted ++ [S] with hL
  have hslen : sorted.length = recs.length := (List.perm_insertionSort _ _).length_eq
  have hmem : ∀ v ∈ sorted, v < S := fun v hv => hlt v ((List.perm_insertionSort _ _).mem_iff.mp hv)
  set N := recs.length with hNdef
  refine Hs.mono (t := (1 + (RW * (1 + 4) + 4 + (1 + (N + 1 + 1 + (N + 1 + 1 + (1 + ((N * (12 * RW + 10 + 2) + 2) + 1 + 1) + 1) + 1) + 1) + 1) + 1) + 1)) ?_ (by nlinarith) (fun _ h => h)
  -- the sentinel
  refine Hs.seq (t1 := 1) (t2 := (RW * (1 + 4) + 4 + (1 + (N + 1 + 1 + (N + 1 + 1 + (1 + ((N * (12 * RW + 10 + 2) + 2) + 1 + 1) + 1) + 1) + 1) + 1) + 1)) (hs_copy C f0 v1 a (by decide)) (fun a1 ha1 => ?_)
  subst ha1
  rw [hc.one]
  let I0 : ℕ → DS VV MM → Prop := fun k d => d.env f0 = 2 ^ k ∧ Fr a d [f0, f1] ∧ Same a d
  have hl0 := forS_spec' (C := C) f1 vRW (by decide) (.op (.shl f0)) (a.set f0 1) RW hN I0 1
    (fun k d v ⟨h1, h2, h3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact h1,
      Fr.trans h2 (Fr.set d v (by decide)), h3.trans (Same.set _ _ _)⟩)
    ⟨by simp, Fr.set a 1 (by decide), Same.set _ _ _⟩ (by rw [DS.set_env_ne _ _ (by decide)]; exact hRW) (by
      intro k hk d ⟨h1, h2, h3⟩ hdk hdm
      have hk2 : 2 * 2 ^ k < 2 ^ C.Wd := by
        rw [← pow_succ']; exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hk) hS
      refine Hs.mono (hs_shl C f0 d (by rw [h1]; exact hk2)) le_rfl ?_
      rintro e rfl
      refine ⟨⟨by vsimp [h1]; ring, Fr.trans h2 (Fr.set d _ (by decide)), h3.trans (Same.set _ _ _)⟩, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ (by decide)]; exact hdk
      · rw [DS.set_env_ne _ _ (by decide)]; exact hdm)
  refine Hs.seq (t1 := RW * (1 + 4) + 4) (t2 := (1 + (N + 1 + 1 + (N + 1 + 1 + (1 + ((N * (12 * RW + 10 + 2) + 2) + 1 + 1) + 1) + 1) + 1) + 1)) (Hs.mono hl0 le_rfl (fun _ h => h)) (fun d ⟨⟨d1, d2, d3⟩, _, _⟩ => ?_)
  have dlen : d.rc sREC ≤ (d.ram sREC).length := by rw [d3.rc, d3.ram, hram, hrc]
  -- append the sentinel
  refine Hs.seq (t1 := 1) (t2 := (N + 1 + 1 + (N + 1 + 1 + (1 + ((N * (12 * RW + 10 + 2) + 2) + 1 + 1) + 1) + 1) + 1)) (hs_wrM C sREC f0 d dlen) (fun d2' hd2 => ?_)
  subst hd2
  have r2 : (d.put sREC (d.env f0)).ram sREC = recs ++ [S] := by
    simp only [DS.put, Function.update_self, d1, d3.ram, hram]
    unfold putAt; rw [d3.rc, hrc, if_neg (lt_irrefl _)]
  -- rewind
  have rc3 : (d.put sREC (d.env f0)).rc sREC = N + 1 := by
    simp only [DS.put, Function.update_self, d3.rc, hrc]
  refine Hs.seq (t1 := N + 1 + 1) (t2 := (N + 1 + 1 + (1 + ((N * (12 * RW + 10 + 2) + 2) + 1 + 1) + 1) + 1)) (Hs.mono (hs_rwM C sREC _) (le_of_eq (by rw [rc3])) (fun _ h => h)) (fun d4 hd4 => ?_)
  subst hd4
  -- sort
  have len4 : ((d.put sREC (d.env f0)).rew sREC).ram sREC = recs ++ [S] := by simp only [DS.rew]; exact r2
  refine Hs.seq (t1 := N + 1 + 1) (t2 := (1 + ((N * (12 * RW + 10 + 2) + 2) + 1 + 1) + 1)) (Hs.mono (hs_srtM C sREC _ (by simp [DS.rew])) (le_of_eq (by rw [len4]; simp; rfl))
    (fun _ h => h)) (fun d5 hd5 => ?_)
  subst hd5
  set e0 := ((d.put sREC (d.env f0)).rew sREC).srt sREC with he0
  have e0ram : e0.ram sREC = L := by
    rw [he0]; simp only [DS.srt, Function.update_self, len4]
    exact insertionSort_sentinel recs S hlt
  have e0rc : e0.rc sREC = 0 := by rw [he0]; simp [DS.srt, DS.rew]
  have e0fr : Frame a e0 := by
    refine Frame.trans (Frame.of_sameO d2 (by decide) ⟨d3.ip, d3.ram, d3.rc, d3.kin, d3.kout, d3.kc⟩) ?_
    exact Frame.trans (Frame.put _ _) (Frame.trans (Frame.rew _) (Frame.srt _))
  have e0kc : e0.kc = a.kc := by rw [he0]; simp only [DS.srt, DS.rew, DS.put]; exact d3.kc
  have e0out : e0.out = a.out := by rw [he0]; simp only [DS.srt, DS.rew, DS.put]; exact d3.out
  have e0f0 : e0.env f0 = S := by rw [he0]; simp only [DS.srt, DS.rew, DS.put]; exact d1
  have hLlen : L.length = N + 1 := by rw [hL, List.length_append, hslen]; rfl
  -- first read
  refine Hs.seq (t1 := 1) (t2 := ((N * (12 * RW + 10 + 2) + 2) + 1 + 1)) (hs_rdM C sREC f2 e0 (by rw [e0rc, e0ram, hLlen]; omega)) (fun e1 he1 => ?_)
  subst he1
  -- the loop over the records
  let I : ℕ → DS VV MM → Prop := fun k g => g.out = a.out ++ ((sorted.take k).map (binary RW)).flatMap frame ∧
    g.ram sREC = L ∧ g.rc sREC = k + 1 ∧ g.env f2 = L.getD k 0 ∧ g.env f0 = S ∧ Frame a g ∧ g.kc = a.kc
  have hloop := Hs.loopN (C := C) (c := .lt f2 f0) (s := .seq emRec (.op (.rdM sREC f2))) (show f2 ≠ f0 by decide) I N
    (12 * RW + 10) ?_ ?_ ((e0.set f2 ((e0.ram sREC).getD (e0.rc sREC) 0)).adv sREC) ?_
  · refine Hs.seq (t1 := (N * (12 * RW + 10 + 2) + 2)) (t2 := 1) hloop (fun g ⟨g1, _, _, _, _, g6, g7⟩ => ?_)
    refine Hs.mono (hs_emit C false g) le_rfl ?_
    rintro r rfl
    refine ⟨?_, g7, g6.trans (Frame.out _ _)⟩
    simp only [g1, List.append_assoc, WordPrograms.recStream]
    rw [List.take_of_length_le (by omega)]
  · intro k hk g ⟨g1, g2, g3, g4, g5, g6, g7⟩
    have hkL : L.getD k 0 = sorted[k]'(by omega) := by
      rw [hL, List.getD_eq_getElem _ _ (by rw [List.length_append, hslen]; simp; omega),
        List.getElem_append_left]
    have hkS : sorted[k]'(by omega) < S := hmem _ (List.getElem_mem _)
    refine ⟨by simp only [Cnd.eval, g4, g5, hkL]; exact decide_eq_true hkS, ?_⟩
    have gc : Cst g := g6.cst hc
    have gRW : g.env vRW = RW := by rw [g6.env_lo vRW (by decide)]; exact hRW
    refine Hs.seq (t1 := 12 * RW + 8) (t2 := 1) (emRec_spec C g gc RW gRW hN hW) (fun h ⟨h1, h2, h3⟩ => ?_)
    have hrc' : h.rc sREC < (h.ram sREC).length := by rw [h3.rc, h3.ram, g3, g2, hLlen]; omega
    refine Hs.mono (hs_rdM C sREC f2 h hrc') le_rfl ?_
    rintro r rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [DS.adv, DS.set_out, h1, g1, g4, hkL, List.append_assoc]
      rw [take_succ_getElem sorted k _ (List.getElem?_eq_getElem (by omega)), List.map_append,
        List.flatMap_append]
      simp
    · simp only [DS.adv, DS.set_ram, h3.ram, g2]
    · simp only [DS.adv, DS.set_rc, Function.update_self, h3.rc, g3]
    · simp only [DS.adv]; vsimp [h3.ram, h3.rc, g2, g3]
    · simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), h2 f0 (by decide), g5]
    · exact g6.trans (Frame.trans (Frame.of_sameO h2 (by decide) h3)
        (Frame.trans (Frame.set _ _ _ (by decide)) (Frame.adv _)))
    · simp only [DS.adv, DS.set_kc, h3.kc, g7]
  · intro g ⟨_, _, _, g4, g5, _, _⟩
    have : L.getD N 0 = S := by
      rw [hL, List.getD_eq_getElem _ _ (by rw [List.length_append, hslen]; simp), List.getElem_append_right
        (by rw [hslen])]
      simp [hslen]
    simp only [Cnd.eval, g4, g5, this]; exact decide_eq_false (lt_irrefl S)
  · refine ⟨by simp only [DS.adv, DS.set_out, e0out, List.take_zero, List.map_nil, List.flatMap_nil,
      List.append_nil], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [DS.adv, DS.set_ram, e0ram]
    · simp only [DS.adv, DS.set_rc, Function.update_self, e0rc]
    · simp only [DS.adv]; vsimp [e0ram, e0rc]
    · simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), e0f0]
    · exact e0fr.trans (Frame.trans (Frame.set _ _ _ (by decide)) (Frame.adv _))
    · simp only [DS.adv, DS.set_kc, e0kc]

attribute [irreducible] finP

end NearCubicGates.Close.CounterMachine.CellTables
