import Proof.Gates.CellsGatherE.Emit1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

def cntB : St VV MM :=
  .seq (.op (.copy eIdx vIPr)) (.seq (.op (.add eIdx eI)) (.seq (fetch sN eIdx eQ) (.seq (.op (.copy ePw v1))
  (.seq (CounterMachine.CellTablesProg.powP ePw eQ eI2 eD eT2) (.op (.add eS ePw))))))

def cntE : St VV MM :=
  .seq (.op (.zero eS)) (.seq (forS eI vNP cntB) (.seq (.op (.mul ePar eS eR)) (.seq (.op (.copy eA gJ))
  (.seq (.op (.inc eA)) (.seq (.op (.mul gRC eA eB)) (.op (.add eR eB)))))))

def cntT : List (Fin VV) := [eS, eI, eIdx, eQ, ePw, eI2, eT2, eR, eA, eB, c0, vJ]

theorem take_succ_sum (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (L.take (k + 1)).sum = (L.take k).sum + L[k] := by
  rw [List.take_add_one, List.sum_append]; simp [List.getElem?_eq_getElem hk]

theorem cnt_spec (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) (hc : Cst a) (hcv : CV c p a)
    (hN : a.ram sN = CounterMachine.cellN c p wt) (hNP : a.env vNP = (p.primes.sort (· ≤ ·)).length)
    (hIPr : (CounterMachine.cellN c p wt).drop (a.env vIPr) = p.primes.sort (· ≤ ·) ++
      (CounterMachine.cellN c p wt).drop (a.env vIPr + (p.primes.sort (· ≤ ·)).length))
    (hJ : a.env gJ = p.J) (hrc : a.env gRC = roleCount c.kind) (hrcN : ∀ m, a.rc m ≤ (a.ram m).length)
    (hq2 : ∀ q ∈ p.primes, 2 ≤ q)
    (hR : (reqIds c p).length < 2 ^ C.Wd) (hNL : (CounterMachine.cellN c p wt).length < 2 ^ C.Wd) :
    Hs C cntE a ((p.primes.sort (· ≤ ·)).length * (6 * (CounterMachine.cellN c p wt).length +
        7 * CounterMachine.CellTablesProg.dOf c p + 40) + 30)
      (fun e => e.env eR = (reqIds c p).length ∧ Kp a e ∧ Fr a e cntT ∧ Cst e ∧ (∀ m, e.rc m ≤ (e.ram m).length)) := by
  set L := p.primes.sort (· ≤ ·) with hL
  set D := CounterMachine.CellTablesProg.dOf c p with hD
  have hlen := reqIds_length c p
  rw [← hL, ← hD] at hlen
  have hq1 : ∀ q ∈ L, 1 ≤ q := fun q hq => by have := hq2 q ((Finset.mem_sort _).mp hq); omega
  have hpar : 1 ≤ (parts c).length := by unfold parts; split <;> simp
  have hsumle : (L.map (fun q => q ^ D)).sum ≤ (reqIds c p).length := by rw [hlen]; nlinarith
  have hLle : L.length ≤ (CounterMachine.cellN c p wt).length := by
    have h1 := congrArg List.length hIPr
    rw [List.length_drop, List.length_append] at h1
    omega
  have hRJ : (parts c).length * (L.map (fun q => q ^ D)).sum + roleCount c.kind * (p.J + 1) < 2 ^ C.Wd := by
    rw [← hlen]; exact hR
  have hJ1 : p.J + 1 ≤ roleCount c.kind * (p.J + 1) := Nat.le_mul_of_pos_left _ (roleCount_pos _)
  have hLW : L.length < 2 ^ C.Wd := lt_of_le_of_lt hLle hNL
  apply Hx.hs
  refine Hs.then (hs_zero C eS a) (fun b1 hb1 n1 hn1 => ?_); subst hb1
  -- the loop
  let I : ℕ → DS VV MM → Prop := fun k d => d.env eS = ((L.take k).map (fun q => q ^ D)).sum ∧ Kp a d ∧
    Fr a d cntT ∧ Cst d ∧ (∀ m, d.rc m ≤ (d.ram m).length)
  have hloop := CounterMachine.PrefixProg.forS_specV (C := C) eI vNP (by decide) cntB (a.set eS 0) L.length hLW I
    (6 * (CounterMachine.cellN c p wt).length + 7 * D + 30)
    (fun k d v hv ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      i2.trans (Kp.of_same (Same.set _ _ _)), Fr.trans i3 (Fr.set d v (by decide)),
      cst_of i4 (Fr.set d v (show eI ∈ [eI] by simp)) (by decide), i5⟩)
    ⟨by simp, Kp.of_same (Same.set _ _ _), Fr.set a 0 (by decide),
      cst_of hc (Fr.set a 0 (show eS ∈ [eS] by simp)) (by decide), hrcN⟩
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hNP) ?_
  · refine Hs.then hloop (fun b2 ⟨⟨i1, i2, i3, i4, i5⟩, _, _⟩ n2 hn2 => ?_)
    rw [List.take_of_length_le le_rfl] at i1
    have g2 : ∀ y, y ∉ cntT → b2.env y = a.env y := fun y hy => i3 y hy
    refine Hs.then (hs_mul C ePar eS eR b2 (by decide) (by decide) (by decide)
      (by rw [i1, g2 ePar (by decide), hcv.par]; omega)) (fun b3 hb3 n3 hn3 => ?_); subst hb3
    refine Hs.then (hs_copy C eA gJ _ (by decide)) (fun b4 hb4 n4 hn4 => ?_); subst hb4
    refine Hs.then (hs_inc C eA _ (by vsimp [g2 gJ (by decide), hJ] <;> omega))
      (fun b5 hb5 n5 hn5 => ?_); subst hb5
    refine Hs.then (hs_mul C gRC eA eB _ (by decide) (by decide) (by decide)
      (by vsimp [g2 gJ (by decide), g2 gRC (by decide), hJ, hrc] <;> omega))
      (fun b6 hb6 n6 hn6 => ?_); subst hb6
    refine Hs.last (hs_add C eR eB _ (by decide)
      (by vsimp [g2 gJ (by decide), g2 gRC (by decide), g2 ePar (by decide), hJ, hrc, hcv.par, i1] <;> omega))
      (fun b7 hb7 n7 hn7 => ?_); subst hb7
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · vsimp [g2 gJ (by decide), g2 gRC (by decide), g2 ePar (by decide), hJ, hrc, hcv.par, i1, hlen] <;> ring
    · exact i2.trans (Kp.of_same ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans
        ((Same.set _ _ _).trans (Same.set _ _ _))))))
    · exact Fr.trans i3 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans
        (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))))
    · exact ⟨by vsimp [i4.z], by vsimp [i4.one], by vsimp [i4.two]⟩
    · intro m; simp only [DS.set]; exact i5 m
    · nlinarith
  · intro k hk d ⟨i1, i2, i3, i4, i5⟩ hdk hdm
    have gd : ∀ y, y ∉ cntT → d.env y = a.env y := fun y hy => i3 y hy
    have hqk : L[k] ∈ L := List.getElem_mem hk
    have hqD : L[k] ^ D ≤ (L.map (fun q => q ^ D)).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨_, hqk, rfl⟩)
    have hpart : ((L.take (k + 1)).map (fun q => q ^ D)).sum ≤ (L.map (fun q => q ^ D)).sum := by
      have := congrArg (fun l => (l.map (fun q => q ^ D)).sum) (List.take_append_drop (k + 1) L)
      simp only [List.map_append, List.sum_append] at this; omega
    have htk : ((L.take (k + 1)).map (fun q => q ^ D)).sum = ((L.take k).map (fun q => q ^ D)).sum + L[k] ^ D := by
      rw [List.take_add_one, List.map_append, List.sum_append]; simp [List.getElem?_eq_getElem hk]
    obtain ⟨hget, hlt⟩ := SystemsPhase.drop_getD hIPr k hk
    apply Hx.hs
    refine Hs.then (hs_copy C eIdx vIPr d (by decide)) (fun e1 he1 m1 hm1 => ?_); subst he1
    refine Hs.then (hs_add C eIdx eI _ (by decide) (by vsimp [gd vIPr (by decide), hdk] <;> omega))
      (fun e2 he2 m2 hm2 => ?_); subst he2
    have hix : (L.getD k 0) = L[k] := by rw [List.getD_eq_getElem _ _ hk]
    have hvi : (((d.set eIdx (d.env vIPr)).set eIdx ((d.set eIdx (d.env vIPr)).env eIdx +
        (d.set eIdx (d.env vIPr)).env eI)).env eIdx) = a.env vIPr + k := by vsimp [gd vIPr (by decide), hdk]
    have hram2 : ((d.set eIdx (d.env vIPr)).set eIdx ((d.set eIdx (d.env vIPr)).env eIdx +
        (d.set eIdx (d.env vIPr)).env eI)).ram sN = CounterMachine.cellN c p wt := by
      simp only [DS.set]; rw [i2.ram, hN]
    refine Hs.then (o_fetch sN eIdx eQ (by decide) (by decide) (by decide) _ (by rw [hvi, hram2]; exact hlt)
      (by rw [hvi]; omega)) (fun e3 ⟨v3, f3, k3, r3⟩ m3 hm3 => ?_)
    rw [hvi, hram2, hget, hix] at v3
    have c3 : Cst e3 := cst_of (cst_of (cst_of i4 (Fr.set d _ (show eIdx ∈ [eIdx] by simp)) (by decide))
      (Fr.set _ _ (show eIdx ∈ [eIdx] by simp)) (by decide)) f3 (by decide)
    refine Hs.then (hs_copy C ePw v1 e3 (by decide)) (fun e4 he4 m4 hm4 => ?_); subst he4
    have e4D : (e3.set ePw (e3.env v1)).env eD = D := by
      rw [DS.set_env_ne _ _ (by decide), f3 eD (by decide)]; vsimp [gd eD (by decide), hcv.d, ← hD]
    have hDW : D < 2 ^ C.Wd := by
      have : D ≤ (reqIds c p).length := by rw [hlen]; have := Nat.le_mul_of_pos_left (roleCount c.kind * (p.J + 1))
                                                  hpar; unfold D CounterMachine.CellTablesProg.dOf; omega
      omega
    refine Hs.then (CounterMachine.CellTablesProg.powP_spec C ePw eQ eI2 eD eT2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) _ D 1 L[k] e4D (by vsimp [c3.one])
      (by rw [DS.set_env_ne _ _ (by decide)]; exact v3) hDW (by omega)) (fun e5 ⟨v5, s5, f5⟩ m5 hm5 => ?_)
    have e5S : e5.env eS = ((L.take k).map (fun q => q ^ D)).sum := by
      rw [f5 eS (by decide), DS.set_env_ne _ _ (by decide), f3 eS (by decide)]; vsimp [i1]
    refine Hs.last (hs_add C eS ePw e5 (by decide) (by rw [e5S, v5]; omega)) (fun e6 he6 m6 hm6 => ?_)
    subst he6
    have sh5 : e5.ram = e3.ram ∧ e5.rc = e3.rc ∧ e5.ip = e3.ip ∧ e5.out = e3.out ∧ e5.kin = e3.kin ∧
        e5.kout = e3.kout ∧ e5.kc = e3.kc := by
      simp only [DS.sh, Prod.mk.injEq, DS.set] at s5; exact ⟨s5.2.2.1, s5.2.2.2.1, s5.1, s5.2.1, s5.2.2.2.2.1,
        s5.2.2.2.2.2.1, s5.2.2.2.2.2.2⟩
    have gfr : Fr d e5 cntT := Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.weaken f3 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken f5 (by decide)))))
    have hfr6 : Fr d ((e5.set eS (e5.env eS + e5.env ePw))) [eIdx, c0, vJ, eQ, ePw, eI2, eT2, eS] :=
      Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken f3 (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken f5 (by decide)) (Fr.set _ _ (by decide))))))
    have hrcd := i5 sN
    rw [i2.ram, hN] at hrcd
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [DS.set_env_self, e5S, v5, htk]; ring
    · refine i2.trans ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [DS.set]
      · rw [sh5.2.2.1]; exact k3.ip
      · rw [sh5.2.2.2.1]; exact k3.out
      · rw [sh5.1]; exact k3.ram
      · rw [sh5.2.2.2.2.1]; exact k3.kin
      · rw [sh5.2.2.2.2.2.1]; exact k3.kout
      · rw [sh5.2.2.2.2.2.2]; exact k3.kc
      · rw [sh5.2.1]; exact k3.rcA
    · exact Fr.trans i3 (Fr.weaken hfr6 (by decide))
    · exact cst_of c3 (T := [ePw, eI2, eT2, eS]) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken f5 (by decide))
        (Fr.set _ _ (by decide)))) (by decide)
    · intro m; simp only [DS.set]; rw [sh5.2.1, sh5.1, r3, k3.ram]
      by_cases hm : m = sN
      · subst hm; simp only [Function.update_self]; rw [hvi]; simp only [DS.set]; rw [i2.ram, hN]; omega
      · rw [Function.update_of_ne hm]; exact i5 m
    · rw [hfr6 eI (by decide)]; exact hdk
    · rw [hfr6 vNP (by decide)]; exact hdm
    · have h3' : m3 ≤ d.rc sN + 5 * (a.env vIPr + k) + 9 := by rw [hvi] at hm3; exact hm3
      omega

end NearCubicGates.Close.Cells.RecordEmission
