import Proof.Gates.Cells.Pre1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

theorem drop_inj {α : Type} (L : List α) (x y : ℕ) (hx : x ≤ L.length) (hy : y ≤ L.length)
    (h : L.drop x = L.drop y) : x = y := by
  have := congrArg List.length h
  simp only [List.length_drop] at this
  omega

theorem nmem_sub {y : Fin VV} {L1 L2 : List (Fin VV)} (h : ∀ x ∈ L1, x ∈ L2) (hy : y ∉ L2) : y ∉ L1 :=
  fun h1 => hy (h y h1)

def walkCall : St VV MM :=
  .seq (.op (.rwM sN)) (.seq (.op (.zero wPos)) (.seq (skK 2) (.seq (circW vTS0 vTW0) (.seq (.op (.copy gB1 wPos))
  (.seq (circW vTS1 vTW1) (.seq (rdW gPL) (.seq (.op (.copy gPar wPos)) (.seq (.op (.copy wY gPL))
  (.seq skW (skK 3))))))))))

def walkCallT : List (Fin VV) := [wG, wY, wC, wTb, wPos, c0, vJ, vTS0, vTW0, gB1, vTS1, vTW1, gPL, gPar]

theorem cellN_call (c : Call) (p : Params) (wt : Wit c.n) : cellN c p wt = [c.n, kindTag c.kind] ++
    (circN c.first ++ (circN c.second ++ (c.parity.length :: (c.parity ++ (ratN c.radius ++
    (paramsN p ++ witN c p wt)))))) := by
  simp [cellN, callN, List.append_assoc]

theorem walkCall_spec {B1 B2 : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
    (a : DS VV MM) (hc : Cst a) (hN : a.ram sN = cellN c p wt) (hS : a.env gS = 2 * c.n + 3)
    (hW : (cellN c p wt).length + 2 * c.n + 10 < 2 ^ C.Wd) :
    Hs C walkCall a (a.rc sN + 25 * (cellN c p wt).length + 400) (fun d =>
      WSt (cellN c p wt) d (iPsi (cellN c p wt)) (paramsN p ++ witN c p wt) ∧
      (cellN c p wt).drop (d.env vTS0) = (circ c 0).table.map bitN ++
        (cellN c p wt).drop (d.env vTS0 + (circ c 0).table.length) ∧
      (cellN c p wt).drop (d.env vTS1) = (circ c 1).table.map bitN ++
        (cellN c p wt).drop (d.env vTS1 + (circ c 1).table.length) ∧
      d.env vTW0 = (circ c 0).topWeight ∧ d.env vTW1 = (circ c 1).topWeight ∧
      d.env gB1 = iG2 (cellN c p wt) ∧ d.env gPL = c.parity.length ∧ d.env gPar = iPar (cellN c p wt) + 1 ∧
      Agr a d [sN] walkCallT) := by
  have hsp := cellN_call c p wt
  have hwf1 := circ_wf c hadm 0
  have hwf2 := circ_wf c hadm 1
  have hc0 : circ c 0 = c.first := by simp [circ]
  have hc1 : circ c 1 = c.second := by simp [circ]
  rw [hc0] at hwf1 ⊢; rw [hc1] at hwf2 ⊢
  have hlen := congrArg List.length hsp
  simp only [List.length_append, List.length_cons, List.length_nil, ratN_length] at hlen
  have hT1 : 1 ≤ c.first.table.length := by rw [hwf1.2.2.1]; omega
  have hT2 : 1 ≤ c.second.table.length := by rw [hwf2.2.2.1]; omega
  -- rewind, start
  refine Hs.bseq (hs_rwM C sN a) (by omega) (fun e1 he1 => ?_)
  subst he1
  refine Hs.bseq (hs_zero C wPos _) (by omega) (fun e2 he2 => ?_)
  subst he2
  have ag2 : Agr a ((a.rew sN).set wPos 0) [sN] walkCallT :=
    (Agr.rew a (by simp) _).trans (Agr.set _ _ _ (by simp [walkCallT]))
  have w2 : WSt (cellN c p wt) ((a.rew sN).set wPos 0) 0 ([c.n, kindTag c.kind] ++ (circN c.first ++
      (circN c.second ++ (c.parity.length :: (c.parity ++ (ratN c.radius ++ (paramsN p ++ witN c p wt))))))) :=
    ⟨by simp [DS.rew, hN], by simp [DS.rew], by simp, by rw [← hsp]; simp, by simp⟩
  refine Hs.bseq (skK_spec (C := C) 2 _ _ 0 _ _ w2 rfl (by omega)) (by omega) (fun e3 ⟨w3, a3⟩ => ?_)
  have ag3 := ag2.trans (a3.weaken (by simp) (by decide))
  have c3 : Cst e3 := Cst.of_fr hc ag3.fr (by decide)
  -- first circuit
  have hc4 := circW_spec (C := C) vTS0 vTW0 (by decide) (by decide) _ e3 _ c.first _ w3 c3
    (by rw [ag3.fr gS (by decide), hS]) hT1 (by omega)
  refine Hs.bseq (Hs.mono hc4 le_rfl (fun _ h => h)) (by omega) (fun e4 ⟨w4, t4, v4, d4, a4⟩ => ?_)
  have ag4 := ag3.trans (a4.weaken (by simp) (by decide))
  refine Hs.bseq (hs_copy C gB1 wPos e4 (by decide)) (by omega) (fun e5 he5 => ?_)
  subst he5
  have w5 : WSt (cellN c p wt) (e4.set gB1 (e4.env wPos)) (0 + 2 + (circN c.first).length) (circN c.second ++
      (c.parity.length :: (c.parity ++ (ratN c.radius ++ (paramsN p ++ witN c p wt))))) :=
    ⟨w4.ram, w4.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact w4.pv, w4.dr, w4.le⟩
  have ag5 := ag4.trans (Agr.set e4 [sN] (e4.env wPos) (show gB1 ∈ walkCallT by simp [walkCallT]))
  have c5 : Cst (e4.set gB1 (e4.env wPos)) := Cst.of_fr hc ag5.fr (by decide)
  -- second circuit
  have hc6 := circW_spec (C := C) vTS1 vTW1 (by decide) (by decide) _ _ _ c.second _ w5 c5
    (by rw [ag5.fr gS (by decide), hS]) hT2 (by omega)
  refine Hs.bseq (Hs.mono hc6 le_rfl (fun _ h => h)) (by omega) (fun e6 ⟨w6, t6, v6, d6, a6⟩ => ?_)
  have ag6 := ag5.trans (a6.weaken (by simp) (by decide))
  -- the parity list and the radius
  refine Hs.bseq (rdW_spec (C := C) gPL (by decide) _ e6 _ _ _ w6 (by omega)) (by omega)
    (fun e7 ⟨u7, w7, a7⟩ => ?_)
  have ag7 := ag6.trans (a7.weaken (by simp) (by decide))
  refine Hs.bseq (hs_copy C gPar wPos e7 (by decide)) (by omega) (fun e8 he8 => ?_)
  subst he8
  refine Hs.bseq (hs_copy C wY gPL _ (by decide)) (by omega) (fun e9 he9 => ?_)
  subst he9
  have w9 : WSt (cellN c p wt) ((e7.set gPar (e7.env wPos)).set wY ((e7.set gPar (e7.env wPos)).env gPL))
      (0 + 2 + (circN c.first).length + (circN c.second).length + 1) (c.parity ++ (ratN c.radius ++
      (paramsN p ++ witN c p wt))) :=
    ⟨w7.ram, w7.rc, by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact w7.pv, w7.dr, w7.le⟩
  have hsk := skW_spec (C := C) _ _ _ _ _ w9 (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), u7]) (by omega)
  refine Hs.bseq hsk (by omega) (fun e10 ⟨w10, _, a10⟩ => ?_)
  refine Hs.mono (skK_spec (C := C) 3 _ e10 _ (ratN c.radius) _ w10 (ratN_length _) (by omega)) (by omega) ?_
  rintro d ⟨wd, ad⟩
  have agd : Agr a d [sN] walkCallT := ag7.trans ((Agr.set _ _ _ (by simp [walkCallT])).trans
    ((Agr.set _ _ _ (by simp [walkCallT])).trans ((a10.weaken (by simp) (by decide)).trans
      (ad.weaken (by simp) (by decide)))))
  -- positions as layout indices
  have hpsi : 0 + 2 + (circN c.first).length + (circN c.second).length + 1 + c.parity.length + 3 =
      iPsi (cellN c p wt) := by
    apply drop_inj (cellN c p wt) _ _ wd.le
    · have := drop_eq_len (lay c p wt).params (by simp [paramsN]); omega
    · rw [wd.dr, (lay c p wt).params]
  have hpar : iPsi (cellN c p wt) = iPar (cellN c p wt) + 4 + c.parity.length := by
    rw [← (lay c p wt).par]; rfl
  have hg2 : 0 + 2 + (circN c.first).length = iG2 (cellN c p wt) := by
    apply drop_inj (cellN c p wt) _ _ w5.le
    · have := drop_eq_len (Call.drop_iG2 c p wt) (by simp [circN]); omega
    · rw [w5.dr, Call.drop_iG2]; simp [List.append_assoc]
  have hfr7 : ∀ y, y ∉ [wY, c0, vJ, wPos, gPar] → d.env y = e7.env y := by
    intro y hy
    have h1 : y ≠ wY := fun h => hy (by rw [h]; decide)
    have h2 : y ≠ gPar := fun h => hy (by rw [h]; decide)
    rw [ad.fr y (nmem_sub (by decide) hy), a10.fr y (nmem_sub (by decide) hy), DS.set_env_ne _ _ h1,
      DS.set_env_ne _ _ h2]
  have hfr6 : ∀ y, y ∉ [wY, c0, vJ, wPos, gPar, gPL] → d.env y = e6.env y := by
    intro y hy
    rw [hfr7 y (nmem_sub (by decide) hy), a7.fr y (nmem_sub (by decide) hy)]
  have hfr4 : ∀ y, y ∉ [wY, c0, vJ, wPos, gPar, gPL, wG, wC, wTb, vTS1, vTW1, gB1] → d.env y = e4.env y := by
    intro y hy
    have h1 : y ≠ gB1 := fun h => hy (by rw [h]; decide)
    rw [hfr6 y (nmem_sub (by decide) hy), a6.fr y (nmem_sub (by decide) hy), DS.set_env_ne _ _ h1]
  have hsp' : ∀ (x : ℕ) (A R : List ℕ), (cellN c p wt).drop x = A ++ R →
      (cellN c p wt).drop x = A ++ (cellN c p wt).drop (x + A.length) := by
    intro x A R h; rw [drop_split h]; exact h
  refine ⟨by rw [← hpsi]; exact wd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, agd⟩
  · rw [hfr4 vTS0 (by decide)]; have := hsp' _ _ _ d4; rw [List.length_map] at this; exact this
  · rw [hfr6 vTS1 (by decide)]; have := hsp' _ _ _ d6; rw [List.length_map] at this; exact this
  · rw [hfr4 vTW0 (by decide), v4, hwf1.2.2.1]; unfold NCircuit.topWeight; omega
  · rw [hfr6 vTW1 (by decide), v6, hwf2.2.2.1]; unfold NCircuit.topWeight; omega
  · rw [hfr6 gB1 (by decide), a6.fr gB1 (by decide), DS.set_env_self, w4.pv, ← hg2]
  · rw [hfr7 gPL (by decide), u7]
  · rw [ad.fr gPar (by decide), a10.fr gPar (by decide), DS.set_env_ne _ _ (by decide), DS.set_env_self, w7.pv]
    omega

end NearCubicGates.Close.Cells
