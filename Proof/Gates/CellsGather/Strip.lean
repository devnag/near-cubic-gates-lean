import Proof.Gates.CellsGather.Sweep2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def stBody : St VV MM := .seq (.op (.rdM sA gx)) (.seq (.op (.dm gx p2VW gQ gR)) (.op (.wrM sG gR)))
def stripP : St VV MM := .seq (.op (.rwM sA)) (.seq (.op (.rwM sG)) (forS t0 gNQ stBody))
def cpBody : St VV MM := .seq (.op (.rdM sG gx)) (.op (.wrM sA gx))
def copyP : St VV MM := .seq (.op (.rwM sA)) (.seq (.op (.rwM sG)) (forS t0 gNQ cpBody))

def stT : List (Fin VV) := [t0, gx, gQ, gR]

theorem putAt_pre' (W S : List ℕ) (k v : ℕ) (hk : W.length = k) :
    putAt (W ++ S.drop k) k v = (W ++ [v]) ++ S.drop (k + 1) := by
  subst hk; exact putAt_pre W S v

variable {C : Ctx}

/-- The strip invariant after `k` records. -/
structure StI (VW : ℕ) (Ans G : List ℕ) (e : DS VV MM) (k : ℕ) (b : DS VV MM) : Prop where
  ramA : b.ram sA = Ans
  rcA : b.rc sA = k
  rcG : b.rc sG = k
  ramG : b.ram sG = (Ans.take k).map (· % 2 ^ VW) ++ G.drop k
  ramO : ∀ m, m ≠ sG → b.ram m = e.ram m
  fr : Fr e b stT
  ip : b.ip = e.ip
  out : b.out = e.out
  kin : b.kin = e.kin
  kout : b.kout = e.kout
  kc : b.kc = e.kc

theorem StI.set {VW : ℕ} {Ans G : List ℕ} {e : DS VV MM} {k : ℕ} {b : DS VV MM} (h : StI VW Ans G e k b) (v : ℕ) :
    StI VW Ans G e k (b.set t0 v) :=
  ⟨h.ramA, h.rcA, h.rcG, h.ramG, h.ramO, h.fr.trans (Fr.set b v (by decide)), h.ip, h.out, h.kin, h.kout, h.kc⟩

theorem stripP_spec (e : DS VV MM) (VW N : ℕ) (Ans G : List ℕ) (hA : e.ram sA = Ans) (hG : e.ram sG = G)
    (hN : Ans.length = N) (hNG : N ≤ G.length) (hq : e.env gNQ = N) (hv : e.env p2VW = 2 ^ VW)
    (hW1 : 2 * 2 ^ VW ≤ 2 ^ C.Wd) (hW2 : N < 2 ^ C.Wd) :
    Hs C stripP e (e.rc sA + e.rc sG + 9 * N + 8) (fun b =>
      b.ram sG = Ans.map (· % 2 ^ VW) ++ G.drop N ∧ b.ram sA = Ans ∧ (∀ m, m ≠ sG → b.ram m = e.ram m) ∧
      b.rc sA = N ∧ b.rc sG = N ∧ Fr e b stT ∧
      b.ip = e.ip ∧ b.out = e.out ∧ b.kin = e.kin ∧ b.kout = e.kout ∧ b.kc = e.kc) := by
  obtain ⟨s1, n1, e1, hn1, h1⟩ := hs_rwM C sA e
  subst h1
  obtain ⟨s2, n2, e2, hn2, h2⟩ := hs_rwM C sG (e.rew sA)
  subst h2
  have hrcG : (e.rew sA).rc sG = e.rc sG := by simp [DS.rew, Function.update_of_ne (by decide : sG ≠ sA)]
  have h0 : StI VW Ans G e 0 ((e.rew sA).rew sG) := by
    refine ⟨hA, ?_, ?_, by simp [DS.rew, hG], fun m _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [DS.rew, Function.update_of_ne (by decide : sA ≠ sG)]
    · simp [DS.rew]
  have hloop := forS_spec' (C := C) t0 gNQ (by decide) stBody ((e.rew sA).rew sG) N hW2 (StI VW Ans G e)
    5 (fun k b v h => h.set v) h0 hq ?_
  · obtain ⟨s3, n3, e3, hn3, hI, -, -⟩ := hloop
    refine ⟨s3, n1 + (n2 + n3 + 1) + 1, Ex.seq e1 (Ex.seq e2 e3), by rw [hrcG] at hn2; omega, ?_⟩
    refine ⟨by rw [hI.ramG, ← hN, List.take_length], hI.ramA, hI.ramO, hI.rcA, hI.rcG, hI.fr, hI.ip, hI.out,
      hI.kin, hI.kout, hI.kc⟩
  · intro k hk b hI hbk hbN
    have hkA : k < Ans.length := by omega
    have hr1 : b.rc sA < (b.ram sA).length := by rw [hI.rcA, hI.ramA]; exact hkA
    obtain ⟨s1, n1, e1, hn1, h1⟩ := hs_rdM C sA gx b hr1
    subst h1
    set b1 := (b.set gx ((b.ram sA).getD (b.rc sA) 0)).adv sA with hb1
    have hx1 : b1.env gx = Ans[k] := by
      rw [hb1]; simp only [DS.adv, DS.set, DS.env_set, Function.update_self]
      rw [hI.ramA, hI.rcA, List.getD_eq_getElem _ _ hkA]
    have hv1 : b1.env p2VW = 2 ^ VW := by
      rw [hb1]; simp only [DS.adv, DS.set, DS.env_set]; rw [Function.update_of_ne (by decide), hI.fr.ev (by decide), hv]
    obtain ⟨s2, n2, e2, hn2, h2⟩ := hs_dm C gx p2VW gQ gR b1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [hv1]; positivity) (by rw [hv1]; exact hW1)
    subst h2
    set b2 := (b1.set gQ (b1.env gx / b1.env p2VW)).set gR (b1.env gx % b1.env p2VW) with hb2
    have hlk : ((Ans.take k).map (· % 2 ^ VW)).length = k := by
      rw [List.length_map, List.length_take, Nat.min_eq_left (by omega)]
    have hb2rc : b2.rc = Function.update b.rc sA (k + 1) := by
      rw [hb2, hb1]; simp only [DS.adv, DS.set]; rw [hI.rcA]
    have hb2ram : b2.ram = b.ram := by rw [hb2, hb1]; rfl
    have hb2sh : b2.ip = b.ip ∧ b2.out = b.out ∧ b2.kin = b.kin ∧ b2.kout = b.kout ∧ b2.kc = b.kc := by
      rw [hb2, hb1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hb2env : ∀ y, y ≠ gx → y ≠ gQ → y ≠ gR → b2.env y = b.env y := by
      intro y h1 h2 h3
      rw [hb2, hb1]; simp only [DS.adv, DS.set, DS.env_set]
      rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    have hval : b2.env gR = Ans[k] % 2 ^ VW := by
      rw [hb2]; simp only [DS.set, DS.env_set, Function.update_self]; rw [hx1, hv1]
    have hrG2 : b2.rc sG = k := by rw [hb2rc, Function.update_of_ne (by decide : sG ≠ sA), hI.rcG]
    have hramG2 : b2.ram sG = (Ans.take k).map (· % 2 ^ VW) ++ G.drop k := by rw [hb2ram, hI.ramG]
    have hr2 : b2.rc sG ≤ (b2.ram sG).length := by rw [hrG2, hramG2]; simp; omega
    obtain ⟨s3, n3, e3, hn3, h3⟩ := hs_wrM C sG gR b2 hr2
    subst h3
    refine ⟨_, n1 + (n2 + n3 + 1) + 1, Ex.seq e1 (Ex.seq e2 e3), by omega, ?_⟩
    have htk : (Ans.take (k + 1)).map (· % 2 ^ VW) = (Ans.take k).map (· % 2 ^ VW) ++ [Ans[k] % 2 ^ VW] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkA, List.map_append]; rfl
    have hput : putAt ((Ans.take k).map (· % 2 ^ VW) ++ G.drop k) k (Ans[k] % 2 ^ VW) =
        (Ans.take (k + 1)).map (· % 2 ^ VW) ++ G.drop (k + 1) := by
      rw [htk, putAt_pre' _ _ _ _ hlk]
    refine ⟨⟨?_, ?_, ?_, ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [DS.put]; rw [Function.update_of_ne (by decide : sA ≠ sG), hb2ram]; exact hI.ramA
    · simp only [DS.put]; rw [Function.update_of_ne (by decide : sA ≠ sG), hb2rc, Function.update_self]
    · simp only [DS.put, Function.update_self]; rw [hrG2]
    · simp only [DS.put, Function.update_self]; rw [hramG2, hrG2, hval, hput]
    · simp only [DS.put]; rw [Function.update_of_ne hm, hb2ram]; exact hI.ramO m hm
    · intro y hy
      show b2.env y = e.env y
      rw [hb2env y (fun e' => hy (by rw [e']; decide)) (fun e' => hy (by rw [e']; decide))
        (fun e' => hy (by rw [e']; decide))]
      exact hI.fr y hy
    · show b2.ip = e.ip; rw [hb2sh.1]; exact hI.ip
    · show b2.out = e.out; rw [hb2sh.2.1]; exact hI.out
    · show b2.kin = e.kin; rw [hb2sh.2.2.1]; exact hI.kin
    · show b2.kout = e.kout; rw [hb2sh.2.2.2.1]; exact hI.kout
    · show b2.kc = e.kc; rw [hb2sh.2.2.2.2]; exact hI.kc
    · show b2.env t0 = k; rw [hb2env t0 (by decide) (by decide) (by decide)]; exact hbk
    · show b2.env gNQ = N; rw [hb2env gNQ (by decide) (by decide) (by decide)]; exact hbN

end NearCubicGates.Close.Cells.GatherPhase
