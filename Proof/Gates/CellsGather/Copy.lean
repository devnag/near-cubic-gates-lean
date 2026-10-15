import Proof.Gates.CellsGather.Strip

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def cpT : List (Fin VV) := [t0, gx]

/-- The copy invariant after `k` records. -/
structure CpI (Out A0 : List ℕ) (e : DS VV MM) (k : ℕ) (b : DS VV MM) : Prop where
  ramA : b.ram sA = Out.take k ++ A0.drop k
  rcA : b.rc sA = k
  rcG : b.rc sG = k
  ramO : ∀ m, m ≠ sA → b.ram m = e.ram m
  fr : Fr e b cpT
  ip : b.ip = e.ip
  out : b.out = e.out
  kin : b.kin = e.kin
  kout : b.kout = e.kout
  kc : b.kc = e.kc

theorem CpI.set {Out A0 : List ℕ} {e : DS VV MM} {k : ℕ} {b : DS VV MM} (h : CpI Out A0 e k b) (v : ℕ) :
    CpI Out A0 e k (b.set t0 v) :=
  ⟨h.ramA, h.rcA, h.rcG, h.ramO, h.fr.trans (Fr.set b v (by decide)), h.ip, h.out, h.kin, h.kout, h.kc⟩

theorem copyP_spec (e : DS VV MM) (N : ℕ) (Out rest A0 : List ℕ) (hG : e.ram sG = Out ++ rest)
    (hO : Out.length = N) (hA : e.ram sA = A0) (hA0 : A0.length = N) (hq : e.env gNQ = N) (hW : N < 2 ^ C.Wd) :
    Hs C copyP e (e.rc sA + e.rc sG + 7 * N + 8) (fun b =>
      b.ram sA = Out ∧ (∀ m, m ≠ sA → b.ram m = e.ram m) ∧ Fr e b cpT ∧
      b.ip = e.ip ∧ b.out = e.out ∧ b.kin = e.kin ∧ b.kout = e.kout ∧ b.kc = e.kc) := by
  obtain ⟨s1, n1, e1, hn1, h1⟩ := hs_rwM C sA e
  subst h1
  obtain ⟨s2, n2, e2, hn2, h2⟩ := hs_rwM C sG (e.rew sA)
  subst h2
  have hrcG : (e.rew sA).rc sG = e.rc sG := by simp [DS.rew, Function.update_of_ne (by decide : sG ≠ sA)]
  have h0 : CpI Out A0 e 0 ((e.rew sA).rew sG) := by
    refine ⟨by simp [DS.rew, hA], ?_, ?_, fun m _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [DS.rew, Function.update_of_ne (by decide : sA ≠ sG)]
    · simp [DS.rew]
  have hloop := forS_spec' (C := C) t0 gNQ (by decide) cpBody ((e.rew sA).rew sG) N hW (CpI Out A0 e)
    3 (fun k b v h => h.set v) h0 hq ?_
  · obtain ⟨s3, n3, e3, hn3, hI, -, -⟩ := hloop
    refine ⟨s3, n1 + (n2 + n3 + 1) + 1, Ex.seq e1 (Ex.seq e2 e3), by rw [hrcG] at hn2; omega, ?_⟩
    refine ⟨by rw [hI.ramA, ← hO, List.take_length, List.drop_eq_nil_of_le (by omega), List.append_nil],
      hI.ramO, hI.fr, hI.ip, hI.out, hI.kin, hI.kout, hI.kc⟩
  · intro k hk b hI hbk hbN
    have hkO : k < Out.length := by omega
    have hGb : b.ram sG = Out ++ rest := by rw [hI.ramO sG (by decide), hG]
    have hr1 : b.rc sG < (b.ram sG).length := by rw [hI.rcG, hGb]; simp; omega
    obtain ⟨s1, n1, e1, hn1, h1⟩ := hs_rdM C sG gx b hr1
    subst h1
    set b1 := (b.set gx ((b.ram sG).getD (b.rc sG) 0)).adv sG with hb1
    have hx1 : b1.env gx = Out[k] := by
      rw [hb1]; simp only [DS.adv, DS.set, DS.env_set, Function.update_self]
      rw [hGb, hI.rcG, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hkO]
    have hb1rc : b1.rc = Function.update b.rc sG (k + 1) := by rw [hb1]; simp only [DS.adv, DS.set]; rw [hI.rcG]
    have hb1ram : b1.ram = b.ram := by rw [hb1]; rfl
    have hb1sh : b1.ip = b.ip ∧ b1.out = b.out ∧ b1.kin = b.kin ∧ b1.kout = b.kout ∧ b1.kc = b.kc := by
      rw [hb1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hb1env : ∀ y, y ≠ gx → b1.env y = b.env y := by
      intro y h1; rw [hb1]; simp only [DS.adv, DS.set, DS.env_set]; rw [Function.update_of_ne h1]
    have hlk : (Out.take k).length = k := by rw [List.length_take, Nat.min_eq_left (by omega)]
    have hrA : b1.rc sA = k := by rw [hb1rc, Function.update_of_ne (by decide : sA ≠ sG), hI.rcA]
    have hramA : b1.ram sA = Out.take k ++ A0.drop k := by rw [hb1ram, hI.ramA]
    have hr2 : b1.rc sA ≤ (b1.ram sA).length := by rw [hrA, hramA]; simp; omega
    obtain ⟨s2, n2, e2, hn2, h2⟩ := hs_wrM C sA gx b1 hr2
    subst h2
    refine ⟨_, n1 + n2 + 1, Ex.seq e1 e2, by omega, ?_⟩
    have htk : Out.take (k + 1) = Out.take k ++ [Out[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkO]; rfl
    refine ⟨⟨?_, ?_, ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [DS.put, Function.update_self]; rw [hramA, hrA, hx1, putAt_pre' _ _ _ _ hlk, htk]
    · simp only [DS.put, Function.update_self]; rw [hrA]
    · simp only [DS.put]; rw [Function.update_of_ne (by decide : sG ≠ sA), hb1rc, Function.update_self]
    · simp only [DS.put]; rw [Function.update_of_ne hm, hb1ram]; exact hI.ramO m hm
    · intro y hy
      show b1.env y = e.env y
      rw [hb1env y (fun e' => hy (by rw [e']; decide))]
      exact hI.fr y hy
    · show b1.ip = e.ip; rw [hb1sh.1]; exact hI.ip
    · show b1.out = e.out; rw [hb1sh.2.1]; exact hI.out
    · show b1.kin = e.kin; rw [hb1sh.2.2.1]; exact hI.kin
    · show b1.kout = e.kout; rw [hb1sh.2.2.2.1]; exact hI.kout
    · show b1.kc = e.kc; rw [hb1sh.2.2.2.2]; exact hI.kc
    · show b1.env t0 = k; rw [hb1env t0 (by decide)]; exact hbk
    · show b1.env gNQ = N; rw [hb1env gNQ (by decide)]; exact hbN

end NearCubicGates.Close.Cells.GatherPhase
