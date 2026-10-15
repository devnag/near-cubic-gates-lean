import Proof.Gates.Cells.Forms4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (gateN intN)

variable {C : Ctx}

/-! ## Part 3: the stage loop -/

def stagesPart : St VV MM := .seq (seekP sN xWS) (.seq (.op (.rwM sG)) stagesP)

def sgT : List (Fin VV) := [c0, vJ, c5, fL, c3, gS0, gS1, gZ, gPos, gNeg]

theorem stagesPart_spec (a : DS VV MM) (hc : Cst a) (rc r : ℕ) (hrc : rc = 1 ∨ rc = 2) (hr : r < rc)
    (hR : a.env fR = r) (hRC : a.env gRC = rc) (J : ℕ) (hJ : a.env gJ = J) (hJW : J < 2 ^ C.Wd)
    (cf : ℕ → ℕ → List ℤ) (R : List ℕ) (hWS : (a.ram sN).drop (a.env xWS) = blocksAll cf rc J ++ R)
    (hWSl : a.env xWS ≤ (a.ram sN).length) (hWSW : a.env xWS < 2 ^ C.Wd)
    (gb Z : List ℕ) (hsB : a.ram sB = gb ++ Z) (hgb : ∀ s < J, (cf s r).length ≤ gb.length) (hB0 : a.rc sB = 0)
    (Gm : ℕ) (hGm : ∀ s < J, ∀ ρ < rc, (cf s ρ).length ≤ Gm)
    (hLW : Gm < 2 ^ C.Wd) (hW : ∀ s < J, ∀ ρ < rc, ((cf s ρ).map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C stagesPart a (a.rc sN + 5 * a.env xWS + a.rc sG + J * (30 * Gm + 40 + 4) + 16) (fun b =>
      b.ram sG = wr (a.ram sG) 0 (kPairs cf gb r J) ∧ b.rc sG = 2 * J ∧
      b.rc sN = a.env xWS + (blocksAll cf rc J).length ∧ b.ram sN = a.ram sN ∧ Agr a b [sN, sG] sgT) := by
  have hsg : sN ≠ sG := by decide
  refine Hs.bseq (seekP_spec sN xWS (by decide) (by decide) a hWSl hWSW) (by omega) (fun e1 he1 => ?_)
  have ag1 : Agr a e1 [sN, sG] sgT := Agr.of_seek (m := sN) (by simp) (by simp [sgT]) he1
  obtain ⟨h1, h2, -, -, -, -, -, h8⟩ := he1
  have e1G : e1.rc sG = a.rc sG := by rw [h2, Function.update_of_ne (Ne.symm hsg)]
  refine Hs.bseq (Hs.mono (hs_rwM C sG e1) (show e1.rc sG + 1 ≤ a.rc sG + 1 by rw [e1G]) (fun _ h => h))
    (by omega) (fun e2 he2 => ?_)
  subst he2
  have ag2 : Agr a (e1.rew sG) [sN, sG] sgT := ag1.trans (Agr.rew _ (by simp) _)
  have e2c : Cst (e1.rew sG) := Cst.of_fr hc ag2.fr (by decide)
  have e2N : ((e1.rew sG).ram sN).drop ((e1.rew sG).rc sN) = blocksAll cf rc J ++ R := by
    simp only [DS.rew]; rw [Function.update_of_ne hsg, h2, Function.update_self, h1, hWS]
  have e2B : (e1.rew sG).ram sB = gb ++ Z := by rw [ag2.ram sB (by decide), hsB]
  have e2B0 : (e1.rew sG).rc sB = 0 := by rw [ag2.rc sB (by decide), hB0]
  have hst := stagesP_spec (C := C) (e1.rew sG) e2c rc r hrc hr (by rw [ag2.fr fR (by decide)]; exact hR)
    (by rw [ag2.fr gRC (by decide)]; exact hRC) J (by rw [ag2.fr gJ (by decide)]; exact hJ) hJW cf R e2N gb Z
    e2B hgb e2B0 (by simp [DS.rew]) Gm hGm hLW hW
  refine Hs.mono hst (by omega) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  have e2Gram : (e1.rew sG).ram sG = a.ram sG := by simp only [DS.rew]; rw [h1]
  refine ⟨by rw [b1, Function.update_self, e2Gram], by rw [b2, Function.update_self], ?_, ?_, ?_⟩
  · rw [b2, Function.update_of_ne hsg, Function.update_self]
    simp only [DS.rew]; rw [Function.update_of_ne hsg, h2, Function.update_self]
  · rw [b1, Function.update_of_ne hsg]; simp only [DS.rew]; rw [h1]
  · refine ag2.trans ⟨fun m hm => ?_, fun m hm => ?_, b3, b4, b5, b6, b7, Fr.weaken b8 (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      rw [b1, Function.update_of_ne hm.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      rw [b2, Function.update_of_ne hm.2, Function.update_of_ne hm.1]

/-! ## Part 4: the digit centres -/

def ePart : St VV MM :=
  .seq (.op (.rwM sG)) (.seq (seekP sN xFS) (.seq (.op (.zero ePP)) (.seq (.op (.zero ePN)) eLoopP)))

def epT : List (Fin VV) := [c0, vJ, c5, ePP, ePN, eA, eB, eF, eT, eX, eY]

theorem ePart_spec (a : DS VV MM) (J : ℕ) (hJ : a.env gJ = J) (hJW : J < 2 ^ C.Wd) (kp kn : ℕ → ℕ)
    (hG2 : 2 * J ≤ (a.ram sG).length)
    (hGk : ∀ s < J, (a.ram sG).getD (2 * s) 0 = kp s ∧ (a.ram sG).getD (2 * s + 1) 0 = kn s)
    (fs R : List ℕ) (hFS : (a.ram sN).drop (a.env xFS) = [fs.length] ++ (fs ++ R)) (hJf : J ≤ fs.length + 1)
    (hFSW : a.env xFS < 2 ^ C.Wd) (FB KB : ℕ) (hFB1 : fs.length ≤ FB) (hFB2 : ∀ f ∈ fs, f ≤ FB)
    (hKp : ∀ s < J, kp s ≤ KB) (hKn : ∀ s < J, kn s ≤ KB) (hWd : KB + FB * KB < 2 ^ C.Wd)
    (E0 Pre : List ℕ) (hE : a.ram sE = wr E0 0 Pre) (hEc : a.rc sE = Pre.length) :
    Hs C ePart a (a.rc sG + a.rc sN + 5 * a.env xFS + J * 37 + 20) (fun b =>
      b.ram sE = wr E0 0 (Pre ++ ePairs kp kn fs J) ∧ b.rc sE = Pre.length + 2 * J ∧
      b.env ePP = prevV kp J ∧ b.env ePN = prevV kn J ∧ b.ram sN = a.ram sN ∧ b.ram sG = a.ram sG ∧
      b.rc sG = 2 * J ∧ b.rc sN = a.env xFS + J ∧ Agr a b [sG, sN, sE] epT) := by
  have hGN : sG ≠ sN := by decide
  have hGE : sG ≠ sE := by decide
  have hNE : sN ≠ sE := by decide
  have hlenN : a.env xFS + 1 + fs.length ≤ (a.ram sN).length := by
    have := congrArg List.length hFS; simp at this; omega
  refine Hs.bseq (hs_rwM C sG a) (by omega) (fun e1 he1 => ?_)
  subst he1
  refine Hs.bseq (Hs.mono (seekP_spec sN xFS (by decide) (by decide) (a.rew sG) (by simp [DS.rew]; omega) hFSW)
    (show (a.rew sG).rc sN + 5 * (a.rew sG).env xFS + 6 ≤ a.rc sN + 5 * a.env xFS + 6 by
      simp [DS.rew, Function.update_of_ne (Ne.symm hGN)]) (fun _ h => h)) (by omega) (fun e2 he2 => ?_)
  have ag2 : Agr (a.rew sG) e2 [sG, sN, sE] epT := Agr.of_seek (m := sN) (by simp) (by simp [epT]) he2
  obtain ⟨h1, h2, -, -, -, -, -, h8⟩ := he2
  refine Hs.bseq (hs_zero C ePP e2) (by omega) (fun e3 he3 => ?_)
  subst he3
  refine Hs.bseq (hs_zero C ePN _) (by omega) (fun e4 he4 => ?_)
  subst he4
  set e4 := (e2.set ePP 0).set ePN 0 with he4
  have ag4 : Agr a e4 [sG, sN, sE] epT := (Agr.rew a (by simp) _).trans (ag2.trans
    ((Agr.set _ _ _ (by simp [epT])).trans (Agr.set _ _ _ (by simp [epT]))))
  have e4ram : e4.ram = a.ram := by simp only [he4, DS.set_ram]; rw [h1]; rfl
  have e4rc : e4.rc = Function.update (Function.update a.rc sG 0) sN (a.env xFS) := by
    simp only [he4, DS.set_rc]; rw [h2]; simp [DS.rew, h8 xFS (by decide)]
  have hF : ∀ j, 1 ≤ j → j < J → (e4.ram sN).getD (e4.rc sN + j) 0 = fs.getD (j - 1) 0 := by
    intro j h1j hjJ
    rw [e4ram, e4rc, Function.update_self, List.getD_eq_getElem?_getD, ← List.getElem?_drop, hFS]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  have hFB : ∀ j < J, (e4.ram sN).getD (e4.rc sN + j) 0 ≤ FB := by
    intro j hjJ
    rw [e4ram, e4rc, Function.update_self, List.getD_eq_getElem?_getD, ← List.getElem?_drop, hFS]
    rcases j with _ | j
    · simp; exact hFB1
    · simp only [List.singleton_append, List.getElem?_cons_succ]
      rw [List.getElem?_append_left (by omega)]
      have hj : j < fs.length := by omega
      rw [List.getElem?_eq_getElem hj]; simp only [Option.getD_some]
      exact hFB2 _ (List.getElem_mem hj)
  have hl := eLoopP_spec (C := C) e4 J (by rw [ag4.fr gJ (by decide)]; exact hJ) hJW kp kn
    (by rw [e4ram]; exact hG2) (by rw [e4rc]; simp [Function.update_of_ne hGN])
    (by rw [e4ram]; exact hGk) fs FB KB (by rw [e4ram, e4rc, Function.update_self]; omega) hF hFB hKp hKn hWd
    E0 Pre (by rw [e4ram, hE]) (by rw [e4rc, Function.update_of_ne (Ne.symm hNE),
      Function.update_of_ne (Ne.symm hGE), hEc]) (by simp only [he4]; vsimp []) (by simp only [he4]; vsimp [])
  refine Hs.mono hl (by omega) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
  refine ⟨by rw [b1, Function.update_self], by rw [b2, Function.update_self], b3, b4,
    by rw [b1, Function.update_of_ne hNE, e4ram], by rw [b1, Function.update_of_ne hGE, e4ram],
    by rw [b2, Function.update_of_ne hGE, Function.update_of_ne hGN, Function.update_self],
    by rw [b2, Function.update_of_ne hNE, Function.update_self, e4rc, Function.update_self], ?_⟩
  refine ag4.trans ⟨fun m hm => ?_, fun m hm => ?_, b5, b6, b7, b8, b9, Fr.weaken b10 (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    rw [b1, Function.update_of_ne hm.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    rw [b2, Function.update_of_ne hm.2.2, Function.update_of_ne hm.2.1, Function.update_of_ne hm.1]

/-! ## Part 5: `pairOf (K_{J−1})` and `pairOf (X)` into `sX` -/

def xPart : St VV MM :=
  .seq (normP ePP ePN) (.seq (.op (.wrM sX ePP)) (.seq (.op (.wrM sX ePN)) (.seq (.op (.wrM sX xP))
    (.op (.wrM sX xN)))))

theorem xPart_spec (a : DS VV MM) (X0 Pre : List ℕ) (hX : a.ram sX = wr X0 0 Pre) (hXc : a.rc sX = Pre.length) :
    Hs C xPart a 12 (fun b =>
      b.ram sX = wr X0 0 (Pre ++ (pairOf ((a.env ePP : ℤ) - a.env ePN) ++ [a.env xP, a.env xN])) ∧
      b.rc sX = Pre.length + 4 ∧ Agr a b [sX] [ePP, ePN]) := by
  refine Hs.bseq (normP_spec ePP ePN (by decide) a) (by omega) (fun e1 he1 => ?_)
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := he1
  have ag1 : Agr a e1 [sX] [ePP, ePN] := Agr.of_fr_same (fun y hy => hy) ⟨n4, n5, n2, n3, n6, n7, n8, n9⟩
  have e1X : e1.ram sX = wr X0 0 Pre := by rw [n4, hX]
  have e1Xc : e1.rc sX = Pre.length := by rw [n5, hXc]
  have e1P : e1.env xP = a.env xP := n9 xP (by decide)
  have e1N : e1.env xN = a.env xN := n9 xN (by decide)
  have hl : ∀ (W : List ℕ), Pre.length + W.length ≤ (wr X0 0 (Pre ++ W)).length := by
    intro W; have := wr_length X0 (Pre ++ W); simpa using this
  refine Hs.bseq (hs_wrM C sX ePP e1 (by rw [e1Xc, e1X]; have := hl []; simpa using this)) (by omega)
    (fun e2 he2 => ?_)
  subst he2
  have s2 : (e1.put sX (e1.env ePP)).ram sX = wr X0 0 (Pre ++ [e1.env ePP]) := by
    simp only [DS.put, Function.update_self]; rw [e1Xc, e1X, wr_zero]
  have c2 : (e1.put sX (e1.env ePP)).rc sX = Pre.length + 1 := by simp [DS.put, e1Xc]
  refine Hs.bseq (hs_wrM C sX ePN _ (by rw [c2, s2]; have := hl [e1.env ePP]; simpa using this)) (by omega)
    (fun e3 he3 => ?_)
  subst he3
  set e2 := e1.put sX (e1.env ePP) with he2
  have s3 : (e2.put sX (e2.env ePN)).ram sX = wr X0 0 (Pre ++ [e1.env ePP, e1.env ePN]) := by
    simp only [DS.put, Function.update_self]; rw [c2, s2, show Pre.length + 1 = (Pre ++ [e1.env ePP]).length by simp,
      wr_zero]; simp [he2, DS.put]
  have c3 : (e2.put sX (e2.env ePN)).rc sX = Pre.length + 2 := by simp [DS.put, c2]
  refine Hs.bseq (hs_wrM C sX xP _ (by rw [c3, s3]; have := hl [e1.env ePP, e1.env ePN]; simpa using this))
    (by omega) (fun e4 he4 => ?_)
  subst he4
  set e3 := e2.put sX (e2.env ePN) with he3
  have s4 : (e3.put sX (e3.env xP)).ram sX = wr X0 0 (Pre ++ [e1.env ePP, e1.env ePN, a.env xP]) := by
    simp only [DS.put, Function.update_self]
    rw [c3, s3, show Pre.length + 2 = (Pre ++ [e1.env ePP, e1.env ePN]).length by simp, wr_zero]
    simp [he3, he2, DS.put, e1P]
  have c4 : (e3.put sX (e3.env xP)).rc sX = Pre.length + 3 := by simp [DS.put, c3]
  refine Hs.mono (hs_wrM C sX xN _ (by rw [c4, s4]; have := hl [e1.env ePP, e1.env ePN, a.env xP]; simpa using this))
    (by omega) ?_
  rintro b rfl
  set e4 := e3.put sX (e3.env xP) with he4
  refine ⟨?_, by simp [DS.put, c4], ?_⟩
  · simp only [DS.put, Function.update_self]
    rw [c4, s4, show Pre.length + 3 = (Pre ++ [e1.env ePP, e1.env ePN, a.env xP]).length by simp, wr_zero]
    have : [e1.env ePP, e1.env ePN] = pairOf ((a.env ePP : ℤ) - a.env ePN) := n1
    rw [← this]; simp [he4, he3, he2, DS.put, e1N]
  · refine ag1.trans ⟨fun m hm => ?_, fun m hm => ?_, rfl, rfl, rfl, rfl, rfl, fun y _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      simp [he4, he3, he2, DS.put, Function.update_of_ne hm]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      simp [he4, he3, he2, DS.put, Function.update_of_ne hm]

end NearCubicGates.Close.Cells
