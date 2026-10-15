import Proof.Gates.Cells.Forms5

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

def roleP : St VV MM := .seq gatesPart (.seq scorePart (.seq stagesPart (.seq ePart xPart)))

def roleT : List (Fin VV) :=
  [c0, vJ, gG, c4, c3, gS0, gS1, gZ, gPos, gNeg, fL, xP, xN, c5, ePP, ePN, eA, eB, eF, eT, eX, eY]

def roleMs : List (Fin MM) := [sN, sB, sG, sE, sX]

/-- The stage pairs of the role as functions. -/
def kpOf (cf : ℕ → ℕ → List ℤ) (gb : List ℕ) (r s : ℕ) : ℕ := posPart (cf s r) (gb.take (cf s r).length)
def knOf (cf : ℕ → ℕ → List ℤ) (gb : List ℕ) (r s : ℕ) : ℕ := negPart (cf s r) (gb.take (cf s r).length)

theorem kPairs_getD (cf : ℕ → ℕ → List ℤ) (gb : List ℕ) (r J s : ℕ) (hs : s < J) :
    (kPairs cf gb r J).getD (2 * s) 0 = kpOf cf gb r s ∧ (kPairs cf gb r J).getD (2 * s + 1) 0 = knOf cf gb r s := by
  induction J with
  | zero => omega
  | succ J ih =>
    unfold kPairs
    rw [flatMap_range_succ (fun s => [posPart (cf s r) (gb.take (cf s r).length),
      negPart (cf s r) (gb.take (cf s r).length)]) J]
    have hl : ((List.range J).flatMap fun s => [posPart (cf s r) (gb.take (cf s r).length),
        negPart (cf s r) (gb.take (cf s r).length)]).length = 2 * J := kPairs_length cf gb r J
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
    · obtain ⟨i1, i2⟩ := ih h
      unfold kPairs at i1 i2
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ⟨i1, i2⟩
    · subst h
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
      simp [kpOf, knOf]

theorem roleP_spec {n : ℕ} (a : DS VV MM) (hc : Cst a) (hn : a.env gN = n) (hnW : n < 2 ^ C.Wd)
    -- gates
    (gs : List (NormalizedThresholdGate n)) (R1 : List ℕ)
    (hGS : (a.ram sN).drop (a.env xGS) = gs.flatMap gateN ++ R1) (hGSl : a.env xGS ≤ (a.ram sN).length)
    (hGSW : a.env xGS < 2 ^ C.Wd) (hG : a.env xG = gs.length) (hGW : gs.length < 2 ^ C.Wd)
    (zb : List ℕ) (hzb : a.ram sZb = zb) (hzl : zb.length = n) (hz0 : a.rc sZb = 0)
    (hWg : ∀ g ∈ gs, ((List.ofFn g.weight).map Int.natAbs).sum + g.threshold.natAbs < 2 ^ C.Wd)
    -- score
    (cs : List ℤ) (R2 : List ℕ)
    (hCS : (a.ram sN).drop (a.env xCS) = cs.flatMap intN ++ R2) (hCSl : a.env xCS ≤ (a.ram sN).length)
    (hCSW : a.env xCS < 2 ^ C.Wd) (hNC : a.env xNC = cs.length) (hgc : gs.length = cs.length)
    (hB : (cs.map Int.natAbs).sum < 2 ^ C.Wd)
    -- stages
    (rc r : ℕ) (hrc : rc = 1 ∨ rc = 2) (hr : r < rc) (hR : a.env fR = r) (hRC : a.env gRC = rc)
    (J : ℕ) (hJ : a.env gJ = J) (hJW : J < 2 ^ C.Wd)
    (cf : ℕ → ℕ → List ℤ) (R3 : List ℕ) (hWS : (a.ram sN).drop (a.env xWS) = blocksAll cf rc J ++ R3)
    (hWSl : a.env xWS ≤ (a.ram sN).length) (hWSW : a.env xWS < 2 ^ C.Wd)
    (hcf : ∀ s < J, (cf s r).length ≤ gs.length)
    (Gm : ℕ) (hGm : ∀ s < J, ∀ ρ < rc, (cf s ρ).length ≤ Gm) (hLW : Gm < 2 ^ C.Wd)
    (hWc : ∀ s < J, ∀ ρ < rc, ((cf s ρ).map Int.natAbs).sum < 2 ^ C.Wd)
    -- centres
    (fs R4 : List ℕ) (hFS : (a.ram sN).drop (a.env xFS) = [fs.length] ++ (fs ++ R4)) (hJf : J ≤ fs.length + 1)
    (hFSW : a.env xFS < 2 ^ C.Wd) (FB KB : ℕ) (hFB1 : fs.length ≤ FB) (hFB2 : ∀ f ∈ fs, f ≤ FB)
    (hKB : ∀ s < J, ((cf s r).map Int.natAbs).sum ≤ KB) (hWd : KB + FB * KB < 2 ^ C.Wd)
    (E0 Pre : List ℕ) (hE : a.ram sE = wr E0 0 Pre) (hEc : a.rc sE = Pre.length)
    (X0 PreX : List ℕ) (hX : a.ram sX = wr X0 0 PreX) (hXc : a.rc sX = PreX.length) :
    Hs C roleP a ((a.rc sN + 5 * a.env xGS + a.rc sB + gs.length * (15 * n + 28) + 16) +
      ((a.env xGS + gs.length * (2 * n + 3)) + 5 * a.env xCS + gs.length + 15 * cs.length + 40) +
      ((a.env xCS + 2 * cs.length) + 5 * a.env xWS + a.rc sG + J * (30 * Gm + 40 + 4) + 16) +
      (2 * J + (a.env xWS + (blocksAll cf rc J).length) + 5 * a.env xFS + J * 37 + 20) + 12 + 4) (fun b =>
      b.ram sE = wr E0 0 (Pre ++ ePairs (kpOf cf (gs.map (gbit · zb)) r) (knOf cf (gs.map (gbit · zb)) r) fs J) ∧
      b.rc sE = Pre.length + 2 * J ∧
      b.ram sX = wr X0 0 (PreX ++ (pairOf ((prevV (kpOf cf (gs.map (gbit · zb)) r) J : ℤ) -
        prevV (knOf cf (gs.map (gbit · zb)) r) J) ++
        pairOf ((posPart cs (gs.map (gbit · zb)) : ℤ) - negPart cs (gs.map (gbit · zb))))) ∧
      b.rc sX = PreX.length + 4 ∧
      b.ram sN = a.ram sN ∧ b.ram sB = gs.map (gbit · zb) ++ (a.ram sB).drop gs.length ∧ b.rc sB = 0 ∧
      b.ram sG = wr (a.ram sG) 0 (kPairs cf (gs.map (gbit · zb)) r J) ∧ b.rc sG = 2 * J ∧
      b.rc sN = a.env xFS + J ∧ Agr a b roleMs roleT) := by
  have hsb : sN ≠ sB := by decide
  have s_gp : ∀ y ∈ gatesPartT, y ∈ roleT := by decide
  have s_sp : ∀ y ∈ spT, y ∈ roleT := by decide
  have s_sg : ∀ y ∈ sgT, y ∈ roleT := by decide
  have s_ep : ∀ y ∈ epT, y ∈ roleT := by decide
  have s_x : ∀ y ∈ [ePP, ePN], y ∈ roleT := by decide
  have m_1 : ∀ m ∈ [sN, sB], m ∈ roleMs := by decide
  have m_3 : ∀ m ∈ [sN, sG], m ∈ roleMs := by decide
  have m_4 : ∀ m ∈ [sG, sN, sE], m ∈ roleMs := by decide
  have m_5 : ∀ m ∈ [sX], m ∈ roleMs := by decide
  set gb := gs.map (gbit · zb) with hgb
  have hgbl : gb.length = gs.length := by simp [hgb]
  -- part 1
  refine Hs.bseq (gatesPart_spec (C := C) a hc hn hnW gs R1 hGS hGSl hGSW hG hGW zb hzb hzl hz0 hWg) (by omega)
    (fun e1 ⟨g1, g2, g3, g4, ag1⟩ => ?_)
  have e1c : Cst e1 := Cst.of_fr hc ag1.fr (by decide)
  -- part 2
  have e1CS : e1.env xCS = a.env xCS := ag1.fr xCS (by decide)
  have hsc := scorePart_spec (C := C) e1 e1c cs R2 (by rw [g4, e1CS, hCS]) (by rw [g4, e1CS]; exact hCSl)
    (by rw [e1CS]; exact hCSW) (by rw [ag1.fr xNC (by decide)]; exact hNC) (by rw [← hgc]; exact hGW)
    gb ((a.ram sB).drop gs.length) g1 (by rw [hgbl, hgc]) hB
  refine Hs.bseq (Hs.mono hsc (show e1.rc sN + 5 * e1.env xCS + e1.rc sB + 15 * cs.length + 40 ≤
      (a.env xGS + gs.length * (2 * n + 3)) + 5 * a.env xCS + gs.length + 15 * cs.length + 40 by
      rw [g3, e1CS, g2]) (fun _ h => h)) (by omega) (fun e2 ⟨s1, s2, s3, s4, s5, ag2⟩ => ?_)
  have e2c : Cst e2 := Cst.of_fr e1c ag2.fr (by decide)
  have f12 : ∀ y, y ∉ roleT → e2.env y = a.env y := fun y hy =>
    (ag2.fr y (fun h => hy (s_sp y h))).trans (ag1.fr y (fun h => hy (s_gp y h)))
  -- part 3
  have e2N : e2.ram sN = a.ram sN := by rw [s4, g4]
  have e2B : e2.ram sB = gb ++ (a.ram sB).drop gs.length := by rw [s5, g1]
  have e2G : e2.ram sG = a.ram sG := by rw [ag2.ram sG (by decide), ag1.ram sG (by decide)]
  have e2Gc : e2.rc sG = a.rc sG := by rw [ag2.rc sG (by decide), ag1.rc sG (by decide)]
  have e2WS : e2.env xWS = a.env xWS := f12 xWS (by decide)
  have hst := stagesPart_spec (C := C) e2 e2c rc r hrc hr (by rw [f12 fR (by decide)]; exact hR)
    (by rw [f12 gRC (by decide)]; exact hRC) J (by rw [f12 gJ (by decide)]; exact hJ) hJW cf R3
    (by rw [e2N, e2WS, hWS]) (by rw [e2N, e2WS]; exact hWSl) (by rw [e2WS]; exact hWSW) gb
    ((a.ram sB).drop gs.length) e2B (fun s hs => by rw [hgbl]; exact hcf s hs) s2 Gm hGm hLW hWc
  refine Hs.bseq (Hs.mono hst (show e2.rc sN + 5 * e2.env xWS + e2.rc sG + J * (30 * Gm + 40 + 4) + 16 ≤
      (a.env xCS + 2 * cs.length) + 5 * a.env xWS + a.rc sG + J * (30 * Gm + 40 + 4) + 16 by
      rw [s3, e2WS, e2Gc, e1CS]) (fun _ h => h)) (by omega) (fun e3 ⟨t1, t2, t3, t4, ag3⟩ => ?_)
  have f13 : ∀ y, y ∉ roleT → e3.env y = a.env y := fun y hy =>
    (ag3.fr y (fun h => hy (s_sg y h))).trans (f12 y hy)
  -- part 4
  have e3G : e3.ram sG = wr (a.ram sG) 0 (kPairs cf gb r J) := by rw [t1, e2G]
  have e3N : e3.ram sN = a.ram sN := by rw [t4, e2N]
  have e3FS : e3.env xFS = a.env xFS := f13 xFS (by decide)
  have e3E : e3.ram sE = a.ram sE := by
    rw [ag3.ram sE (by decide), ag2.ram sE (by decide), ag1.ram sE (by decide)]
  have e3Ec : e3.rc sE = a.rc sE := by
    rw [ag3.rc sE (by decide), ag2.rc sE (by decide), ag1.rc sE (by decide)]
  have hK : ∀ s < J, kpOf cf gb r s ≤ KB ∧ knOf cf gb r s ≤ KB := by
    intro s hs
    have := posPart_le (cf s r) (gb.take (cf s r).length)
    have := hKB s hs
    unfold kpOf knOf; omega
  have hep := ePart_spec (C := C) e3 J (by rw [f13 gJ (by decide)]; exact hJ) hJW (kpOf cf gb r) (knOf cf gb r)
    (by rw [e3G]; have := wr_length (a.ram sG) (kPairs cf gb r J); rw [kPairs_length] at this; exact this)
    (fun s hs => by
      rw [e3G, getD_wr _ _ _ (by rw [kPairs_length]; omega), getD_wr _ _ _ (by rw [kPairs_length]; omega)]
      exact kPairs_getD cf gb r J s hs)
    fs R4 (by rw [e3N, e3FS, hFS]) hJf (by rw [e3FS]; exact hFSW) FB KB hFB1 hFB2 (fun s hs => (hK s hs).1)
    (fun s hs => (hK s hs).2) hWd E0 Pre (by rw [e3E, hE]) (by rw [e3Ec, hEc])
  refine Hs.bseq (Hs.mono hep (show e3.rc sG + e3.rc sN + 5 * e3.env xFS + J * 37 + 20 ≤
      2 * J + (a.env xWS + (blocksAll cf rc J).length) + 5 * a.env xFS + J * 37 + 20 by
      rw [t2, t3, e3FS, e2WS]) (fun _ h => h)) (by omega) (fun e4 ⟨u1, u2, u3, u4, u5, u6, u7, u8, ag4⟩ => ?_)
  -- part 5
  have e4X : e4.ram sX = a.ram sX := by
    rw [ag4.ram sX (by decide), ag3.ram sX (by decide), ag2.ram sX (by decide), ag1.ram sX (by decide)]
  have e4Xc : e4.rc sX = a.rc sX := by
    rw [ag4.rc sX (by decide), ag3.rc sX (by decide), ag2.rc sX (by decide), ag1.rc sX (by decide)]
  have hxp := xPart_spec (C := C) e4 X0 PreX (by rw [e4X, hX]) (by rw [e4Xc, hXc])
  refine Hs.mono hxp (by omega) ?_
  rintro b ⟨v1', v2', ag5⟩
  have e4xP : e4.env xP = e2.env xP := by rw [ag4.fr xP (by decide), ag3.fr xP (by decide)]
  have e4xN : e4.env xN = e2.env xN := by rw [ag4.fr xN (by decide), ag3.fr xN (by decide)]
  have agAll : Agr a b roleMs roleT :=
    (ag1.weaken m_1 s_gp).trans ((ag2.weaken m_1 s_sp).trans
      ((ag3.weaken m_3 s_sg).trans ((ag4.weaken m_4 s_ep).trans (ag5.weaken m_5 s_x))))
  refine ⟨?_, ?_, ?_, v2', ?_, ?_, ?_, ?_, ?_, ?_, agAll⟩
  · rw [ag5.ram sE (by decide), u1]
  · rw [ag5.rc sE (by decide), u2]
  · rw [v1', u3, u4, e4xP, e4xN, s1]
  · rw [ag5.ram sN (by decide), u5, e3N]
  · rw [ag5.ram sB (by decide), ag4.ram sB (by decide), ag3.ram sB (by decide), e2B]
  · rw [ag5.rc sB (by decide), ag4.rc sB (by decide), ag3.rc sB (by decide), s2]
  · rw [ag5.ram sG (by decide), u6, e3G]
  · rw [ag5.rc sG (by decide), u7]
  · rw [ag5.rc sN (by decide), u8, e3FS]

end NearCubicGates.Close.Cells
