import Proof.Gates.Cells.Forms7
import Proof.Gates.Cells.Lay2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (gateN intN circN)

variable {C : Ctx}

/-- Run-wide layout values (set by the prelude): the base of the second circuit, the witness blocks, the
factor-count field. -/
def gB1 : Fin VV := ⟨121, by decide⟩
def gWS : Fin VV := ⟨122, by decide⟩
def gFS : Fin VV := ⟨123, by decide⟩
/-- The base of the current circuit. -/
def xB : Fin VV := ⟨66, by decide⟩

/-- `xGS := b + 1`, `t0 := 2n + 3`, `t1 := G·(2n+3)`, `xCS := b + 1 + G·(2n+3)`. -/
def setArith : St VV MM :=
  .seq (.op (.copy xGS xB)) (.seq (.op (.inc xGS)) (.seq (.op (.copy t0 gN))
  (.seq (.op (.shl t0)) (.seq (.op (.inc t0)) (.seq (.op (.inc t0)) (.seq (.op (.inc t0))
  (.seq (.op (.mul xG t0 t1)) (.seq (.op (.copy xCS xGS)) (.op (.add xCS t1))))))))))

def setTail : St VV MM := .seq (.op (.inc xCS)) (.seq (.op (.copy xWS gWS)) (.op (.copy xFS gFS)))

def setP : St VV MM := .seq (fetch sN xB xG) (.seq setArith (.seq (fetch sN xCS xNC) setTail))

def setT : List (Fin VV) := [c0, vJ, xG, xGS, t0, t1, xCS, xNC, xWS, xFS]

theorem setArith_spec (a : DS VV MM) (bb G n : ℕ) (hB : a.env xB = bb) (hG : a.env xG = G) (hn : a.env gN = n)
    (hW : bb + 1 + G * (2 * n + 3) < 2 ^ C.Wd) (hWn : 2 * n + 3 < 2 ^ C.Wd) :
    Hs C setArith a 19 (fun b => b.env xGS = bb + 1 ∧ b.env xCS = bb + 1 + G * (2 * n + 3) ∧
      b.ram = a.ram ∧ b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b [xGS, t0, t1, xCS]) := by
  have hGt : G * (2 * n + 3) < 2 ^ C.Wd := by omega
  refine Hs.seq (t1 := 1) (t2 := 17) (hs_copy C xGS xB a (by decide)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 15) (hs_inc C xGS _ (by vsimp [hB]; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 13) (hs_copy C t0 gN _ (by decide)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 11) (hs_shl C t0 _ (by vsimp [hn]; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 9) (hs_inc C t0 _ (by vsimp [hn]; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 7) (hs_inc C t0 _ (by vsimp [hn]; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_inc C t0 _ (by vsimp [hn]; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_mul C xG t0 t1 _ (by decide) (by decide) (by decide)
    (by vsimp [hn, hG]; ring_nf; ring_nf at hGt; omega)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C xCS xGS _ (by decide)) (fun e he => ?_)
  subst he
  refine Hs.mono (hs_add C xCS t1 _ (by decide) (by vsimp [hn, hG, hB]; ring_nf; ring_nf at hW; omega)) le_rfl ?_
  rintro b rfl
  refine ⟨by vsimp [hB], by vsimp [hn, hG, hB], rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  vsimp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

theorem setTail_spec (a : DS VV MM) (h : a.env xCS + 1 < 2 ^ C.Wd) :
    Hs C setTail a 5 (fun b => b.env xCS = a.env xCS + 1 ∧ b.env xWS = a.env gWS ∧ b.env xFS = a.env gFS ∧
      b.ram = a.ram ∧ b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b [xCS, xWS, xFS]) := by
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_inc C xCS a h) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C xWS gWS _ (by decide)) (fun e he => ?_)
  subst he
  refine Hs.mono (hs_copy C xFS gFS _ (by decide)) le_rfl ?_
  rintro b rfl
  refine ⟨by vsimp [], by vsimp [], by vsimp [], rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  vsimp [hy.1, hy.2.1, hy.2.2]

theorem setP_spec {n : ℕ} (a : DS VV MM) (Cc : NCircuit n) (R : List ℕ) (hn : a.env gN = n)
    (hb : (a.ram sN).drop (a.env xB) = circN Cc ++ R)
    (hW : a.env xB + 1 + Cc.gates.length * (2 * n + 3) + 2 < 2 ^ C.Wd) (hWn : 2 * n + 3 < 2 ^ C.Wd) :
    Hs C setP a (a.rc sN + 5 * a.env xB + 9 + 19 + (a.env xB + 1 + 5 * (a.env xB + 1 + Cc.gates.length * (2 * n + 3)) +
      9) + 5 + 3) (fun b =>
      b.env xG = Cc.gates.length ∧ b.env xGS = a.env xB + 1 ∧
      b.env xCS = a.env xB + 1 + Cc.gates.length * (2 * n + 3) + 1 ∧ b.env xNC = Cc.coeffs.length ∧
      b.env xWS = a.env gWS ∧ b.env xFS = a.env gFS ∧
      b.rc sN = a.env xB + 1 + Cc.gates.length * (2 * n + 3) + 1 ∧ b.ram sN = a.ram sN ∧ Agr a b [sN] setT) := by
  set bb := a.env xB with hbb
  set G := Cc.gates.length with hG
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := circ_fields Cc (a.ram sN) R bb hb
  have hlen : bb + 1 + G * (2 * n + 3) + 1 ≤ (a.ram sN).length := by
    by_contra h
    have h0 := List.drop_eq_nil_of_le (as := a.ram sN)
      (show (a.ram sN).length ≤ bb + 1 + G * (2 * n + 3) + 1 by omega)
    rw [f4] at h0; simp at h0
  refine Hs.bseq (fetch_spec sN xB xG (by decide) (by decide) a (by omega) (by omega)) (by omega)
    (fun e1 ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ => ?_)
  have ag1 : Agr a e1 [sN] setT := ⟨fun m _ => by rw [d4], fun m hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [d5, Function.update_of_ne hm], d2, d3, d6, d7,
    d8, Fr.weaken d9 (by decide)⟩
  have e1G : e1.env xG = G := by rw [d1]; exact f1
  have e1B : e1.env xB = bb := d9 xB (by decide)
  have e1n : e1.env gN = n := by rw [d9 gN (by decide)]; exact hn
  refine Hs.bseq (setArith_spec (C := C) e1 bb G n e1B e1G e1n (by omega) hWn) (by omega)
    (fun e2 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ => ?_)
  have ag2 : Agr e1 e2 [sN] setT := Agr.of_fr_same (by decide) ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩
  have e2N : e2.ram sN = a.ram sN := by rw [r3, d4]
  have e2Nc : e2.rc sN = bb + 1 := by rw [r4, d5, Function.update_self]
  have hx1 : e2.env xCS < (e2.ram sN).length := by rw [r2, e2N]; omega
  have hx2 : e2.env xCS < 2 ^ C.Wd := by rw [r2]; omega
  refine Hs.bseq (Hs.mono (fetch_spec sN xCS xNC (by decide) (by decide) e2 hx1 hx2)
    (show e2.rc sN + 5 * e2.env xCS + 9 ≤ bb + 1 + 5 * (bb + 1 + G * (2 * n + 3)) + 9 by rw [e2Nc, r2])
    (fun _ h => h)) (by omega) (fun e3 ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ => ?_)
  have ag3 : Agr e2 e3 [sN] setT := ⟨fun m _ => by rw [k4], fun m hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [k5, Function.update_of_ne hm], k2, k3, k6, k7,
    k8, Fr.weaken k9 (by decide)⟩
  have e3NC : e3.env xNC = Cc.coeffs.length := by rw [k1, e2N, r2]; exact f3
  have e3CS : e3.env xCS = bb + 1 + G * (2 * n + 3) := by rw [k9 xCS (by decide), r2]
  refine Hs.mono (setTail_spec (C := C) e3 (by rw [e3CS]; omega)) (by omega) ?_
  rintro b ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  have ag4 : Agr e3 b [sN] setT := Agr.of_fr_same (by decide) ⟨s4, s5, s6, s7, s8, s9, s10, s11⟩
  have fr := (ag1.trans (ag2.trans (ag3.trans ag4)))
  refine ⟨?_, ?_, by rw [s1, e3CS], by rw [s11 xNC (by decide), e3NC], ?_, ?_, ?_, ?_, fr⟩
  · rw [s11 xG (by decide), k9 xG (by decide), r10 xG (by decide), e1G]
  · rw [s11 xGS (by decide), k9 xGS (by decide), r1]
  · rw [s2, k9 gWS (by decide), r10 gWS (by decide), d9 gWS (by decide)]
  · rw [s3, k9 gFS (by decide), r10 gFS (by decide), d9 gFS (by decide)]
  · rw [s5, k5, Function.update_self, r2]
  · rw [s4, k4, e2N]

end NearCubicGates.Close.Cells
