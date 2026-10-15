import Proof.Gates.CounterMachine.CellTablesCst3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW)

def cstP : St VV MM := .seq cst1 (.seq cst2 (.seq cst3 cst4))

def cstT : List (Fin VV) := [vS, cA, vH1, cI, vH0, cKB, kB2, kD, cKL, cB, cDB, cSD, cT, kVW2, cKK, vSH, vRW, kPAD]

/-- The constants of the call. -/
structure CstV (e : DS VV MM) (c : Call) (p : Params) : Prop where
  s : e.env vS = c.n - p.k
  h1 : e.env vH1 = 2 ^ ((c.n - p.k + 1) / 2)
  h0 : e.env vH0 = 2 ^ ((c.n - p.k) / 2)
  sh : e.env vSH = 2 ^ (keyBits p * keyLen c p + valueWidth c p)
  b2 : e.env kB2 = 2 ^ keyBits p
  d : e.env kD = dOf c p
  vw2 : e.env kVW2 = 2 ^ valueWidth c p
  pad : e.env kPAD = 2 ^ (keyBits p * dOf c p) * 2 ^ valueWidth c p
  rw : e.env vRW = c.n - p.k + keyBits p * keyLen c p + valueWidth c p

def cstCost (c : Call) (p : Params) : ℕ :=
  5 * c.n + 10 * (p.P + p.J + dOf c p) + 5 * Nat.size (deltaBound c p) + 5 * valueWidth c p +
    5 * (keyBits p * keyLen c p + valueWidth c p) + 7 * dOf c p + 200

theorem cst_spec (C : Ctx) (c : Call) (p : Params) (a : DS VV MM) (hc : Cst a) (hpv : ParV a p)
    (hn : a.env gN = c.n) (hJ : a.env gJ = p.J) (hrc : a.env gRC = roleCount c.kind) (hWc : p.W = c.W)
    (hkn : p.k ≤ c.n) (hW : lamW c p + p.P + p.J + dOf c p + 4 ≤ C.Wd) (hDB : deltaBound c p < 2 ^ C.Wd) :
    Hs C cstP a (cstCost c p) (fun e => CstV e c p ∧ e.sh = a.sh ∧ Fr a e cstT) := by
  have hKL : keyLen c p = dOf c p + 3 := by unfold keyLen dOf; omega
  have hVW : valueWidth c p = p.k + 2 * p.k * Nat.size (2 * (p.M1 + p.A + p.factors.sum + 1) * (p.W + 1)) + 1 := by
    rw [hWc]; rfl
  have hDB' : 2 * (p.M1 + p.A + p.factors.sum + 1) * (p.W + 1) < 2 ^ C.Wd := by rw [hWc]; exact hDB
  unfold lamW at hW
  apply Hx.hs
  refine Hs.then (cst1_spec C a hc c.n p.k hn hpv.k hkn (by omega)) (fun b1 ⟨v1s, v1h1, v1h0, s1, f1⟩ n1 hn1 => ?_)
  have c1 := cst_fr hc f1 (by decide)
  refine Hs.then (cst2_spec C b1 c1 p.P p.J (roleCount c.kind) (by rw [f1 wP (by decide)]; exact hpv.P)
    (by rw [f1 gJ (by decide)]; exact hJ) (by rw [f1 gRC (by decide)]; exact hrc) (by unfold dOf at hW; nlinarith))
    (fun b2 ⟨v2kb, v2b2, v2d, v2kl, s2, f2⟩ n2 hn2 => ?_)
  have c2 := cst_fr c1 f2 (by decide)
  have g2 : ∀ y, y ∉ [vS, cA, vH1, cI, vH0] → y ∉ [cA, cKB, kB2, cI, kD, cKL] → b2.env y = a.env y :=
    fun y h1 h2 => by rw [f2 y h2, f1 y h1]
  refine Hs.then (cst3_spec C b2 c2 p.M1 p.A p.factors.sum p.W p.k (by rw [g2 wM1 (by decide) (by decide)]; exact hpv.M1)
    (by rw [g2 wA (by decide) (by decide)]; exact hpv.A) (by rw [g2 wF (by decide) (by decide)]; exact hpv.F)
    (by rw [g2 wW (by decide) (by decide)]; exact hpv.W) (by rw [g2 wK (by decide) (by decide)]; exact hpv.k) hDB'
    (by rw [← hVW]; omega)) (fun b3 ⟨v3t, v3v2, s3, f3⟩ n3 hn3 => ?_)
  have c3 := cst_fr c2 f3 (by decide)
  rw [← hVW] at v3t v3v2
  refine Hs.last (cst4_spec C b3 c3 (c.n - p.k) (keyBits p) (keyLen c p) (valueWidth c p) (dOf c p)
    (by rw [f3 cKB (by decide)]; exact v2kb) (by rw [f3 cKL (by decide), v2kl, hKL]; rfl) v3t
    (by rw [f3 vS (by decide), f2 vS (by decide)]; exact v1s) v3v2 (by rw [f3 kB2 (by decide)]; exact v2b2)
    (by rw [f3 kD (by decide)]; exact v2d) (by omega) (by unfold dOf at hW ⊢; omega) (by omega))
    (fun b4 ⟨v4sh, v4rw, v4pad, s4, f4⟩ n4 hn4 => ?_)
  refine ⟨⟨⟨?_, ?_, ?_, v4sh, ?_, ?_, ?_, ?_, v4rw⟩, by rw [s4, s3, s2, s1], ?_⟩, ?_⟩
  · rw [f4 vS (by decide), f3 vS (by decide), f2 vS (by decide)]; exact v1s
  · rw [f4 vH1 (by decide), f3 vH1 (by decide), f2 vH1 (by decide)]; exact v1h1
  · rw [f4 vH0 (by decide), f3 vH0 (by decide), f2 vH0 (by decide)]; exact v1h0
  · rw [f4 kB2 (by decide), f3 kB2 (by decide)]; exact v2b2
  · rw [f4 kD (by decide), f3 kD (by decide)]; exact v2d
  · rw [f4 kVW2 (by decide)]; exact v3v2
  · rw [v4pad, ← pow_mul, mul_comm]
  · exact Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.weaken f2 (by decide)) (Fr.trans (Fr.weaken f3 (by decide))
      (Fr.weaken f4 (by decide))))
  · unfold cstCost
    have : Nat.size (2 * (p.M1 + p.A + p.factors.sum + 1) * (p.W + 1)) = Nat.size (deltaBound c p) := by
      rw [hWc]; rfl
    rw [← hVW, this] at hn3
    have hd : roleCount c.kind * (p.J + 1) = dOf c p := rfl
    rw [hd] at hn2
    omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
