import Proof.Gates.Cells.CellLoop2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

def cellLoop (gP sysPr : St VV MM) : St VV MM := forS cI gNC (cellBody gP sysPr)

/-- The per-cell cost bound (uniform over the cells). -/
noncomputable def cellCostU (c : Call) (p : Params) (wt : Wit c.n) (TG TS : ℕ) : ℕ :=
  blkCost (reqIds c p).length (recWidth c p wt) + 3 +
    passCost c.n (cellN c p wt).length (ctrL c p wt (cellOf wt.I 0)).length (kxL c p wt (cellOf wt.I 0)).length
      (gWork c p wt (cellOf wt.I 0)) (formsCost (cellN c p wt).length c.n) TG TS

section Lp
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

open Classical in
include hadm hs hw in
/-- **The loop over the cells.** -/
theorem cellLoop_spec (S : SolveMachine) (gP sysPr : St VV MM) (tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ) (hG : GatherGoal gP tg) (hS : SysGoal sysPr ts)
    (hK : C.K = Callee.ofSolve S) (Big : ℕ) (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big)
    (hWd : wdNeed c p wt Big ≤ C.Wd)
    (hLB : ∀ (y : Cells wt.I) part κ, κ ∈ digitVectors c p wt y →
      (sysWord (sysOf c p wt y κ part)).length ≤ C.Lk ∧ S.budget (sysOf c p wt y κ part) ≤ C.Bk)
    (pre : List Bool) (hinp : C.inp = pre ++ cellWord c p wt)
    (a : DS VV MM) (hI : Iface c p wt a) (hSt : Sto c p wt a) (hip : a.ip = pre.length)
    (hc0 : a.env vCnt = 0) (hu0 : a.env vUnc = 0) :
    Hs C (cellLoop gP sysPr) a (2 ^ cellBits wt.I * (cellCostU c p wt (tg C c p Big) (ts S C c p Big) + 4) + 4)
      (fun b => Iface c p wt b ∧ Sto c p wt b ∧
        (b.env vCnt : ℚ) = ∑ j ∈ Finset.range (2 ^ cellBits wt.I),
          (if CellTests c p wt (cellOf wt.I j) then cellCount c p wt (cellOf wt.I j) else 0) ∧
        b.env vUnc = ∑ j ∈ Finset.range (2 ^ cellBits wt.I), (if CellTests c p wt (cellOf wt.I j) then 0 else 1)) := by
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  have hcb := cb_eq c p wt hs w hw
  have hcn : cellBits wt.I ≤ c.n := by rw [hcb]; omega
  have hnw : c.n + 1 ≤ 256 * (p.J + 4) * (Big + c.n + 16) := by nlinarith
  have hN : 2 ^ cellBits wt.I < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  let I : ℕ → DS VV MM → Prop := fun k e => Iface c p wt e ∧ Sto c p wt e ∧
    e.ip = pre.length + k * ((reqIds c p).length * (2 * recWidth c p wt + 1)) ∧
    (e.env vCnt : ℚ) = ∑ j ∈ Finset.range k,
      (if CellTests c p wt (cellOf wt.I j) then cellCount c p wt (cellOf wt.I j) else 0) ∧
    e.env vCnt ≤ k * 2 ^ p.k ∧
    e.env vUnc = ∑ j ∈ Finset.range k, (if CellTests c p wt (cellOf wt.I j) then 0 else 1) ∧ e.env vUnc ≤ k
  have hl := forS_spec' (C := C) cI gNC (by decide) (cellBody gP sysPr) a (2 ^ cellBits wt.I) hN I
    (cellCostU c p wt (tg C c p Big) (ts S C c p Big))
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7⟩ => ⟨i1.of_eq (fun x hx => DS.set_env_ne _ _
      (fun h => by subst h; revert hx; decide)), ⟨i2.sN, i2.sP, i2.sR, i2.lCT, i2.lZb, i2.lE, i2.lX, i2.lG, i2.lB,
      i2.lA, i2.rcur, i2.out, i2.kin, i2.kc⟩, i3, by rw [DS.set_env_ne _ _ (by decide)]; exact i4,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i5, by rw [DS.set_env_ne _ _ (by decide)]; exact i6,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i7⟩)
    ⟨hI, hSt, by rw [hip]; simp, by rw [hc0]; simp, by rw [hc0]; simp, by rw [hu0]; simp, by rw [hu0]⟩ hI.NC ?_
  · refine Hs.mono hl le_rfl ?_
    rintro b ⟨⟨i1, i2, -, i4, -, i6, -⟩, -, -⟩
    exact ⟨i1, i2, i4, i6⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7⟩ hek hem
    have hb := cellBody_spec c p wt hadm hs w hw S gP sysPr tg ts hG hS hK Big hBig hWd hLB pre hinp k hk e i1 i2
      i3 hek i5 (by omega)
    refine Hs.mono hb ?_ ?_
    · unfold cellCostU
      rw [ctrL_len c p wt (cellOf wt.I k) (cellOf wt.I 0), kxL_len c p wt (cellOf wt.I k) (cellOf wt.I 0),
        gWork_eq c p wt (cellOf wt.I k) (cellOf wt.I 0)]
    · rintro d ⟨d1, d2, d3, d4, d5, d6, d7⟩
      refine ⟨⟨d1, d2, d3, ?_, d5, ?_, ?_⟩, by rw [d7, hek], by rw [d1.NC, ← hem, i1.NC]⟩
      · rw [d4, i4, Finset.sum_range_succ]
      · rw [d6, i6, Finset.sum_range_succ]
      · rw [d6]; split_ifs <;> omega

end Lp

end NearCubicGates.Close.Cells
