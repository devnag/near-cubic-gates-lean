import Proof.Gates.CellsSys.Val

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def sysStep (pr : PrFrag) (cf : CallFrag) : St VV MM := .seq boxes (.seq pr.prog cf.prog)

/-- The variables a system step may change. -/
def StepVar (x : Fin VV) : Prop := FragVar x ∨ x ∈ boxesT ∨ x = vCnt

theorem boxesT_range : ∀ x ∈ boxesT, (50 ≤ x.val ∧ x.val ≤ 99) ∨ (3 ≤ x.val ∧ x.val ≤ 19) := by decide

theorem not_frag {x : Fin VV} (h : (20 ≤ x.val ∧ x.val ≤ 86) ∨ x.val = 99 ∨ x.val < 3 ∨ 99 < x.val) :
    ¬ FragVar x := by unfold FragVar; omega

theorem not_box {x : Fin VV} (h : x.val < 50 ∧ (x.val < 3 ∨ 19 < x.val)) : x ∉ boxesT := fun hm => by
  have := boxesT_range x hm; omega

theorem keep_of {a0 d g : DS VV MM} (hK : Keep a0 d) (hram : g.ram = d.ram) (hip : g.ip = d.ip) (hout : g.out = d.out)
    (hrc : RcOK g) (hfr : ∀ x : Fin VV, (x.val < 3 ∨ (20 ≤ x.val ∧ x.val < 50)) → x ≠ vCnt → g.env x = d.env x) :
    Keep a0 g :=
  ⟨hram.trans hK.ram, hip.trans hK.ip, hout.trans hK.out, hrc, fun x hx hc => (hfr x hx hc).trans (hK.env x hx hc)⟩

theorem boxIn_of {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {a0 d : DS VV MM}
    (h0 : SysPre S C c p wt y a0) (hK : Keep a0 d) (t : ℕ) (htI : d.env tI = t) (hw : d.env wW = wWin p)
    (hnD : d.env nDg = nDig c p) : BoxIn c p wt y t d :=
  ⟨Keep.cst h0 hK, hK.rc, htI, (hK.ev (x := vJ') (by decide) (by decide)).trans h0.J,
    (hK.ev (x := vHE) (by decide) (by decide)).trans h0.hE, hw, hnD,
    (hK.ev (x := vM1) (by decide) (by decide)).trans h0.M1, (hK.ev (x := vA) (by decide) (by decide)).trans h0.A,
    (hK.ev (x := vLam) (by decide) (by decide)).trans h0.Lam,
    (hK.ev (x := vTW0) (by decide) (by decide)).trans h0.TW0, (hK.ev (x := vTW1) (by decide) (by decide)).trans h0.TW1,
    (hK.ev (x := vRC) (by decide) (by decide)).trans h0.rc, by rw [hK.ram]; exact h0.tails,
    by rw [hK.ram]; exact h0.ctrs, by rw [hK.ram]; exact h0.kx⟩

theorem boxV_of {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {κ : Role c × Fin p.J → ℤ}
    {a b : DS VV MM} (h : BoxV c p wt y κ a) (hfr : ∀ x : Fin VV, ¬ FragVar x → b.env x = a.env x) :
    BoxV c p wt y κ b :=
  ⟨by rw [hfr l0P (not_frag (by decide))]; exact h.l0p, by rw [hfr l0N (not_frag (by decide))]; exact h.l0n,
   by rw [hfr n0 (not_frag (by decide))]; exact h.n0e, by rw [hfr l1P (not_frag (by decide))]; exact h.l1p,
   by rw [hfr l1N (not_frag (by decide))]; exact h.l1n, by rw [hfr n1 (not_frag (by decide))]; exact h.n1e⟩

theorem sysStep_spec (pr : PrFrag) (cf : CallFrag) {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n}
    {y : Cells wt.I} {Big : ℕ} {a0 d : DS VV MM} (G : Glob S C c p wt y Big) (h0 : SysPre S C c p wt y a0)
    (hK : Keep a0 d) (part : Option Bool) (hpart : part ∈ parts c) (t : ℕ) (ht : t < BN c p)
    (htI : d.env tI = t) (hw : d.env wW = wWin p) (hnD : d.env nDg = nDig c p)
    (hpI : d.env pI = if part = some true then 1 else 0) (hkin : d.kin = []) (rest : List ℕ)
    (hA : (d.ram sA).drop (d.rc sA) = Rw c p wt y part t ++ rest)
    (hcnt : d.env vCnt + (ptsOf c p wt y (kap c p wt y t)).length * 2 ^ c.n < 2 ^ C.Wd) :
    Hs C (sysStep pr cf) d (boxesCost p.J + (pr.cost S C c p Big + cf.cost S C c p Big + 1) + 1) (fun g =>
      ((g.env vCnt : ℕ) : ℚ) = (d.env vCnt : ℚ) + Tm c p wt y part t ∧ g.kin = [] ∧
      (g.ram sA).drop (g.rc sA) = rest ∧ Keep a0 g ∧ ∀ x : Fin VV, ¬ StepVar x → g.env x = d.env x) := by
  obtain ⟨cT, hs⟩ := G.spec
  have hκ := kap_mem c p wt y hs t ht
  have N := nums G
  refine Hs.seq (boxes_spec N t d (boxIn_of h0 hK t htI hw hnD)) (fun e1 ⟨b1, b2, b3, b4⟩ => ?_)
  have hK1 : Keep a0 e1 := keep_of hK b3.ram b3.ip b3.out b4 (fun x hx hc => b2 x (not_box (by omega)))
  have hA1 : (e1.ram sA).drop (e1.rc sA) = (rowsOf c p wt y (kap c p wt y t) part).map (fun row => row.2.2) ++ rest := by
    rw [b3.ram, b3.rcA]; exact hA
  refine Hs.seq (pr.spec S C c p wt y Big a0 e1 part (kap c p wt y t) rest G h0 hK1 hκ hpart b1
    (by rw [b3.kin]; exact hkin) hA1) (fun e2 ⟨c1, c2, c3, c4, c5, c6, c7⟩ => ?_)
  have hK2 : Keep a0 e2 := keep_of hK1 c3 c4 c5 c6 (fun x hx hc => c7 x (by unfold FragVar; omega))
  have e2pI : e2.env pI = if part = some true then 1 else 0 := by
    rw [c7 pI (not_frag (by decide)), b2 pI (by decide)]; exact hpI
  have e2cnt : e2.env vCnt = d.env vCnt := by
    rw [c7 vCnt (not_frag (by decide)), b2 vCnt (not_box (by decide))]
  refine Hs.mono (cf.spec S C c p wt y Big a0 e2 part (kap c p wt y t) G h0 hK2 hκ hpart (boxV_of b1 c7) e2pI c1
    (by rw [e2cnt]; exact hcnt)) le_rfl ?_
  rintro g ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩
  refine ⟨by rw [g1, e2cnt]; rfl, g2, by rw [g3, g6]; exact c2, keep_of hK2 g3 g4 g5 g7 (fun x hx hc => g8 x
    (by unfold FragVar; omega) hc), fun x hx => ?_⟩
  have h1 : ¬ FragVar x := fun h => hx (Or.inl h)
  have h2 : x ∉ boxesT := fun h => hx (Or.inr (Or.inl h))
  have h3 : x ≠ vCnt := fun h => hx (Or.inr (Or.inr h))
  rw [g8 x h1 h3, c7 x h1, b2 x h2]

end NearCubicGates.Close.Cells.SystemsPhase
