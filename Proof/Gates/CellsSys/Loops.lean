import Proof.Gates.CellsSys.Step

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def tLoop (pr : PrFrag) (cf : CallFrag) : St VV MM := forS tI vBN (sysStep pr cf)
def pLoop (pr : PrFrag) (cf : CallFrag) : St VV MM := forS pI nPa (tLoop pr cf)

/-- The point bound of a box. -/
abbrev PT (c : Call) : ℕ := (2 * c.W + 1) ^ 2

/-- The cost of one system step. -/
def stepCost (pr : PrFrag) (cf : CallFrag) (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  boxesCost p.J + (pr.cost S C c p Big + cf.cost S C c p Big + 1) + 1

theorem Tm_le (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (t : ℕ) :
    Tm c p wt y part t ≤ ((PT c * 2 ^ c.n : ℕ) : ℚ) := by
  have h := (Tm_bounds c p wt y part t).2
  have h2 := pts_le c p wt y (kap c p wt y t)
  have : (ptsOf c p wt y (kap c p wt y t)).length * 2 ^ c.n ≤ PT c * 2 ^ c.n := Nat.mul_le_mul_right _ h2
  calc _ ≤ _ := h
    _ ≤ _ := by exact_mod_cast this

theorem sum_Tm_le (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (k : ℕ) :
    ((List.range k).map (Tm c p wt y part)).sum ≤ ((k * (PT c * 2 ^ c.n) : ℕ) : ℚ) := by
  have := List.sum_le_card_nsmul ((List.range k).map (Tm c p wt y part)) ((PT c * 2 ^ c.n : ℕ) : ℚ)
    (fun x hx => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx; exact Tm_le c p wt y part t)
  rw [List.length_map, List.length_range, nsmul_eq_mul] at this
  push_cast at this ⊢; linarith

theorem sum_Tm_nonneg (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (k : ℕ) :
    0 ≤ ((List.range k).map (Tm c p wt y part)).sum :=
  List.sum_nonneg (fun x hx => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx; exact (Tm_bounds c p wt y part t).1)

/-- The invariant of the loop over counter values. -/
structure TI (S : SolveMachine) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (a0 a1 : DS VV MM)
    (part : Option Bool) (Rest : List ℕ) (k : ℕ) (b : DS VV MM) : Prop where
  keep : Keep a0 b
  kin : b.kin = []
  w : b.env wW = wWin p
  nD : b.env nDg = nDig c p
  pI : b.env pI = if part = some true then 1 else 0
  sA : (b.ram sA).drop (b.rc sA) = ((List.range (BN c p)).drop k).flatMap (Rw c p wt y part) ++ Rest
  cnt : ((b.env vCnt : ℕ) : ℚ) = (a1.env vCnt : ℚ) + ((List.range k).map (Tm c p wt y part)).sum
  fr : ∀ x : Fin VV, ¬ (StepVar x ∨ x = tI) → b.env x = a1.env x

theorem TI.set {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {a0 a1 : DS VV MM}
    {part : Option Bool} {Rest : List ℕ} {k : ℕ} {b : DS VV MM} (h : TI S c p wt y a0 a1 part Rest k b) (v : ℕ) :
    TI S c p wt y a0 a1 part Rest k (b.set tI v) :=
  ⟨⟨h.keep.ram, h.keep.ip, h.keep.out, RcOK.same h.keep.rc (Same.set b tI v), fun x hx hc => by
      rw [DS.set_env_ne _ _ (fun e => by subst e; revert hx; decide)]; exact h.keep.env x hx hc⟩,
    h.kin, by rw [DS.set_env_ne _ _ (by decide)]; exact h.w, by rw [DS.set_env_ne _ _ (by decide)]; exact h.nD,
    by rw [DS.set_env_ne _ _ (by decide)]; exact h.pI, h.sA, by rw [DS.set_env_ne _ _ (by decide)]; exact h.cnt,
    fun x hx => by rw [DS.set_env_ne _ _ (fun e => hx (Or.inr e))]; exact h.fr x hx⟩

theorem drop_range_cons (N k : ℕ) (hk : k < N) : (List.range N).drop k = k :: (List.range N).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk), List.getElem_range]

theorem tLoop_spec (pr : PrFrag) (cf : CallFrag) {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n}
    {y : Cells wt.I} {Big : ℕ} {a0 a1 : DS VV MM} (G : Glob S C c p wt y Big) (h0 : SysPre S C c p wt y a0)
    (hK : Keep a0 a1) (part : Option Bool) (hpart : part ∈ parts c) (hw : a1.env wW = wWin p)
    (hnD : a1.env nDg = nDig c p) (hpI : a1.env pI = if part = some true then 1 else 0) (hkin : a1.kin = [])
    (Rest : List ℕ) (hA : (a1.ram sA).drop (a1.rc sA) = (List.range (BN c p)).flatMap (Rw c p wt y part) ++ Rest)
    (hroom : a1.env vCnt + (BN c p + 1) * (PT c * 2 ^ c.n) < 2 ^ C.Wd) :
    Hs C (tLoop pr cf) a1 (BN c p * (stepCost pr cf S C c p Big + 4) + 4) (fun b =>
      ((b.env vCnt : ℕ) : ℚ) = (a1.env vCnt : ℚ) + ((List.range (BN c p)).map (Tm c p wt y part)).sum ∧
      b.kin = [] ∧ (b.ram sA).drop (b.rc sA) = Rest ∧ Keep a0 b ∧
      ∀ x : Fin VV, ¬ (StepVar x ∨ x = tI) → b.env x = a1.env x) := by
  have hBNW : BN c p < 2 ^ C.Wd := by
    have := (nums G).pw
    have h1 : wWin p ^ nDig c p ≤ wWin p ^ nDig c p * (wWin p + 1) := Nat.le_mul_of_pos_right _ (by omega)
    exact lt_of_le_of_lt h1 this
  have hBN : a1.env vBN = BN c p := (hK.ev (x := vBN) (by decide) (by decide)).trans h0.BN
  refine Hs.mono (forS_spec' (C := C) tI vBN (by decide) (sysStep pr cf) a1 (BN c p) hBNW
    (TI S c p wt y a0 a1 part Rest) (stepCost pr cf S C c p Big) (fun k b v h => h.set v)
    ⟨hK, hkin, hw, hnD, hpI, by rw [List.drop_zero]; exact hA, by simp, fun x _ => rfl⟩ hBN ?_) le_rfl ?_
  · intro k hk b hI hbk hbN
    -- room for the counter
    have hcq : ((b.env vCnt : ℕ) : ℚ) ≤ ((a1.env vCnt + k * (PT c * 2 ^ c.n) : ℕ) : ℚ) := by
      rw [hI.cnt]; push_cast; have := sum_Tm_le c p wt y part k; push_cast at this; linarith
    have hcn : b.env vCnt ≤ a1.env vCnt + k * (PT c * 2 ^ c.n) := by exact_mod_cast hcq
    have hpts := pts_le c p wt y (kap c p wt y k)
    have hpts2 : (ptsOf c p wt y (kap c p wt y k)).length * 2 ^ c.n ≤ PT c * 2 ^ c.n :=
      Nat.mul_le_mul_right _ hpts
    have hk1 : k * (PT c * 2 ^ c.n) + PT c * 2 ^ c.n ≤ (BN c p + 1) * (PT c * 2 ^ c.n) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have hA' : (b.ram sA).drop (b.rc sA) = Rw c p wt y part k ++
        (((List.range (BN c p)).drop (k + 1)).flatMap (Rw c p wt y part) ++ Rest) := by
      rw [hI.sA, drop_range_cons _ _ hk, List.flatMap_cons, List.append_assoc]
    refine Hs.mono (sysStep_spec (C := C) pr cf G h0 hI.keep part hpart k hk hbk hI.w hI.nD hI.pI hI.kin _ hA'
      (by omega)) (by unfold stepCost; omega) ?_
    rintro g ⟨g1, g2, g3, g4, g5⟩
    have nS : ∀ x : Fin VV, ¬ (StepVar x ∨ x = tI) → ¬ StepVar x := fun x hx h => hx (Or.inl h)
    refine ⟨⟨g4, g2, by rw [g5 wW (by unfold StepVar FragVar; decide)]; exact hI.w,
      by rw [g5 nDg (by unfold StepVar FragVar; decide)]; exact hI.nD,
      by rw [g5 pI (by unfold StepVar FragVar; decide)]; exact hI.pI, g3, ?_,
      fun x hx => by rw [g5 x (nS x hx)]; exact hI.fr x hx⟩, by rw [g5 tI (by unfold StepVar FragVar; decide)]; exact hbk,
      by rw [g5 vBN (by unfold StepVar FragVar; decide)]; exact hbN⟩
    rw [g1, hI.cnt, List.range_succ, List.map_append, List.sum_append]
    simp; ring
  · rintro b ⟨hI, _, _⟩
    refine ⟨hI.cnt, hI.kin, by rw [hI.sA, List.drop_eq_nil_of_le (by simp)]; simp, hI.keep, hI.fr⟩

end NearCubicGates.Close.Cells.SystemsPhase
