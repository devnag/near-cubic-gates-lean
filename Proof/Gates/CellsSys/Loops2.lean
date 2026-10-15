import Proof.Gates.CellsSys.Loops

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

theorem parts_pidx (c : Call) (i : ℕ) (hi : i < (parts c).length) :
    (if (parts c)[i] = some true then 1 else 0) = i := by
  by_cases h : c.kind = .parity
  · have hl : (parts c).length = 2 := by simp [parts, h]
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [parts, h]
  · have hl : (parts c).length = 1 := by simp [parts, h]
    have : i = 0 := by omega
    subst this; simp [parts, h]

/-- The joint counts of a part. -/
noncomputable def Fp (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) : List ℕ :=
  (List.range (BN c p)).flatMap (Rw c p wt y part)

/-- The count of a part. -/
noncomputable def Gp (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) : ℚ :=
  ((List.range (BN c p)).map (Tm c p wt y part)).sum

def PVar (x : Fin VV) : Prop := StepVar x ∨ x = tI ∨ x = pI

/-- The invariant of the loop over parts. -/
structure PJ (S : SolveMachine) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (a0 a2 : DS VV MM)
    (i : ℕ) (b : DS VV MM) : Prop where
  keep : Keep a0 b
  kin : b.kin = []
  w : b.env wW = wWin p
  nD : b.env nDg = nDig c p
  sA : (b.ram sA).drop (b.rc sA) = ((parts c).drop i).flatMap (Fp c p wt y)
  cnt : ((b.env vCnt : ℕ) : ℚ) = (a2.env vCnt : ℚ) + (((parts c).take i).map (Gp c p wt y)).sum
  cb : b.env vCnt ≤ a2.env vCnt + i * (BN c p * (PT c * 2 ^ c.n))
  fr : ∀ x : Fin VV, ¬ PVar x → b.env x = a2.env x

theorem PJ.set {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {a0 a2 : DS VV MM}
    {i : ℕ} {b : DS VV MM} (h : PJ S c p wt y a0 a2 i b) (v : ℕ) : PJ S c p wt y a0 a2 i (b.set pI v) :=
  ⟨⟨h.keep.ram, h.keep.ip, h.keep.out, RcOK.same h.keep.rc (Same.set b pI v), fun x hx hc => by
      rw [DS.set_env_ne _ _ (fun e => by subst e; revert hx; decide)]; exact h.keep.env x hx hc⟩,
    h.kin, by rw [DS.set_env_ne _ _ (by decide)]; exact h.w, by rw [DS.set_env_ne _ _ (by decide)]; exact h.nD,
    h.sA, by rw [DS.set_env_ne _ _ (by decide)]; exact h.cnt, by rw [DS.set_env_ne _ _ (by decide)]; exact h.cb,
    fun x hx => by rw [DS.set_env_ne _ _ (fun e => hx (Or.inr (Or.inr e)))]; exact h.fr x hx⟩

/-- The cost of the loop over counter values. -/
def tCost (pr : PrFrag) (cf : CallFrag) (S : SolveMachine) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  BN c p * (stepCost pr cf S C c p Big + 4) + 4

theorem pLoop_spec (pr : PrFrag) (cf : CallFrag) {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n}
    {y : Cells wt.I} {Big : ℕ} {a0 a2 : DS VV MM} (G : Glob S C c p wt y Big) (h0 : SysPre S C c p wt y a0)
    (hK : Keep a0 a2) (hw : a2.env wW = wWin p) (hnD : a2.env nDg = nDig c p) (hkin : a2.kin = [])
    (hnP : a2.env nPa = (parts c).length) (hA : (a2.ram sA).drop (a2.rc sA) = rowVals c p wt y)
    (hroom : a2.env vCnt + (2 * BN c p + 1) * (PT c * 2 ^ c.n) < 2 ^ C.Wd) :
    Hs C (pLoop pr cf) a2 ((parts c).length * (tCost pr cf S C c p Big + 4) + 4) (fun b =>
      ((b.env vCnt : ℕ) : ℚ) = (a2.env vCnt : ℚ) + ((parts c).map (Gp c p wt y)).sum ∧
      b.kin = [] ∧ Keep a0 b ∧ ∀ x : Fin VV, ¬ PVar x → b.env x = a2.env x) := by
  have hpl : (parts c).length ≤ 2 := parts_length_le c
  have hW1 : 4 ≤ 2 ^ C.Wd := by have := (nums G).q64; have := (nums G).q8; omega
  refine Hs.mono (forS_spec' (C := C) pI nPa (by decide) (tLoop pr cf) a2 (parts c).length (by omega)
    (PJ S c p wt y a0 a2) (tCost pr cf S C c p Big) (fun k b v h => h.set v)
    ⟨hK, hkin, hw, hnD, by rw [hA, rowVals_eq]; rfl, by simp, by omega, fun x _ => rfl⟩ hnP ?_) le_rfl ?_
  · intro i hi b hI hbi hbn
    have hpart : (parts c)[i] ∈ parts c := List.getElem_mem _
    have hpI : b.env pI = if (parts c)[i] = some true then 1 else 0 := by rw [parts_pidx c i hi]; exact hbi
    have hA' : (b.ram sA).drop (b.rc sA) = (List.range (BN c p)).flatMap (Rw c p wt y (parts c)[i]) ++
        ((parts c).drop (i + 1)).flatMap (Fp c p wt y) := by
      rw [hI.sA, List.drop_eq_getElem_cons hi, List.flatMap_cons]; rfl
    have hi1 : i ≤ 1 := by omega
    have hroom' : b.env vCnt + (BN c p + 1) * (PT c * 2 ^ c.n) < 2 ^ C.Wd := by
      have h1 := hI.cb
      have h2 : i * (BN c p * (PT c * 2 ^ c.n)) ≤ 1 * (BN c p * (PT c * 2 ^ c.n)) := Nat.mul_le_mul_right _ hi1
      have h3 : (BN c p + 1) * (PT c * 2 ^ c.n) = BN c p * (PT c * 2 ^ c.n) + PT c * 2 ^ c.n := by ring
      have h4 : (2 * BN c p + 1) * (PT c * 2 ^ c.n) = 2 * (BN c p * (PT c * 2 ^ c.n)) + PT c * 2 ^ c.n := by ring
      omega
    refine Hs.mono (tLoop_spec (C := C) pr cf G h0 hI.keep (parts c)[i] hpart hI.w hI.nD hpI hI.kin _ hA' hroom')
      (by unfold tCost; omega) ?_
    rintro g ⟨g1, g2, g3, g4, g5⟩
    have nS : ∀ x : Fin VV, ¬ PVar x → ¬ (StepVar x ∨ x = tI) := fun x hx h => by
      rcases h with h | h
      · exact hx (Or.inl h)
      · exact hx (Or.inr (Or.inl h))
    have hnP : ¬ (StepVar pI ∨ pI = tI) := by unfold StepVar FragVar; decide
    have hnN : ¬ (StepVar nPa ∨ nPa = tI) := by unfold StepVar FragVar; decide
    have hsum := sum_Tm_le c p wt y (parts c)[i] (BN c p)
    have hsum0 := sum_Tm_nonneg c p wt y (parts c)[i] (BN c p)
    have htake : ((parts c).take (i + 1)).map (Gp c p wt y) =
        ((parts c).take i).map (Gp c p wt y) ++ [Gp c p wt y (parts c)[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    refine ⟨⟨g4, g2, by rw [g5 wW (by unfold StepVar FragVar; decide)]; exact hI.w,
      by rw [g5 nDg (by unfold StepVar FragVar; decide)]; exact hI.nD, g3, ?_, ?_,
      fun x hx => by rw [g5 x (nS x hx)]; exact hI.fr x hx⟩, by rw [g5 pI hnP]; exact hbi,
      by rw [g5 nPa hnN]; exact hbn⟩
    · rw [g1, hI.cnt, htake, List.sum_append]; simp [Gp]; ring
    · have hq : ((g.env vCnt : ℕ) : ℚ) ≤ ((a2.env vCnt + (i + 1) * (BN c p * (PT c * 2 ^ c.n)) : ℕ) : ℚ) := by
        rw [g1]
        have hb : ((b.env vCnt : ℕ) : ℚ) ≤ ((a2.env vCnt + i * (BN c p * (PT c * 2 ^ c.n)) : ℕ) : ℚ) := by
          exact_mod_cast hI.cb
        push_cast at hb hsum ⊢
        nlinarith
      exact_mod_cast hq
  · rintro b ⟨hI, _, _⟩
    refine ⟨by rw [hI.cnt, List.take_of_length_le le_rfl], hI.kin, hI.keep, hI.fr⟩

end NearCubicGates.Close.Cells.SystemsPhase
