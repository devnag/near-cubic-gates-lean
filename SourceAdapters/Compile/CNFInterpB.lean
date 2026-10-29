import SourceAdapters.Compile.CNFInterpA

/-!
# Token interpreter, part B: the Tseitin clauses of one node

proof of `lem:multitape-refuter`: each gate contributes its fixed exact-three Tseitin clauses (`CNFRpn.rcl`, equal to the released
`circuitInputNodeClauses`). With the gate variable `n + idx` in `iG` and the operand variables in `iX`/`iY` (or the
input index / constant in `iPl`), `clCstP`, `clInpP`, `clNegP`, `clConjP`, `clDisjP` append exactly
`(rcl n idx node).map encode` to the clause store.
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

theorem rcl_cst (n i : ℕ) (b : Bool) :
    (rcl n i (.cst b)).map Encodable.encode = [ccode b.toNat (n + i) b.toNat (n + i) b.toNat (n + i)] := by
  cases b <;> simp [rcl, positiveUnit, negativeUnit, positive, negative, encode_triple]

theorem rcl_inp (n i j : ℕ) :
    (rcl n i (.inp j)).map Encodable.encode = [ccode 0 (n + i) 1 j 1 j, ccode 1 (n + i) 0 j 0 j] := by
  simp [rcl, positive, negative, encode_triple]

theorem rcl_neg (n i c : ℕ) :
    (rcl n i (.neg c)).map Encodable.encode = [ccode 0 (n + i) 0 (n + c) 0 (n + c), ccode 1 (n + i) 1 (n + c) 1 (n + c)] := by
  simp [rcl, positive, negative, encode_triple]

theorem rcl_conj (n i l r : ℕ) :
    (rcl n i (.conj l r)).map Encodable.encode = [ccode 0 (n + i) 1 (n + l) 1 (n + l),
      ccode 0 (n + i) 1 (n + r) 1 (n + r), ccode 1 (n + i) 0 (n + l) 0 (n + r)] := by
  simp [rcl, positive, negative, encode_triple]

theorem rcl_disj (n i l r : ℕ) :
    (rcl n i (.disj l r)).map Encodable.encode = [ccode 1 (n + i) 0 (n + l) 0 (n + l),
      ccode 1 (n + i) 0 (n + r) 0 (n + r), ccode 0 (n + i) 1 (n + l) 1 (n + r)] := by
  simp [rcl, positive, negative, encode_triple]

/-- Two clauses in sequence. -/
theorem clause2_spec (P1 P2 : St VV MM) (a : DS VV MM) (k1 k2 : ℕ) (hc0 : a.rc sCL = (a.ram sCL).length)
    (h1 : ∀ b : DS VV MM, b.rc sCL = (b.ram sCL).length → (∀ y, y ∉ clT → b.env y = a.env y) →
      Hs C P1 b 70 (fun d => ExtS sCL b d [k1] ∧ Fr b d clT))
    (h2 : ∀ b : DS VV MM, b.rc sCL = (b.ram sCL).length → (∀ y, y ∉ clT → b.env y = a.env y) →
      Hs C P2 b 70 (fun d => ExtS sCL b d [k2] ∧ Fr b d clT)) :
    Hs C (.seq P1 P2) a 141 (fun d => ExtS sCL a d [k1, k2] ∧ Fr a d clT) := by
  refine Hs.seqc (t1 := 70) (t2 := 70) (h1 a hc0 (fun _ _ => rfl)) (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hcb : b.rc sCL = (b.ram sCL).length := by rw [hb1.rc, hb1.st, hc0]; simp
  refine Hs.mono (h2 b hcb (fun y hy => hb2 y hy)) le_rfl ?_
  rintro d ⟨hd1, hd2⟩
  exact ⟨(hb1.trans hd1).congr (by simp), hb2.trans hd2⟩

/-- `clauseP` with the values of its registers named. -/
theorem clauseP_at (p1 x1 p2 x2 p3 x3 : Fin VV) (hr : ∀ y ∈ [p1, x1, p2, x2, p3, x3], y ∉ clT)
    (h1 : p1 ≠ x1) (h2 : p2 ≠ x2) (h3 : p3 ≠ x3) (a : DS VV MM) (hz : a.env vZ = 0)
    (hend : a.rc sCL = (a.ram sCL).length) (B1 X1 B2 X2 B3 X3 : ℕ) (e1 : a.env p1 = B1) (e2 : a.env x1 = X1)
    (e3 : a.env p2 = B2) (e4 : a.env x2 = X2) (e5 : a.env p3 = B3) (e6 : a.env x3 = X3)
    (hW : ccode B1 X1 B2 X2 B3 X3 < 2 ^ C.Wd) :
    Hs C (clauseP p1 x1 p2 x2 p3 x3) a 70 (fun b => ExtS sCL a b [ccode B1 X1 B2 X2 B3 X3] ∧ Fr a b clT) := by
  subst e1 e2 e3 e4 e5 e6
  exact clauseP_spec p1 x1 p2 x2 p3 x3 hr h1 h2 h3 a hz hend hW

/-- Clauses of a constant node (`iPl` = the constant as `0/1`, `iG` = gate variable). -/
def clCstP : St VV MM := clauseP iPl iG iPl iG iPl iG

theorem clCstP_spec (a : DS VV MM) (n i : ℕ) (b : Bool) (hz : a.env vZ = 0) (hend : a.rc sCL = (a.ram sCL).length)
    (hg : a.env iG = n + i) (hp : a.env iPl = b.toNat) (hW : ∀ c ∈ (rcl n i (.cst b)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C clCstP a 70 (fun d => ExtS sCL a d ((rcl n i (.cst b)).map Encodable.encode) ∧ Fr a d clT) := by
  rw [rcl_cst] at hW ⊢
  exact clauseP_at iPl iG iPl iG iPl iG (by decide) (by decide) (by decide) (by decide) a hz hend _ _ _ _ _ _
    hp hg hp hg hp hg (hW _ (by simp))

/-- Clauses of an input node (`iPl` = input index). -/
def clInpP : St VV MM := .seq (clauseP vZ iG v1 iPl v1 iPl) (clauseP v1 iG vZ iPl vZ iPl)

theorem clInpP_spec (a : DS VV MM) (n i j : ℕ) (hz : a.env vZ = 0) (h1 : a.env v1 = 1)
    (hend : a.rc sCL = (a.ram sCL).length) (hg : a.env iG = n + i) (hp : a.env iPl = j)
    (hW : ∀ c ∈ (rcl n i (.inp j)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C clInpP a 141 (fun d => ExtS sCL a d ((rcl n i (.inp j)).map Encodable.encode) ∧ Fr a d clT) := by
  rw [rcl_inp] at hW ⊢
  have fz := fun (b : DS VV MM) (hb : ∀ y, y ∉ clT → b.env y = a.env y) (y : Fin VV) (hy : y ∉ clT) => hb y hy
  exact clause2_spec _ _ a _ _ hend
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf vZ (by decide), hz]) (by rw [hf iG (by decide), hg])
      (by rw [hf v1 (by decide), h1]) (by rw [hf iPl (by decide), hp]) (by rw [hf v1 (by decide), h1])
      (by rw [hf iPl (by decide), hp]) (hW _ (by simp)))
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf v1 (by decide), h1]) (by rw [hf iG (by decide), hg])
      (by rw [hf vZ (by decide), hz]) (by rw [hf iPl (by decide), hp]) (by rw [hf vZ (by decide), hz])
      (by rw [hf iPl (by decide), hp]) (hW _ (by simp)))

/-- Clauses of a negation (`iX` = operand variable). -/
def clNegP : St VV MM := .seq (clauseP vZ iG vZ iX vZ iX) (clauseP v1 iG v1 iX v1 iX)

theorem clNegP_spec (a : DS VV MM) (n i c : ℕ) (hz : a.env vZ = 0) (h1 : a.env v1 = 1)
    (hend : a.rc sCL = (a.ram sCL).length) (hg : a.env iG = n + i) (hx : a.env iX = n + c)
    (hW : ∀ k ∈ (rcl n i (.neg c)).map Encodable.encode, k < 2 ^ C.Wd) :
    Hs C clNegP a 141 (fun d => ExtS sCL a d ((rcl n i (.neg c)).map Encodable.encode) ∧ Fr a d clT) := by
  rw [rcl_neg] at hW ⊢
  exact clause2_spec _ _ a _ _ hend
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf vZ (by decide), hz]) (by rw [hf iG (by decide), hg])
      (by rw [hf vZ (by decide), hz]) (by rw [hf iX (by decide), hx]) (by rw [hf vZ (by decide), hz])
      (by rw [hf iX (by decide), hx]) (hW _ (by simp)))
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf v1 (by decide), h1]) (by rw [hf iG (by decide), hg])
      (by rw [hf v1 (by decide), h1]) (by rw [hf iX (by decide), hx]) (by rw [hf v1 (by decide), h1])
      (by rw [hf iX (by decide), hx]) (hW _ (by simp)))

/-- Three clauses in sequence. -/
theorem clause3_spec (P1 P2 P3 : St VV MM) (a : DS VV MM) (k1 k2 k3 : ℕ) (hc0 : a.rc sCL = (a.ram sCL).length)
    (h1 : ∀ b : DS VV MM, b.rc sCL = (b.ram sCL).length → (∀ y, y ∉ clT → b.env y = a.env y) →
      Hs C P1 b 70 (fun d => ExtS sCL b d [k1] ∧ Fr b d clT))
    (h2 : ∀ b : DS VV MM, b.rc sCL = (b.ram sCL).length → (∀ y, y ∉ clT → b.env y = a.env y) →
      Hs C P2 b 70 (fun d => ExtS sCL b d [k2] ∧ Fr b d clT))
    (h3 : ∀ b : DS VV MM, b.rc sCL = (b.ram sCL).length → (∀ y, y ∉ clT → b.env y = a.env y) →
      Hs C P3 b 70 (fun d => ExtS sCL b d [k3] ∧ Fr b d clT)) :
    Hs C (.seq P1 (.seq P2 P3)) a 212 (fun d => ExtS sCL a d [k1, k2, k3] ∧ Fr a d clT) := by
  refine Hs.seqc (t1 := 70) (t2 := 141) (h1 a hc0 (fun _ _ => rfl)) (fun b hb => ?_) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hcb : b.rc sCL = (b.ram sCL).length := by rw [hb1.rc, hb1.st, hc0]; simp
  refine Hs.mono (clause2_spec P2 P3 b k2 k3 hcb (fun d hd hf => h2 d hd (fun y hy => (hf y hy).trans (hb2 y hy)))
    (fun d hd hf => h3 d hd (fun y hy => (hf y hy).trans (hb2 y hy)))) le_rfl ?_
  rintro d ⟨hd1, hd2⟩
  exact ⟨(hb1.trans hd1).congr (by simp), hb2.trans hd2⟩

/-- Clauses of a conjunction (`iX`, `iY` = operand variables). -/
def clConjP : St VV MM := .seq (clauseP vZ iG v1 iX v1 iX) (.seq (clauseP vZ iG v1 iY v1 iY) (clauseP v1 iG vZ iX vZ iY))

theorem clConjP_spec (a : DS VV MM) (n i l r : ℕ) (hz : a.env vZ = 0) (h1 : a.env v1 = 1)
    (hend : a.rc sCL = (a.ram sCL).length) (hg : a.env iG = n + i) (hx : a.env iX = n + l) (hy : a.env iY = n + r)
    (hW : ∀ k ∈ (rcl n i (.conj l r)).map Encodable.encode, k < 2 ^ C.Wd) :
    Hs C clConjP a 212 (fun d => ExtS sCL a d ((rcl n i (.conj l r)).map Encodable.encode) ∧ Fr a d clT) := by
  rw [rcl_conj] at hW ⊢
  exact clause3_spec _ _ _ a _ _ _ hend
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf vZ (by decide), hz]) (by rw [hf iG (by decide), hg])
      (by rw [hf v1 (by decide), h1]) (by rw [hf iX (by decide), hx]) (by rw [hf v1 (by decide), h1])
      (by rw [hf iX (by decide), hx]) (hW _ (by simp)))
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf vZ (by decide), hz]) (by rw [hf iG (by decide), hg])
      (by rw [hf v1 (by decide), h1]) (by rw [hf iY (by decide), hy]) (by rw [hf v1 (by decide), h1])
      (by rw [hf iY (by decide), hy]) (hW _ (by simp)))
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf v1 (by decide), h1]) (by rw [hf iG (by decide), hg])
      (by rw [hf vZ (by decide), hz]) (by rw [hf iX (by decide), hx]) (by rw [hf vZ (by decide), hz])
      (by rw [hf iY (by decide), hy]) (hW _ (by simp)))

/-- Clauses of a disjunction. -/
def clDisjP : St VV MM := .seq (clauseP v1 iG vZ iX vZ iX) (.seq (clauseP v1 iG vZ iY vZ iY) (clauseP vZ iG v1 iX v1 iY))

theorem clDisjP_spec (a : DS VV MM) (n i l r : ℕ) (hz : a.env vZ = 0) (h1 : a.env v1 = 1)
    (hend : a.rc sCL = (a.ram sCL).length) (hg : a.env iG = n + i) (hx : a.env iX = n + l) (hy : a.env iY = n + r)
    (hW : ∀ k ∈ (rcl n i (.disj l r)).map Encodable.encode, k < 2 ^ C.Wd) :
    Hs C clDisjP a 212 (fun d => ExtS sCL a d ((rcl n i (.disj l r)).map Encodable.encode) ∧ Fr a d clT) := by
  rw [rcl_disj] at hW ⊢
  exact clause3_spec _ _ _ a _ _ _ hend
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf v1 (by decide), h1]) (by rw [hf iG (by decide), hg])
      (by rw [hf vZ (by decide), hz]) (by rw [hf iX (by decide), hx]) (by rw [hf vZ (by decide), hz])
      (by rw [hf iX (by decide), hx]) (hW _ (by simp)))
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf v1 (by decide), h1]) (by rw [hf iG (by decide), hg])
      (by rw [hf vZ (by decide), hz]) (by rw [hf iY (by decide), hy]) (by rw [hf vZ (by decide), hz])
      (by rw [hf iY (by decide), hy]) (hW _ (by simp)))
    (fun b hb hf => clauseP_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) b
      (by rw [hf vZ (by decide), hz]) hb _ _ _ _ _ _ (by rw [hf vZ (by decide), hz]) (by rw [hf iG (by decide), hg])
      (by rw [hf v1 (by decide), h1]) (by rw [hf iX (by decide), hx]) (by rw [hf v1 (by decide), h1])
      (by rw [hf iY (by decide), hy]) (hW _ (by simp)))

end NearCubicGates.Adapters.Compile
