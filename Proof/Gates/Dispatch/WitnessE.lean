import Proof.Gates.Dispatch.WitnessD

/-!
# Fragment (W), part E: one coefficient segment in the stage/role walk; the segment layout of the witness
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {C : Ctx}

/-- The loop variables of `allW`. -/
def loopV (s r R J : ℕ) (b : DS VV) : Prop := b.env xS = s ∧ b.env xRo = r ∧ b.env xNR = R ∧ b.env pJ = J

/-- **One segment of `allW`** from `roleW_spec`: the role list of `r` at `vCO1`/`vCO2`. -/
theorem seg_of_role (pre act : St VV) (preT actT : List (Fin VV))
    (hpreT : ∀ y ∈ preT, y ∉ [xS, xRo, xNR, pJ, xM]) (hactT : ∀ y ∈ actT, y ∉ [xS, xRo, xNR, pJ, xM, xIc])
    (s r R J : ℕ) (cs : List ℤ) (q : ℕ) (rest : List Bool) (A0 A1 : DS VV → Prop) (P : ℕ → DS VV → Prop)
    (hA0fr : ∀ a b, A0 a → Fr a b roleT0 → b.out = a.out → b.wq = a.wq → A0 b)
    (tp : ℕ) (hpre : ∀ a, A0 a → Cst a → a.env t3 = cs.length → a.env xM = cs.length →
      Hs C pre a tp (fun b => P 0 b ∧ b.cp = a.cp ∧ Cst b ∧ Fr a b preT))
    (hPfr : ∀ k a b, P k a → Fr a b coefT → b.out = a.out → b.wq = a.wq → P k b)
    (ta : ℕ) (hact : ∀ k (hk : k < cs.length), ∀ a, P k a → Cst a → a.env xA = (cs[k]).natAbs →
      a.env xW = coefWidth cs[k] → Hs C act a ta (fun b => P (k + 1) b ∧ b.cp = a.cp ∧ Cst b ∧ Fr a b actT))
    (hend : ∀ b, P cs.length b → A1 b)
    (a : DS VV) (hA : A0 a) (hc : Cst a) (hl : loopV s r R J a)
    (hq : a.env (if r = 0 then vCO1 else vCO2) = q) (hcw : C.cw.drop q = listWord Interfaces.intWord cs ++ rest)
    (hW : C.cw.length + 4 ≤ C.Wd) (hL : 2 ^ (C.cw.length + 2) ≤ 2 ^ C.Wd) :
    Hs C (if r = 0 then roleW vCO1 pre act else roleW vCO2 pre act) a (roleCost C.cw.length tp ta)
      (fun b => A1 b ∧ Cst b ∧ loopV s r R J b) := by
  have hco : (if r = 0 then vCO1 else vCO2) = vCO1 ∨ (if r = 0 then vCO1 else vCO2) = vCO2 := by
    split_ifs <;> simp
  have hprog : (if r = 0 then roleW vCO1 pre act else roleW vCO2 pre act) =
      roleW (if r = 0 then vCO1 else vCO2) pre act := by split_ifs <;> rfl
  rw [hprog]
  have hlfr : ∀ (T : List (Fin VV)) (b d : DS VV), (∀ y ∈ T, y ∉ [xS, xRo, xNR, pJ]) → loopV s r R J b →
      Fr b d T → loopV s r R J d := by
    intro T b d hT ⟨l1, l2, l3, l4⟩ hf
    have h : ∀ y, y ∈ [xS, xRo, xNR, pJ] → d.env y = b.env y := fun y hy => hf y (fun hm => hT y hm hy)
    exact ⟨by rw [h xS (by simp), l1], by rw [h xRo (by simp), l2], by rw [h xNR (by simp), l3],
      by rw [h pJ (by simp), l4]⟩
  refine Hs.mono (roleW_spec _ hco pre act cs q rest (fun b => A0 b ∧ loopV s r R J b)
    (fun k b => P k b ∧ loopV s r R J b)
    (fun b d ⟨h1, h2⟩ hf ho hw => ⟨hA0fr b d h1 hf ho hw, hlfr roleT0 b d (by decide) h2 hf⟩) tp
    (fun b ⟨h1, h2⟩ hcb ht hm => Hs.mono (hpre b h1 hcb ht hm) le_rfl (fun d ⟨d1, d2, d3, d4⟩ =>
      ⟨⟨d1, hlfr preT b d (fun y hy hm' => hpreT y hy (by simp at hm' ⊢; tauto)) h2 d4⟩, d2, d3,
        by rw [d4 xM (fun hm' => hpreT xM hm' (by simp))]⟩))
    (fun k b d ⟨h1, h2⟩ hf ho hw => ⟨hPfr k b d h1 hf ho hw, hlfr coefT b d (by decide) h2 hf⟩) ta
    (fun k hk b ⟨h1, h2⟩ hcb hA' hW' => Hs.mono (hact k hk b h1 hcb hA' hW') le_rfl (fun d ⟨d1, d2, d3, d4⟩ =>
      ⟨⟨d1, hlfr actT b d (fun y hy hm' => hactT y hy (by simp at hm' ⊢; tauto)) h2 d4⟩, d2, d3,
        by rw [d4 xIc (fun hm' => hactT xIc hm' (by simp))], by rw [d4 xM (fun hm' => hactT xM hm' (by simp))]⟩))
    a ⟨hA, hl⟩ hc hq hcw hW hL) le_rfl ?_
  rintro b ⟨⟨b1, b2⟩, b3⟩
  exact ⟨hend b b1, b3, b2⟩

/-! ## The segment layout -/

theorem segW_length (c : Call) (p : Params) :
    (segmentWidths c p).length = p.J * roleCount c.kind := by
  simp [segmentWidths, List.length_flatMap, List.sum_replicate, Nat.mul_comm]

theorem flatMap_range_getD {α : Type} (J R : ℕ) (f : ℕ → α) (d : α) (s r : ℕ) (hs : s < J) (hr : r < R) :
    ((List.range J).flatMap fun _ => (List.range R).map f).getD (s * R + r) d = f r := by
  induction J generalizing s with
  | zero => omega
  | succ J ih =>
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    by_cases h : s < J
    · rw [List.getElem?_append_left (by simp [List.length_flatMap, List.sum_replicate]; nlinarith)]
      rw [← List.getD_eq_getElem?_getD]; exact ih s h
    · have : s = J := by omega
      subst this
      rw [List.getElem?_append_right (by simp [List.length_flatMap, List.sum_replicate])]
      simp [List.length_flatMap, List.sum_replicate, hr]

theorem segW_get (c : Call) (p : Params) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind) :
    (segmentWidths c p).getD (s * roleCount c.kind + r) [] = (circ c r).coeffs.map coefWidth :=
  flatMap_range_getD p.J (roleCount c.kind) (fun r => (circ c r).coeffs.map coefWidth) [] s r hs hr

theorem take_succ_getD {α : Type} (l : List α) (d : α) (g : ℕ) (hg : g < l.length) :
    l.take (g + 1) = l.take g ++ [l.getD g d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg]
  rfl

/-- `readSegments` one segment further. -/
theorem readSegments_snoc (l : List Bool) (segs : List (List ℕ)) (seg : List ℕ) :
    readSegments l (segs ++ [seg]) = ((readSegments l segs).1 ++ [(readBlock (readSegments l segs).2 seg).1],
      (readBlock (readSegments l segs).2 seg).2) := by
  induction segs generalizing l with
  | nil => simp [readSegments]
  | cons s segs ih => simp [readSegments, ih]

theorem readSegments_fst_take (l : List Bool) (segs : List (List ℕ)) (g : ℕ) :
    ((readSegments l segs).1).take g = (readSegments l (segs.take g)).1 := by
  induction segs generalizing l g with
  | nil => simp [readSegments]
  | cons s segs ih =>
    cases g with
    | zero => simp [readSegments]
    | succ g => simp [readSegments, ih]

theorem readSegments_fst_length (l : List Bool) (segs : List (List ℕ)) :
    (readSegments l segs).1.length = segs.length := by
  induction segs generalizing l with
  | nil => simp [readSegments]
  | cons s segs ih => simp [readSegments, ih]

/-- Field by field inside one segment. -/
theorem readBlock_take_succ (l : List Bool) (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    (readBlock l (ws.take (i + 1))).1 = (readBlock l (ws.take i)).1 ++
      [bitsValue ((l.drop (ws.take i).sum).take ws[i])] := by
  induction ws generalizing l i with
  | nil => simp at hi
  | cons m ws ih =>
    cases i with
    | zero => simp [readBlock_cons, readBlock]
    | succ i =>
      simp only [List.take_succ_cons, readBlock_cons, List.cons_append, List.sum_cons, List.getElem_cons_succ]
      rw [ih (l.drop m) i (by simpa using hi), List.drop_drop]

theorem readBlock_fst_take (l : List Bool) (ws : List ℕ) (i : ℕ) :
    ((readBlock l ws).1).take i = (readBlock l (ws.take i)).1 := by
  induction ws generalizing l i with
  | nil => simp [readBlock]
  | cons m ws ih =>
    cases i with
    | zero => simp [readBlock]
    | succ i => simp [readBlock_cons, ih]

end NearCubicGates.Close.Dispatch
