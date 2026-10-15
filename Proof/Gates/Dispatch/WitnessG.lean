import Proof.Gates.Dispatch.WitnessF

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

/-- The packed coefficient window. -/
def L0 (c : Call) (p : Params) (w : List Bool) : List Bool := (w.drop (p.k * Target.lambda c.n)).take (LCof c p)

/-- The window after the first `g` segments. -/
def rsG (c : Call) (p : Params) (w : List Bool) (g : ℕ) : List (List ℕ) × List Bool :=
  readSegments (L0 c p w) ((segmentWidths c p).take g)

/-- The widths of role `r`. -/
def wsR (c : Call) (r : ℕ) : List ℕ := (circ c r).coeffs.map coefWidth

/-- Field `i` of segment `g` (role `g % R`). -/
def fieldV (c : Call) (p : Params) (w : List Bool) (g i : ℕ) : ℕ :=
  bitsValue ((((rsG c p w g).2).drop (((wsR c (g % roleCount c.kind)).take i).sum)).take
    ((wsR c (g % roleCount c.kind)).getD i 0))

/-- Segment `g` passes the range test. -/
def segOK (c : Call) (p : Params) (w : List Bool) (g : ℕ) : Prop :=
  ∀ i < (circ c (g % roleCount c.kind)).coeffs.length,
    fieldV c p w g i ≤ 2 * ((circ c (g % roleCount c.kind)).coeffs.getD i 0).natAbs

instance (c : Call) (p : Params) (w : List Bool) (g : ℕ) : Decidable (segOK c p w g) := by
  unfold segOK; infer_instance

theorem elem_len_le_flatMap {α : Type} (xs : List α) (g : α → List Bool) {x : α} (hx : x ∈ xs) :
    (g x).length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h; omega

theorem rsG_succ_snd (c : Call) (p : Params) (w : List Bool) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind) :
    (rsG c p w (s * roleCount c.kind + r + 1)).2 =
      ((rsG c p w (s * roleCount c.kind + r)).2).drop (wsR c r).sum := by
  unfold rsG
  have hg : s * roleCount c.kind + r < (segmentWidths c p).length := by rw [segW_length]; nlinarith
  rw [take_succ_getD _ [] _ hg, readSegments_snoc, segW_get c p s r hs hr, readBlock_snd]; rfl

theorem mod_role (c : Call) (s r : ℕ) (hr : r < roleCount c.kind) : (s * roleCount c.kind + r) % roleCount c.kind = r := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

def chkAct : St VV :=
  .seq extractW (.seq (.op (.copy xT3 xA)) (.seq (.op (.add xT3 xA)) (.ite (.lt xT3 xV) (.op (.zero vWF)) skipS)))

def chkActT : List (Fin VV) := [xV, xP, xC, xQ, xR, xRem, vJ, xT3, vWF]

def chkWT : List (Fin VV) := [vJ, vPOS, t0, t1, t2, t3, t4, t8, xS, xRo, xM, xIc, xA, xT2, xW, xP, xV, xC, xQ, xR,
  xRem, xT3, vWF]

theorem chkW_spec (c : Call) (p : Params) (G0 : Prop) [Decidable G0] (a0 : DS VV) (hc : Cst a0)
    (hcwc : C.cw = callWord c)
    (hco1 : a0.env vCO1 = coPos c 0) (hco2 : a0.env vCO2 = coPos c 1) (hNR : a0.env xNR = roleCount c.kind)
    (hJ : a0.env pJ = p.J) (hRem : a0.env xRem = bitsValue (L0 c p C.wit)) (hWF : a0.env vWF = bnat G0)
    (hW : C.cw.length + 4 ≤ C.Wd) (hL : 2 ^ (C.cw.length + 2) ≤ 2 ^ C.Wd) (hJW : p.J + 1 < 2 ^ C.Wd) :
    Hs C (allW skipS chkAct) a0 (p.J * (roleCount c.kind * (roleCost C.cw.length 1 (14 * C.cw.length + 50) + 5) + 8) + 4)
      (fun b => b.env vWF = bnat (G0 ∧ ∀ g < p.J * roleCount c.kind, segOK c p C.wit g) ∧ b.wq = a0.wq ∧
        b.out = a0.out ∧ Cst b ∧ Fr a0 b chkWT) := by
  set R := roleCount c.kind with hRd
  have hR2 : R ≤ 2 := by rw [hRd]; cases c.kind <;> simp [roleCount]
  have hR0 : 0 < R := roleCount_pos c.kind
  have h4 : 4 ≤ 2 ^ (C.cw.length + 2) := by
    rw [pow_add]; have := Nat.one_le_two_pow (n := C.cw.length); omega
  let A : ℕ → DS VV → Prop := fun g b => Fr a0 b chkWT ∧ b.env xRem = bitsValue (rsG c p C.wit g).2 ∧
    b.env vWF = bnat (G0 ∧ ∀ g' < g, segOK c p C.wit g') ∧ b.wq = a0.wq ∧ b.out = a0.out
  refine Hs.mono (allW_spec skipS chkAct R p.J A (roleCost C.cw.length 1 (14 * C.cw.length + 50)) ?_ ?_ a0
    ⟨Fr.refl _ _, by rw [hRem]; rfl, by rw [hWF]; unfold bnat; congr 1; simp, rfl, rfl⟩ hc hNR hJ (by omega) hJW)
    le_rfl ?_
  · intro g b v ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨Fr.trans h1 (Fr.set b _ (by decide)), by vsimp [h2], by vsimp [h3], h4, h5⟩,
      ⟨Fr.trans h1 (Fr.set b _ (by decide)), by vsimp [h2], by vsimp [h3], h4, h5⟩⟩
  · intro s hs r hr b hA hcb hS hRo hNRb hJb
    obtain ⟨rest, hrest⟩ := coeffs_at c r
    set cs := (circ c r).coeffs with hcs
    set g := s * R + r with hg
    have hgr : g % R = r := mod_role c s r hr
    have hgr' : g % roleCount c.kind = r := hgr
    have hco : b.env (if r = 0 then vCO1 else vCO2) = coPos c r := by
      have h1 : b.env vCO1 = coPos c 0 := by rw [hA.1 vCO1 (by decide), hco1]
      have h2 : b.env vCO2 = coPos c 1 := by rw [hA.1 vCO2 (by decide), hco2]
      exact co_at c b h1 h2 r
    set lg := (rsG c p C.wit g).2 with hlg
    have hws : wsR c (g % R) = cs.map coefWidth := by rw [hgr]; rfl
    let fOK : ℕ → Prop := fun i => fieldV c p C.wit g i ≤ 2 * (cs.getD i 0).natAbs
    have hfv : ∀ i (hi : i < cs.length), fieldV c p C.wit g i =
        bitsValue ((lg.drop (((cs.map coefWidth).take i).sum)).take (coefWidth cs[i])) := by
      intro i hi; unfold fieldV; rw [hws]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.getD_some]
      rfl
    let P : ℕ → DS VV → Prop := fun k e => Fr a0 e chkWT ∧
      e.env xRem = bitsValue (lg.drop (((cs.map coefWidth).take k).sum)) ∧
      e.env vWF = bnat (G0 ∧ (∀ g' < g, segOK c p C.wit g') ∧ ∀ i < k, fOK i) ∧ e.wq = a0.wq ∧ e.out = a0.out
    refine Hs.mono (seg_of_role skipS chkAct [vJ] chkActT (by decide) (by decide) s r R p.J cs (coPos c r) rest
      (A g) (A (g + 1)) P ?_ 1 ?_ ?_ (14 * C.cw.length + 50) ?_ ?_ b hA hcb ⟨hS, hRo, hNRb, hJb⟩ hco
      (by rw [hcwc]; exact hrest) hW hL) le_rfl (fun e h => h)
    · intro d e ⟨h1, h2, h3, h4, h5⟩ hf ho hw
      exact ⟨Fr.trans h1 (Fr.weaken hf (by decide)), by rw [hf xRem (by decide), h2], by rw [hf vWF (by decide), h3],
        by rw [hw, h4], by rw [ho, h5]⟩
    · intro d ⟨h1, h2, h3, h4, h5⟩ hcd _ _
      refine Hs.mono (skip_spec d) le_rfl ?_
      rintro e rfl
      refine ⟨⟨Fr.trans h1 (Fr.set d _ (by decide)), by vsimp [h2]; rfl, ?_, h4, h5⟩, rfl,
        Cst.of_fr hcd (Fr.set d _ (show vJ ∈ [vJ] by decide)) (by decide) (by vsimp [hcd.pos]),
        Fr.set d _ (by decide)⟩
      vsimp [h3]
    · intro k d e ⟨h1, h2, h3, h4, h5⟩ hf ho hw
      exact ⟨Fr.trans h1 (Fr.weaken hf (by decide)), by rw [hf xRem (by decide), h2], by rw [hf vWF (by decide), h3],
        by rw [hw, h4], by rw [ho, h5]⟩
    · intro k hk d ⟨h1, h2, h3, h4, h5⟩ hcd hA' hW'
      have hlw : (Interfaces.intWord cs[k]).length ≤ C.cw.length := by
        have e1 := len_le_of_drop (by rw [hcwc]; exact hrest : C.cw.drop (coPos c r) = listWord Interfaces.intWord cs ++ rest)
        have e2 := elem_len_le_flatMap cs Interfaces.intWord (List.getElem_mem hk)
        simp only [listWord, List.length_append] at e1; omega
      have hcwk : coefWidth cs[k] ≤ C.cw.length := (coefWidth_le_int cs[k]).trans hlw
      have hAk : cs[k].natAbs < 2 ^ C.cw.length :=
        lt_of_lt_of_le (natAbs_lt_pow cs[k]) (Nat.pow_le_pow_right (by norm_num) hlw)
      have hkw : ((cs.map coefWidth).take (k + 1)).sum = ((cs.map coefWidth).take k).sum + coefWidth cs[k] := by
        rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hk]; simp
      refine Hs.mono (Hs.seq (t2 := 6) (extractW_spec d hcd _ (coefWidth cs[k]) h2 hW' (by omega))
        (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_)) (show 12 * coefWidth cs[k] + 10 + 6 + 1 ≤
          14 * C.cw.length + 50 by omega) (fun _ h => h)
      refine Hs.seq (t2 := 4) (hs_copy C xT3 xA e (by decide)) (fun f hf => ?_)
      subst hf
      have fA : (e.set xT3 (e.env xA)).env xA = cs[k].natAbs := by vsimp [e7 xA (by decide), hA']
      refine Hs.seq (t2 := 2) (hs_add C xT3 xA _ (by decide) (by
        vsimp [e7 xA (by decide), hA']
        have : 2 ^ C.cw.length * 4 ≤ 2 ^ C.Wd := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)) (fun f hf => ?_)
      subst hf
      set fst := (e.set xT3 (e.env xA)).set xT3 ((e.set xT3 (e.env xA)).env xT3 + (e.set xT3 (e.env xA)).env xA)
        with hfst
      have f3 : fst.env xT3 = 2 * cs[k].natAbs := by vsimp [hfst, e7 xA (by decide), hA']; ring
      have fV : fst.env xV = bitsValue (((lg.drop (((cs.map coefWidth).take k).sum)).take (coefWidth cs[k]))) := by
        vsimp [hfst, e1]
      have fR : fst.env xRem = bitsValue (lg.drop (((cs.map coefWidth).take (k + 1)).sum)) := by
        vsimp [hfst, e2, hkw, List.drop_drop]
      have fWF : fst.env vWF = bnat (G0 ∧ (∀ g' < g, segOK c p C.wit g') ∧ ∀ i < k, fOK i) := by
        vsimp [hfst, e7 vWF (by decide), h3]
      have fFr : Fr a0 fst chkWT := Fr.trans h1 (Fr.trans (Fr.weaken e7 (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
      have fc : Cst fst := Cst.of_fr hcd (Fr.trans (Fr.weaken e7 (by decide : ∀ y ∈ extractT, y ∈ chkActT))
        (Fr.trans (Fr.set _ _ (show xT3 ∈ chkActT by decide)) (Fr.set _ _ (show xT3 ∈ chkActT by decide))))
        (by decide) (by vsimp [hfst, e6.pos])
      have hok : fOK k ↔ bitsValue (((lg.drop (((cs.map coefWidth).take k).sum)).take (coefWidth cs[k]))) ≤
          2 * cs[k].natAbs := by
        show fieldV c p C.wit g k ≤ 2 * (cs.getD k 0).natAbs ↔ _
        rw [hfv k hk]; simp [List.getD_eq_getElem?_getD, hk]
      refine Hs.ite (c := .lt xT3 xV) (show xT3 ≠ xV by decide) (fun he => ?_) (fun he => ?_)
      · have hbad : ¬ fOK k := by
          rw [hok]; simp only [Cnd.eval, decide_eq_true_eq] at he; rw [f3, fV] at he; omega
        refine Hs.mono (hs_zero C vWF fst) le_rfl ?_
        rintro f rfl
        refine ⟨⟨Fr.trans fFr (Fr.set _ _ (by decide)), by vsimp [fR], ?_, by simp [hfst, e4, h4], by simp [hfst, e5, h5]⟩, by
          simp [hfst, e3], Cst.of_fr fc (Fr.set _ _ (show vWF ∈ [vWF] by decide)) (by decide) (by vsimp [fc.pos]),
          Fr.trans (Fr.trans (Fr.weaken e7 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
            (Fr.set _ _ (by decide))⟩
        have hno : ¬ (G0 ∧ (∀ g' < g, segOK c p C.wit g') ∧ ∀ i < k + 1, fOK i) :=
          fun ⟨_, _, h⟩ => hbad (h k (by omega))
        show ((fst.set vWF 0).env vWF) = bnat (G0 ∧ (∀ g' < g, segOK c p C.wit g') ∧ ∀ i < k + 1, fOK i)
        rw [DS.set_env_self]; unfold bnat; rw [decide_eq_false hno]; rfl
      · have hgood : fOK k := by
          rw [hok]; simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [f3, fV] at he; omega
        refine Hs.mono (skip_spec fst) (by omega) ?_
        rintro f rfl
        refine ⟨⟨Fr.trans fFr (Fr.set _ _ (by decide)), by vsimp [fR], ?_, by simp [hfst, e4, h4], by simp [hfst, e5, h5]⟩, by
          simp [hfst, e3], Cst.of_fr fc (Fr.set _ _ (show vJ ∈ [vJ] by decide)) (by decide) (by vsimp [fc.pos]),
          Fr.trans (Fr.trans (Fr.weaken e7 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
            (Fr.set _ _ (by decide))⟩
        vsimp [fWF]; unfold bnat; congr 1
        refine decide_eq_decide.mpr ⟨fun ⟨a1, a2, a3⟩ => ⟨a1, a2, fun i hi => ?_⟩, fun ⟨a1, a2, a3⟩ =>
          ⟨a1, a2, fun i hi => a3 i (by omega)⟩⟩
        by_cases h : i < k
        · exact a3 i h
        · have : i = k := by omega
          subst this; exact hgood
    · intro e ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, ?_, ?_, h4, h5⟩
      · rw [h2, List.take_of_length_le (by simp)]
        show bitsValue (lg.drop (cs.map coefWidth).sum) = bitsValue (rsG c p C.wit (g + 1)).2
        rw [rsG_succ_snd c p C.wit s r hs hr]; rfl
      · rw [h3]; unfold bnat; congr 1
        refine decide_eq_decide.mpr ⟨fun ⟨a1, a2, a3⟩ => ⟨a1, fun g' hg' => ?_⟩, fun ⟨a1, a2⟩ =>
          ⟨a1, fun g' hg' => a2 g' (by omega), fun i hi => ?_⟩⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hg' with h | h
          · exact a2 g' h
          · subst h; unfold segOK; rw [hgr']; exact a3
        · have := a2 g (by omega); unfold segOK at this; rw [hgr'] at this; exact this i hi
  · rintro b ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    exact ⟨h3, h4, h5, h6, h1⟩

end NearCubicGates.Close.Dispatch
