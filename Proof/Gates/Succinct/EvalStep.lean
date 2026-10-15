import Proof.Gates.Succinct.EvalNode

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- The field reader's registers inside the evaluator's. -/
def fE (E : EReg → Fin nr) : FReg → Fin nr := fun r => E (.f r)

theorem fE_inj (E : EReg → Fin nr) (hE : Function.Injective E) : Function.Injective (fE E) := by
  intro a b h
  have := hE h
  injection this

/-- The current bound: `cb := lp` for an input gate (tag `1`), else `lb`. -/
def cbW (E : EReg → Fin nr) : WM ns nr :=
  .seq (addTo (E .tg) (E .t2) (E .z)) (.ifr (E .t2) (.seq (.dec (E .t2)) (.ifr (E .t2)
    (.seq (WM.clear (E .t2)) (addTo (E .lb) (E .cb) (E .z))) (addTo (E .lp) (E .cb) (E .z))))
    (addTo (E .lb) (E .cb) (E .z)))

theorem cbW_spec (cap : ℕ) (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr)
    (ht2 : σ.val (E .t2) = 0) (hz : σ.val (E .z) = 0) (hcb : σ.val (E .cb) = 0)
    (hcap : σ.val (E .tg) + σ.val (E .lb) + σ.val (E .lp) + 2 ≤ cap) :
    WExec cap (cbW E) σ (σ.setv (E .cb) (if σ.val (E .tg) = 1 then σ.val (E .lp) else σ.val (E .lb)))
      (21 * (σ.val (E .tg) + σ.val (E .lb) + σ.val (E .lp)) + 30) := by
  have e1 := addTo_spec cap (E .tg) (E .t2) (E .z) (hE.ne (by decide)) (hE.ne (by decide)) (hE.ne (by decide)) σ hz
    (by omega) (by omega)
  set t := σ.val (E .tg) with ht
  set σ1 := σ.setv (E .t2) (σ.val (E .t2) + t) with hσ1
  have h1t2 : σ1.val (E .t2) = t := by simp [σ1, ht2]
  have h1z : σ1.val (E .z) = 0 := by simp [σ1, Function.update_apply, hE.eq_iff, hz]
  have h1cb : σ1.val (E .cb) = 0 := by simp [σ1, Function.update_apply, hE.eq_iff, hcb]
  have h1lb : σ1.val (E .lb) = σ.val (E .lb) := by simp [σ1, Function.update_apply, hE.eq_iff]
  have h1lp : σ1.val (E .lp) = σ.val (E .lp) := by simp [σ1, Function.update_apply, hE.eq_iff]
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · rcases Nat.lt_or_ge t 1 with h0 | h0
    · -- tag 0
      have ea := addTo_spec cap (E .lb) (E .cb) (E .z) (hE.ne (by decide)) (hE.ne (by decide)) (hE.ne (by decide))
        σ1 h1z (by omega) (by omega)
      refine WExec.cast cap (WExec.seq e1 (WExec.ifrF (by omega) ea)) ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ1, WState.setv_val, Function.update_apply]
      by_cases hr : r = E .cb
      · subst hr; simp [hE.eq_iff, hcb, show ¬ t = 1 by omega]
      · by_cases hr2 : r = E .t2
        · subst hr2; simp [hE.eq_iff, ht2]; omega
        · simp [hr, hr2]
    · -- tag 1
      have ed := WExec.dec (cap := cap) (E .t2) σ1 (by omega)
      set σ2 := σ1.setv (E .t2) (σ1.val (E .t2) - 1) with hσ2
      have ea := addTo_spec cap (E .lp) (E .cb) (E .z) (hE.ne (by decide)) (hE.ne (by decide)) (hE.ne (by decide))
        σ2 (by simp [σ2, Function.update_apply, hE.eq_iff, h1z]) (by simp [σ2, Function.update_apply, hE.eq_iff]; omega)
        (by simp [σ2, Function.update_apply, hE.eq_iff, h1cb]; omega)
      refine WExec.cast cap (WExec.seq e1 (WExec.ifrT (by omega) (WExec.seq ed (WExec.ifrF
        (by simp [σ2, h1t2]; omega) ea)))) ?_ (by simp [σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases hr : r = E .cb
      · subst hr; simp [hE.eq_iff, hcb, show t = 1 by omega]
      · by_cases hr2 : r = E .t2
        · subst hr2; simp [hE.eq_iff, ht2]; omega
        · simp [hr, hr2]
  · -- tag ≥ 2
    have ed := WExec.dec (cap := cap) (E .t2) σ1 (by omega)
    set σ2 := σ1.setv (E .t2) (σ1.val (E .t2) - 1) with hσ2
    have ec := wclear_spec cap (E .t2) (t - 1) σ2 (by simp [σ2, h1t2]) (by simp [σ2, h1t2]; omega)
    have ea := addTo_spec cap (E .lb) (E .cb) (E .z) (hE.ne (by decide)) (hE.ne (by decide)) (hE.ne (by decide))
      (σ2.setv (E .t2) 0) (by simp [σ2, Function.update_apply, hE.eq_iff, h1z])
      (by simp [σ2, Function.update_apply, hE.eq_iff]; omega)
      (by simp [σ2, Function.update_apply, hE.eq_iff, h1cb]; omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.ifrT (by omega) (WExec.seq ed (WExec.ifrT
      (by simp [σ2, h1t2]; omega) (WExec.seq ec ea))))) ?_
      (by simp [σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
    refine WState.eq rfl rfl ?_ rfl
    funext r; simp only [σ2, σ1, WState.setv_val, Function.update_apply]
    by_cases hr : r = E .cb
    · subst hr; simp [hE.eq_iff, hcb, show ¬ t = 1 by omega]
    · by_cases hr2 : r = E .t2
      · subst hr2; simp [hE.eq_iff, ht2]
      · simp [hr, hr2]

/-- **One node** (paper lem:succinct-verifier, stage (3)). -/
def nodeW (D P V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (fieldTo D (fE E) (E .lb) (E .tg))
  (.seq (cbW E)
  (.seq (fieldToG D (fE E) (E .cb) (E .a) (E .g1))
  (.seq (WM.clear (E .cb))
  (.seq (fieldTo D (fE E) (E .lb) (E .b))
  (.seq (valueW P V E)
  (.seq (writeAt V (E .j) (E .z) (E .y) (E .t2) (E .rv))
  (.seq (WM.clear (E .rv)) (.inc (E .j)))))))))

/-- The evaluator's scratch registers (zero between nodes). -/
def scratchE : List EReg :=
  [.f .flag, .f .cnt, .f .val, .f .pw, .f .tmp, .f .gc, .f .hc, .f .zg, .cb, .tg, .a, .b, .g1, .rv, .y, .z, .t2, .b1, .b2]

/-- A uniform bound on one node's cost. -/
def nodeCost (dl lb lp J : ℕ) : ℕ := 4 * fieldCost dl (lb + lp) + 100 * 2 ^ (lb + lp) + 40 * J + 40 * (lb + lp) + 400

theorem fieldCost_mono {L L' b b' : ℕ} (hL : L ≤ L') (hb : b ≤ b') : fieldCost L b ≤ fieldCost L' b' := by
  unfold fieldCost
  have : 2 ^ b ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hb
  apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

theorem fE_ne (E : EReg → Fin nr) (hE : Function.Injective E) (k : FReg) (r : EReg) (h : ∀ k', r ≠ .f k') :
    fE E k ≠ E r := fun e => h k (hE e).symm

theorem bool_toNat_ne (b : Bool) : decide (b.toNat ≠ 0) = b := by cases b <;> rfl

/-- **One node step** (paper lem:succinct-verifier, stage (3)), on every description stream: the model's `nodeStep`. -/
theorem nodeW_spec (cap : ℕ) (D P V : Fin (ns + 1)) (hDP : D ≠ P) (hDV : D ≠ V)
    (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (m : ℕ) (vals : List Bool)
    (d : List Bool) (pos lb lp : ℕ) (hd : σ.st D = d) (hpos : σ.sh D = pos) (hlb : σ.val (E .lb) = lb)
    (hlp : σ.val (E .lp) = lp)
    (hz : ∀ r ∈ scratchE, σ.val (E r) = 0) (hcd : σ.val (E (.f .cd)) = pos)
    (hj : σ.val (E .j) = vals.length) (hV : σ.st V = vtape m vals) (hVh : σ.sh V = 0) (hPh : σ.sh P = 0)
    (hcap : pos + 4 * d.length + 4 * (lb + lp) + 4 * 2 ^ (lb + lp + 1) + vals.length + 40 ≤ cap) :
    ∃ τ, WExec cap (nodeW D P V E) σ τ (nodeCost d.length lb lp vals.length) ∧
      τ.sh D = (nodeStep d lb lp (readTapeBit (σ.st P)) ⟨pos, vals⟩).pos ∧
      τ.st V = vtape m (nodeStep d lb lp (readTapeBit (σ.st P)) ⟨pos, vals⟩).vals ∧
      τ.val (E .j) = vals.length + 1 ∧ τ.val (E (.f .cd)) = τ.sh D ∧ τ.st D = d ∧ τ.sh V = 0 ∧
      SameExcept σ τ [D, V] [E (.f .cd), E .j] := by
  have hR := fE_inj E hE
  have hcd' : σ.val (fE E .cd) = pos := hcd
  have z : ∀ k : FReg, k ≠ .cd → σ.val (fE E k) = 0 := by
    intro k hk; cases k <;> first | exact absurd rfl hk | exact hz _ (by simp [scratchE])
  have zz : ∀ r : EReg, r ∈ scratchE → σ.val (E r) = 0 := hz
  have fne : ∀ (k : FReg) (r : EReg), (∀ k', r ≠ .f k') → fE E k ≠ E r := fun k r h => fE_ne E hE k r h
  have hpow : 2 ^ (lb + 1) ≤ 2 ^ (lb + lp + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowlb : 2 ^ lb ≤ 2 ^ (lb + lp) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowS : 2 ^ (lb + lp + 1) = 2 * 2 ^ (lb + lp) := by rw [pow_succ]; ring
  have hdl0 := ones_le d pos
  have hp1le := fieldEnd_le d pos
  -- 1. the tag
  have e1 := fieldTo_spec cap D (fE E) hR (E .lb) (E .tg) (fun k => fne k _ (by intro k'; simp))
    (fun k => fne k _ (by intro k'; simp)) σ z (zz .tg (by simp [scratchE]))
    (by rw [hcd', hd, hpos, hlb]; omega)
  rw [hcd', hd, hpos, hlb] at e1
  generalize hσ1 : ((σ.seth D (fieldEnd d pos)).setv (fE E .cd) (pos + 2 * ones d pos + 1)).setv (E .tg)
    (fieldVal d pos lb) = σ1 at e1
  have s1 : ∀ r, r ≠ E (.f .cd) → r ≠ E .tg → σ1.val r = σ.val r := by
    intro r h1 h2; rw [← hσ1]; simp only [WState.setv_val, WState.seth_val, Function.update_apply, fE, if_neg h1,
      if_neg h2]
  have htlt : fieldVal d pos lb < 2 ^ lb := fieldVal_lt _ _ _
  have h1tg : σ1.val (E .tg) = fieldVal d pos lb := by rw [← hσ1]; simp
  have h1st : σ1.st D = d := by rw [← hσ1]; simpa using hd
  have h1sh : σ1.sh D = fieldEnd d pos := by rw [← hσ1]; simp
  have h1cd : σ1.val (fE E .cd) = fieldEnd d pos := by
    rw [← hσ1]; simp [fE, Function.update_apply, hE.eq_iff, fieldEnd]
  -- 2. the current bound
  have e2 := cbW_spec cap E hE σ1 (by rw [s1 _ (hE.ne (by simp)) (hE.ne (by simp))]; exact zz _ (by simp [scratchE]))
    (by rw [s1 _ (hE.ne (by simp)) (hE.ne (by simp))]; exact zz _ (by simp [scratchE]))
    (by rw [s1 _ (hE.ne (by simp)) (hE.ne (by simp))]; exact zz _ (by simp [scratchE]))
    (by rw [s1 (E .lb) (hE.ne (by simp)) (hE.ne (by simp)), s1 (E .lp) (hE.ne (by simp)) (hE.ne (by simp)), h1tg,
          hlb, hlp]
        omega)
  rw [h1tg, s1 (E .lb) (hE.ne (by simp)) (hE.ne (by simp)), s1 (E .lp) (hE.ne (by simp)) (hE.ne (by simp)), hlb,
    hlp] at e2
  have hcbv_le : (if fieldVal d pos lb = 1 then lp else lb) ≤ lb + lp := by split_ifs <;> omega
  generalize hcbv : (if fieldVal d pos lb = 1 then lp else lb) = cbv at e2 hcbv_le
  generalize hσ2 : σ1.setv (E .cb) cbv = σ2 at e2
  have s2 : ∀ r, r ≠ E (.f .cd) → r ≠ E .tg → r ≠ E .cb → σ2.val r = σ.val r := by
    intro r h1 h2 h3; rw [← hσ2]; simp only [WState.setv_val, Function.update_apply, if_neg h3]; exact s1 r h1 h2
  have h2st : σ2.st D = d := by rw [← hσ2]; simpa using h1st
  have h2sh : σ2.sh D = fieldEnd d pos := by rw [← hσ2]; simpa using h1sh
  have h2cd : σ2.val (fE E .cd) = fieldEnd d pos := by
    rw [← hσ2]; simp [fE, Function.update_apply, hE.eq_iff]; exact h1cd
  have h2cb : σ2.val (E .cb) = cbv := by rw [← hσ2]; simp
  have h2tg : σ2.val (E .tg) = fieldVal d pos lb := by
    rw [← hσ2]; simp [Function.update_apply, hE.eq_iff]; exact h1tg
  -- 3. the first argument, with the input guard
  have z2 : ∀ k : FReg, k ≠ .cd → σ2.val (fE E k) = 0 := by
    intro k hk; rw [s2 _ (fun h => hk (by have := hE h; injection this)) (fne k _ (by intro k'; simp))
      (fne k _ (by intro k'; simp))]; exact z k hk
  have hdl1 := ones_le d (fieldEnd d pos)
  have hp2le := fieldEnd_le d (fieldEnd d pos)
  have hc1 : 2 ^ (cbv + 1) ≤ 2 ^ (lb + lp + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e3 := fieldToG_spec cap D (fE E) hR (E .cb) (E .a) (E .g1) (fun k => fne k _ (by intro k'; simp))
    (fun k => fne k _ (by intro k'; simp)) (fun k => fne k _ (by intro k'; simp)) (hE.ne (by simp))
    σ2 z2 (by rw [s2 _ (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp))]; exact zz _ (by simp [scratchE]))
    (by rw [s2 _ (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp))]; exact zz _ (by simp [scratchE]))
    (by rw [h2cd, h2st, h2sh, h2cb]; omega)
  rw [h2cd, h2st, h2sh, h2cb] at e3
  have havlt : fieldVal d (fieldEnd d pos) cbv < 2 ^ (lb + lp) :=
    (fieldVal_lt _ _ _).trans_le (Nat.pow_le_pow_right (by norm_num) hcbv_le)
  generalize hσ3 : (((σ2.seth D (fieldEnd d (fieldEnd d pos))).setv (fE E .cd)
    (fieldEnd d pos + 2 * ones d (fieldEnd d pos) + 1)).setv (E .a) (fieldVal d (fieldEnd d pos) cbv)).setv (E .g1)
    (if cbv < ones d (fieldEnd d pos) then 1 else 0) = σ3 at e3
  -- 4. clear the bound
  have h3cb : σ3.val (E .cb) = cbv := by rw [← hσ3]; simp [Function.update_apply, hE.eq_iff, fE, h2cb]
  have e4 := wclear_spec cap (E .cb) cbv σ3 h3cb (by rw [h3cb]; omega)
  generalize hσ4 : σ3.setv (E .cb) 0 = σ4 at e4
  have s4 : ∀ r, r ≠ E (.f .cd) → r ≠ E .tg → r ≠ E .a → r ≠ E .g1 → σ4.val r = σ.val r := by
    intro r h1 h2 h3 h4
    rw [← hσ4, ← hσ3]
    by_cases h5 : r = E .cb
    · subst h5; simp; exact (zz _ (by simp [scratchE])).symm
    · simp only [WState.setv_val, WState.seth_val, Function.update_apply, fE, if_neg h1, if_neg h3, if_neg h4,
        if_neg h5]
      exact s2 r h1 h2 h5
  have z4 : ∀ k : FReg, k ≠ .cd → σ4.val (fE E k) = 0 := by
    intro k hk; rw [s4 _ (fun h => hk (by have := hE h; injection this)) (fne k _ (by intro k'; simp))
      (fne k _ (by intro k'; simp)) (fne k _ (by intro k'; simp))]; exact z k hk
  have h4st : σ4.st D = d := by rw [← hσ4, ← hσ3]; simpa using h2st
  have h4sh : σ4.sh D = fieldEnd d (fieldEnd d pos) := by rw [← hσ4, ← hσ3]; simp
  have h4cd : σ4.val (fE E .cd) = fieldEnd d (fieldEnd d pos) := by
    rw [← hσ4, ← hσ3]; simp [fE, Function.update_apply, hE.eq_iff, fieldEnd]
  have h4lb : σ4.val (E .lb) = lb := by
    rw [s4 _ (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)), hlb]
  -- 5. the second argument
  have hdl2 := ones_le d (fieldEnd d (fieldEnd d pos))
  have hp3le := fieldEnd_le d (fieldEnd d (fieldEnd d pos))
  have e5 := fieldTo_spec cap D (fE E) hR (E .lb) (E .b) (fun k => fne k _ (by intro k'; simp))
    (fun k => fne k _ (by intro k'; simp)) σ4 z4
    (by rw [s4 _ (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp))]
        exact zz _ (by simp [scratchE]))
    (by rw [h4cd, h4st, h4sh, h4lb]; omega)
  rw [h4st, h4sh, h4cd, h4lb] at e5
  have hbvlt : fieldVal d (fieldEnd d (fieldEnd d pos)) lb < 2 ^ lb := fieldVal_lt _ _ _
  generalize hσ5 : ((σ4.seth D (fieldEnd d (fieldEnd d (fieldEnd d pos)))).setv (fE E .cd)
    (fieldEnd d (fieldEnd d pos) + 2 * ones d (fieldEnd d (fieldEnd d pos)) + 1)).setv (E .b)
    (fieldVal d (fieldEnd d (fieldEnd d pos)) lb) = σ5 at e5
  have s5 : ∀ r, r ≠ E (.f .cd) → r ≠ E .tg → r ≠ E .a → r ≠ E .g1 → r ≠ E .b → σ5.val r = σ.val r := by
    intro r h1 h2 h3 h4 h5
    rw [← hσ5]; simp only [WState.setv_val, WState.seth_val, Function.update_apply, fE, if_neg h1, if_neg h5]
    exact s4 r h1 h2 h3 h4
  have h5st : ∀ x, σ5.st x = σ.st x := by
    intro x; rw [← hσ5, ← hσ4, ← hσ3, ← hσ2, ← hσ1]; simp
  have h5sh : ∀ x, x ≠ D → σ5.sh x = σ.sh x := by
    intro x hx; rw [← hσ5, ← hσ4, ← hσ3, ← hσ2, ← hσ1]; simp [Function.update_apply, hx]
  have h5shD : σ5.sh D = fieldEnd d (fieldEnd d (fieldEnd d pos)) := by rw [← hσ5]; simp
  have h5cd : σ5.val (E (.f .cd)) = fieldEnd d (fieldEnd d (fieldEnd d pos)) := by
    rw [← hσ5]; simp [fE, Function.update_apply, hE.eq_iff, fieldEnd]
  have h5cell : σ5.cell = σ.cell := by rw [← hσ5, ← hσ4, ← hσ3, ← hσ2, ← hσ1]; simp
  -- 6. the gate value
  have h5tg : σ5.val (E .tg) = fieldVal d pos lb := by
    rw [← hσ5, ← hσ4, ← hσ3]; simp [Function.update_apply, hE.eq_iff, fE]; exact h2tg
  have h5a : σ5.val (E .a) = fieldVal d (fieldEnd d pos) cbv := by
    rw [← hσ5, ← hσ4, ← hσ3]; simp [Function.update_apply, hE.eq_iff, fE]
  have h5b : σ5.val (E .b) = fieldVal d (fieldEnd d (fieldEnd d pos)) lb := by rw [← hσ5]; simp
  have h5g : σ5.val (E .g1) = if cbv < ones d (fieldEnd d pos) then 1 else 0 := by
    rw [← hσ5, ← hσ4, ← hσ3]; simp [Function.update_apply, hE.eq_iff, fE]
  have hgf1 : (if cbv < ones d (fieldEnd d pos) then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have zs : ∀ r, r ∈ [EReg.rv, .y, .b1, .b2, .z, .t2] → σ5.val (E r) = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [s5 _ (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp))];
       exact zz _ (by simp [scratchE]))
  obtain ⟨τ6, e6, h6rv, h6tg, h6a, h6b, h6g, hse6⟩ := valueW_spec cap P V E hE σ5 _ h5g
    (zs .rv (by simp)) (zs .y (by simp)) (zs .b1 (by simp)) (zs .b2 (by simp))
    (by rw [h5sh P (Ne.symm hDP)]; exact hPh) (by rw [h5sh V (Ne.symm hDV)]; exact hVh)
    (by rw [h5tg, h5a, h5b]; omega)
  rw [h5tg, h5a, h5b, h5st P, h5st V] at h6rv
  rw [h5tg, h5a, h5b] at e6
  generalize hval : valueOf (fieldVal d pos lb) (fieldVal d (fieldEnd d pos) cbv)
    (fieldVal d (fieldEnd d (fieldEnd d pos)) lb) (if cbv < ones d (fieldEnd d pos) then 1 else 0)
    (readTapeBit (σ.st P)) (readTapeBit (σ.st V)) = val at h6rv
  have n6 : ∀ r, r ∉ [E .rv, E .tg, E .a, E .b, E .g1] → τ6.val r = σ5.val r := fun r hr => hse6.val hr
  have h6V : τ6.st V = σ.st V := by rw [hse6.st (by simp), h5st]
  have h6Vh : τ6.sh V = 0 := by rw [hse6.sh (by simp), h5sh V (Ne.symm hDV), hVh]
  have h6D : τ6.st D = d := by rw [hse6.st (by simp), h5st, hd]
  have h6Dh : τ6.sh D = fieldEnd d (fieldEnd d (fieldEnd d pos)) := by rw [hse6.sh (by simp), h5shD]
  have h6cd : τ6.val (E (.f .cd)) = fieldEnd d (fieldEnd d (fieldEnd d pos)) := by
    rw [n6 _ (by simp [hE.eq_iff]), h5cd]
  have h6j : τ6.val (E .j) = vals.length := by
    rw [n6 _ (by simp [hE.eq_iff]), s5 _ (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp))
      (hE.ne (by simp)), hj]
  have h6z : ∀ r, r ∈ [EReg.z, .y, .t2] → τ6.val (E r) = 0 := by
    intro r hr
    have hr' : E r ∉ [E .rv, E .tg, E .a, E .b, E .g1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [hE.eq_iff]
    rw [n6 _ hr']; exact zs r (by simp at hr ⊢; tauto)
  -- 7. write the value
  have e7 := writeAt_spec cap V (E .j) (E .z) (E .y) (E .t2) (E .rv)
    (by simp [List.nodup_cons, hE.eq_iff]) τ6 (h6z .z (by simp)) (h6z .y (by simp)) (h6z .t2 (by simp))
    (by rw [h6j]; omega)
  rw [h6V, h6Vh, h6j, h6rv, Nat.zero_add, bool_toNat_ne, hV, vtape_write] at e7
  -- 8. clear the value, next index
  have e8 := wclear_spec cap (E .rv) val.toNat (τ6.sets V (vtape m (vals ++ [val]))) (by simp [h6rv])
    (by simp; have := Bool.toNat_le val; omega)
  have e9 := WExec.inc (cap := cap) (E .j) ((τ6.sets V (vtape m (vals ++ [val]))).setv (E .rv) 0)
    (by simp [Function.update_apply, hE.eq_iff, h6j]; omega)
  -- the model
  have hstep : nodeStep d lb lp (readTapeBit (σ.st P)) ⟨pos, vals⟩ =
      ⟨fieldEnd d (fieldEnd d (fieldEnd d pos)), vals ++ [val]⟩ := by
    unfold nodeStep
    simp only [EvSt.mk.injEq, true_and]
    rw [← hval]
    unfold nodeValue valueOf
    simp only []
    have hrd : readTapeBit (σ.st V) = fun x => vals.getD x false := by
      funext x; rw [hV, read_vtape]
    rw [hrd, ← hcbv]
    by_cases h1 : fieldVal d pos lb = 1
    · simp only [h1, if_true, one_ne_zero, if_false]
      by_cases hl : lp < ones d (fieldEnd d pos)
      · simp [hl, show ¬ ones d (fieldEnd d pos) ≤ lp by omega]
      · simp [hl, show ones d (fieldEnd d pos) ≤ lp by omega]
    · simp only [h1, if_false]
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have c0 : fieldCost (ones d pos) lb ≤ fieldCost d.length (lb + lp) := fieldCost_mono hdl0 (by omega)
    have c1 : fieldCost (ones d (fieldEnd d pos)) cbv ≤ fieldCost d.length (lb + lp) := fieldCost_mono hdl1 hcbv_le
    have c2 : fieldCost (ones d (fieldEnd d (fieldEnd d pos))) lb ≤ fieldCost d.length (lb + lp) :=
      fieldCost_mono hdl2 (by omega)
    have hc2 : 2 ^ cbv ≤ 2 ^ (lb + lp) := Nat.pow_le_pow_right (by norm_num) hcbv_le
    have := Bool.toNat_le val
    unfold nodeCost
    omega
  · simp [h6Dh, hstep]
  · rw [hstep]; simp
  · simp [Function.update_apply, hE.eq_iff, h6j]
  · simp [Function.update_apply, hE.eq_iff, h6cd, h6Dh]
  · simp [Function.update_apply, hDV, h6D]
  · simp [h6Vh]
  · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [WState.setv_st, WState.setv_sh, WState.sets_st, WState.sets_sh, Function.update_apply, hx.2,
        if_false]
      exact ⟨by rw [hse6.st (by simp), h5st], by rw [hse6.sh (by simp), h5sh x hx.1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [WState.setv_val, WState.sets_val, Function.update_apply, hr.2, if_false]
      by_cases hrv : r = E .rv
      · rw [if_pos hrv, hrv]; exact (zz _ (by simp [scratchE])).symm
      · rw [if_neg hrv]
        by_cases hin : r ∈ [E .rv, E .tg, E .a, E .b, E .g1]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
          rcases hin with h | h | h | h | h
          · exact absurd h hrv
          · rw [h, h6tg]; exact (zz _ (by simp [scratchE])).symm
          · rw [h, h6a]; exact (zz _ (by simp [scratchE])).symm
          · rw [h, h6b]; exact (zz _ (by simp [scratchE])).symm
          · rw [h, h6g]; exact (zz _ (by simp [scratchE])).symm
        · rw [n6 r hin]
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hin
          exact s5 r hr.1 hin.2.1 hin.2.2.1 hin.2.2.2.2 hin.2.2.2.1
    · simp [hse6.cell, h5cell]

end NearCubicGates.Close.Succinct
