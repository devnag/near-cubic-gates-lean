import Proof.Gates.Cells.EncRel

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

variable {V M t : ℕ}

/-- Steps per cost unit. -/
def KC (C : Ctx) : ℕ := 500 * (C.Wd + 1) ^ 2 + 100 * (TS C + 3)

theorem KC_ge (C : Ctx) : 41 * C.Wd + 50 ≤ KC C := by unfold KC; nlinarith
theorem KC_ge2 (C : Ctx) : 400 * (C.Wd + 1) ^ 2 ≤ KC C := by unfold KC; nlinarith
theorem KC_ge3 (C : Ctx) : 100 * (TS C + 3) ≤ KC C := by unfold KC; omega
theorem KC_ge4 (C : Ctx) : 500 * (C.Wd + 1) ^ 2 ≤ KC C := by unfold KC; omega

theorem frame_odd' (u : List Bool) (i : ℕ) : (frame u).getD (2 * i + 1) false = u.getD i false := by
  induction u generalizing i with
  | nil => cases i <;> simp [frame]
  | cons b u ih =>
    cases i with
    | zero => simp [frame]
    | succ i =>
      have := ih i
      simp only [frame, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, List.getD_cons_succ] at this ⊢
      exact this

/-! ## The programs -/

section Progs
variable {t : ℕ}

def cOne (x : Fin V) : WMX (NS M t V) (NR M) := BinW.one (vs x) sZ rF rR
def cZero (x : Fin V) : WMX (NS M t V) (NR M) := BinW.zero (vs x) sZ rF rR

def compB : Op V M → WMX (NS M t V) (NR M)
  | .zero x => cZero x
  | .inc x => BinW.inc (vs x) sZ rF rR
  | .add x y => BinW.add (vs x) (vs y) rF rR
  | .sub x y => BinW.sub (vs x) (vs y) rF rR
  | .copy x y => BinW.copy (vs x) (vs y) rF rR
  | .half x => BinW.half (vs x) rR
  | .shl x => BinW.shl (vs x) sZ rF rR
  | .mul x y z => BinW.mul (vs x) (vs y) (vs z) sZ rF rR rG
  | .dm x y q r => BinW.divmod (vs x) (vs y) (vs q) (vs r) sZ rF rR rK rT
  | .rdI x => .seq (WMX.fwd sIN) (.seq (WMX.inc rIP) (.seq (.ifs sIN (cOne x) (cZero x))
      (.seq (WMX.fwd sIN) (WMX.inc rIP))))
  | .bkI => .seq (WMX.bwd sIN) (.seq (WMX.dec rIP) (.seq (WMX.bwd sIN) (WMX.dec rIP)))
  | .emit b => .seq (WMX.wr sOUT b) (.seq (WMX.fwd sOUT) (WMX.inc rOP))
  | .rdM m x => .wm (copyRec (sM m) (vs x) (rM m) rC1)
  | .wrM m x => .seq (.wm (appendRec (vs x) (sM m) rC1 (rM m))) (.ifs (sM m) WMX.skip (WMX.wr (sM m) false))
  | .rwM m => .wm (WM.rewind (sM m) (rM m))
  | _ => WMX.skip

/-- The arithmetic operations. -/
def Op.IsArith : Op V M → Prop
  | .zero _ | .inc _ | .add _ _ | .sub _ _ | .copy _ _ | .half _ | .shl _ | .mul _ _ _ | .dm _ _ _ _ => True
  | _ => False

/-- The test of a condition into register `F`. -/
def condP : Cnd V → WMX (NS M t V) (NR M)
  | .lt x y => BinW.lt (vs x) (vs y) rF rR
  | .eq x y => BinW.eq (vs x) (vs y) rF rR

end Progs

/-! ## Transport lemmas: the encoding after one kind of update -/

section Transport
variable {C : Ctx} {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

theorem upd_ne {α : Type} {n : ℕ} (f : Fin n → α) {i j : Fin n} (v : α) (h : j ≠ i) :
    Function.update f i v j = f j := Function.update_of_ne h _ _

/-- Unchanged components: unfold the state updates, skip every update at another index, close with `e`. -/
macro "keep " e:term : tactic => `(tactic| (
  simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setv_st, WState.seth_st, WState.sets_st,
    WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_cell, WState.seth_cell, WState.sets_cell]
  repeat (rw [Function.update_of_ne (by lay_ne)])
  exact $e))

/-- The entry cursor moves to `p`. -/
theorem Enc.setIP (h : Enc C a σ) (p : ℕ) :
    Enc C { a with ip := p } ((σ.seth sIN (2 * p)).setv rIP (2 * p)) where
  inS := by keep h.inS
  inH := by simp
  inR := by simp
  outS := by keep h.outS
  outH := by keep h.outH
  outR := by keep h.outR
  zero := ⟨by keep h.zero.1, by keep h.zero.2⟩
  var := fun x => ⟨by keep (h.var x).1, by keep (h.var x).2⟩
  ramS := fun m => by keep h.ramS m
  ramH := fun m => by keep h.ramH m
  ramR := fun m => by keep h.ramR m
  shL := fun m => by keep h.shL m
  shH := fun m => by keep h.shH m
  tpS := by keep h.tpS
  tpH := by keep h.tpH
  kiS := by keep h.kiS
  kiH := by keep h.kiH
  kiR := by keep h.kiR
  koS := by keep h.koS
  koH := by keep h.koH
  koR := by keep h.koR
  scS := fun j => by keep h.scS j
  scH := fun j => by keep h.scH j
  lgS := by keep h.lgS
  lgH := by keep h.lgH
  ruS := by keep h.ruS
  ruH := by keep h.ruH
  zF := by keep h.zF
  zR := by keep h.zR
  zG := by keep h.zG
  zK := by keep h.zK
  zT := by keep h.zT
  zC1 := by keep h.zC1
  zC2 := by keep h.zC2
  cell := by keep h.cell

/-- The output grows by one bit. -/
theorem Enc.setOut (h : Enc C a σ) (b : Bool) :
    Enc C { a with out := a.out ++ [b] }
      (((σ.sets sOUT (a.out ++ [b])).seth sOUT (a.out.length + 1)).setv rOP (a.out.length + 1)) where
  inS := by keep h.inS
  inH := by keep h.inH
  inR := by keep h.inR
  outS := by simp
  outH := by simp
  outR := by simp
  zero := ⟨by keep h.zero.1, by keep h.zero.2⟩
  var := fun x => ⟨by keep (h.var x).1, by keep (h.var x).2⟩
  ramS := fun m => by keep h.ramS m
  ramH := fun m => by keep h.ramH m
  ramR := fun m => by keep h.ramR m
  shL := fun m => by keep h.shL m
  shH := fun m => by keep h.shH m
  tpS := by keep h.tpS
  tpH := by keep h.tpH
  kiS := by keep h.kiS
  kiH := by keep h.kiH
  kiR := by keep h.kiR
  koS := by keep h.koS
  koH := by keep h.koH
  koR := by keep h.koR
  scS := fun j => by keep h.scS j
  scH := fun j => by keep h.scH j
  lgS := by keep h.lgS
  lgH := by keep h.lgH
  ruS := by keep h.ruS
  ruH := by keep h.ruH
  zF := by keep h.zF
  zR := by keep h.zR
  zG := by keep h.zG
  zK := by keep h.zK
  zT := by keep h.zT
  zC1 := by keep h.zC1
  zC2 := by keep h.zC2
  cell := by keep h.cell

/-- Store `m` becomes `l` with its cursor at record `r`. -/
theorem Enc.setRam (h : Enc C a σ) (m : Fin M) (l : List ℕ) (r : ℕ)
    (hl : (σ.st (sS m)).length ≤ (encR C.Wd l).length) :
    Enc C { a with ram := Function.update a.ram m l, rc := Function.update a.rc m r }
      (((σ.sets (sM m) (encR C.Wd l)).seth (sM m) ((2 * C.Wd + 1) * r)).setv (rM m) ((2 * C.Wd + 1) * r)) where
  inS := by keep h.inS
  inH := by keep h.inH
  inR := by keep h.inR
  outS := by keep h.outS
  outH := by keep h.outH
  outR := by keep h.outR
  zero := ⟨by keep h.zero.1, by keep h.zero.2⟩
  var := fun x => ⟨by keep (h.var x).1, by keep (h.var x).2⟩
  ramS := fun m' => by
    by_cases hm : m' = m
    · subst hm; simp
    · simp only [WState.setv_st, WState.seth_st, WState.sets_st]
      rw [Function.update_of_ne (sM_inj hm), Function.update_of_ne hm]; exact h.ramS m'
  ramH := fun m' => by
    by_cases hm : m' = m
    · subst hm; simp
    · simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh]
      rw [Function.update_of_ne (sM_inj hm), Function.update_of_ne hm]; exact h.ramH m'
  ramR := fun m' => by
    by_cases hm : m' = m
    · subst hm; simp
    · simp only [WState.setv_val, WState.seth_val, WState.sets_val]
      rw [Function.update_of_ne (rM_inj hm), Function.update_of_ne hm]; exact h.ramR m'
  shL := fun m' => by
    have := m.isLt; have := m'.isLt
    by_cases hm : m' = m
    · subst hm
      simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
      rw [Function.update_of_ne (by lay_ne)]; exact hl
    · simp only [WState.setv_st, WState.seth_st, WState.sets_st]
      rw [Function.update_of_ne (by lay_ne), Function.update_of_ne (sM_inj hm)]; exact h.shL m'
  shH := fun m' => by have := m.isLt; have := m'.isLt; keep h.shH m'
  tpS := by keep h.tpS
  tpH := by keep h.tpH
  kiS := by keep h.kiS
  kiH := by keep h.kiH
  kiR := by keep h.kiR
  koS := by keep h.koS
  koH := by keep h.koH
  koR := by keep h.koR
  scS := fun j => by keep h.scS j
  scH := fun j => by keep h.scH j
  lgS := by keep h.lgS
  lgH := by keep h.lgH
  ruS := by keep h.ruS
  ruH := by keep h.ruH
  zF := by keep h.zF
  zR := by keep h.zR
  zG := by keep h.zG
  zK := by keep h.zK
  zT := by keep h.zT
  zC1 := by keep h.zC1
  zC2 := by keep h.zC2
  cell := by keep h.cell

end Transport

/-! ## The operations -/

section Ops
variable (C : Ctx) (cap : ℕ) {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

theorem fRne : (rF : Fin (NR M)) ≠ rR := by lay_ne

/-- Arithmetic on variables. -/
theorem arith_ok (he : Enc C a σ) (ha : Valid C a) (hW : 1 ≤ C.Wd) (hcap : 2 * C.Wd + 1 ≤ cap) {o : Op V M}
    {b : DS V M} {k : ℕ} (h : OpEx C o a b k) (hA : o.IsArith) :
    ∃ τ, Enc C b τ ∧ WXExec cap (compB o) σ τ (k * KC C) := by
  have hK := KC_ge C
  have hK2 := KC_ge2 C
  have hFR := fRne (M := M)
  cases h with
  | zero x a =>
    exact ⟨_, he.setVar x 0, WXExec.mono (BinW.zero_spec cap C.Wd (vs_ne_Z x) hFR σ _ 0 (he.var x) he.zero
      he.zF he.zR hcap) (by omega)⟩
  | inc x a hv =>
    exact ⟨_, he.setVar x _, WXExec.mono (BinW.inc_spec cap C.Wd (vs_ne_Z x) hFR σ _ 0 (he.var x) he.zero
      he.zF he.zR hv hcap) (by omega)⟩
  | add x y a hxy hv =>
    exact ⟨_, he.setVar x _, WXExec.mono (BinW.add_spec cap C.Wd (vs_inj hxy) hFR σ _ _ (he.var x) (he.var y)
      he.zF he.zR hv hcap) (by omega)⟩
  | sub x y a hxy hv =>
    exact ⟨_, he.setVar x _, WXExec.mono (BinW.sub_spec cap C.Wd (vs_inj hxy) hFR σ _ _ (he.var x) (he.var y)
      he.zF he.zR hv (ha.env_lt x) hcap) (by omega)⟩
  | copy x y a hxy =>
    exact ⟨_, he.setVar x _, WXExec.mono (BinW.copy_spec cap C.Wd (vs_inj hxy) hFR σ _ _ (he.var x) (he.var y)
      he.zF he.zR hcap) (by omega)⟩
  | half x a =>
    exact ⟨_, he.setVar x _, WXExec.mono (BinW.half_spec cap C.Wd σ _ (he.var x) he.zR (ha.env_lt x) (by omega))
      (by omega)⟩
  | shl x a hv =>
    exact ⟨_, he.setVar x _, WXExec.mono (BinW.shl_spec cap C.Wd (vs_ne_Z x) hFR σ _ 0 (he.var x) he.zero
      he.zF he.zR hcap) (by omega)⟩
  | mul x y z a hxy hxz hyz hv =>
    have hm := BinW.mul_spec cap C.Wd (vs_inj hxy) (vs_inj hxz) (vs_ne_Z x) (vs_inj hyz) (vs_ne_Z y) (vs_ne_Z z)
      hFR (by lay_ne : (rF : Fin (NR M)) ≠ rG) (by lay_ne : (rR : Fin (NR M)) ≠ rG) σ _ _ _ 0 (he.var x) (he.var y)
      (he.var z) he.zero he.zF he.zR he.zG hv (ha.env_lt y) hcap
    have e := he.setVar z (a.env x * a.env y)
    refine ⟨_, e, WXExec.cast cap hm ?_ (le_trans (BinW.mulCost_le _) (by omega))⟩
    exact e.setZ
  | dm x y q r a hxy hxq hxr hyq hyr hqr hy h2y =>
    have hd := BinW.divmod_spec cap C.Wd (vs_inj hxq) (vs_inj hxr) (vs_ne_Z x) (vs_inj hyq) (vs_inj hyr)
      (vs_ne_Z y) (vs_inj hqr) (vs_ne_Z q) (vs_ne_Z r) hFR (by lay_ne : (rF : Fin (NR M)) ≠ rK)
      (by lay_ne : (rR : Fin (NR M)) ≠ rK) (by lay_ne : (rK : Fin (NR M)) ≠ rT) σ _ _ _ _ 0 (he.var x) (he.var y)
      (he.var q) (he.var r) he.zero he.zF he.zR he.zK he.zT (ha.env_lt x) hy h2y hcap
    have e := (he.setVar q (a.env x / a.env y)).setVar r (a.env x % a.env y)
    refine ⟨_, e, WXExec.cast cap hd ?_ (le_trans (BinW.divCost_le _) (by omega))⟩
    exact e.setZ
  | rdI x a _ => exact hA.elim
  | bkI a _ => exact hA.elim
  | emit bb a => exact hA.elim
  | rdM m x a _ => exact hA.elim
  | wrM m x a _ => exact hA.elim
  | rwM m a => exact hA.elim
  | srtM m a _ => exact hA.elim
  | kem bb a _ => exact hA.elim
  | kcall s a _ _ => exact hA.elim
  | rdK x a _ => exact hA.elim

/-- The test of a condition into `F`. -/
theorem condP_ok (he : Enc C a σ) (ha : Valid C a) {c : Cnd V} (hc : c.wf) (hcap : 2 * C.Wd + 1 ≤ cap) :
    WXExec cap (condP c) σ (σ.setv rF (c.eval a).toNat) (41 * C.Wd + 7) := by
  have hFR := fRne (M := M)
  cases c with
  | lt x y =>
    exact WXExec.mono (BinW.lt_spec cap C.Wd (vs_inj hc) hFR σ _ _ (he.var x) (he.var y) he.zF he.zR
      (ha.env_lt x) (ha.env_lt y) hcap) (by omega)
  | eq x y =>
    exact BinW.eq_spec cap C.Wd (vs_inj hc) hFR σ _ _ (he.var x) (he.var y) he.zF he.zR (ha.env_lt x)
      (ha.env_lt y) hcap

end Ops

theorem numOn_other {ns nr : ℕ} {σ σ' : WState ns nr} {i : Fin (ns + 1)} {W v : ℕ}
    (h : NumOn σ i W v) (hst : σ'.st i = σ.st i) (hsh : σ'.sh i = σ.sh i) : NumOn σ' i W v :=
  ⟨hst.trans h.1, hsh.trans h.2⟩

/-! ## The entry cursor, the output, the stores -/

section IO
variable (C : Ctx) (cap : ℕ) {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

/-- States equal after commuting updates at distinct indices. -/
macro "wst_eq" : tactic => `(tactic| (
  apply WState.eq
  all_goals (try funext i)
  all_goals (try simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setv_st, WState.seth_st,
    WState.sets_st, WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_cell, WState.seth_cell,
    WState.sets_cell, Function.update_apply])
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)))

/-- `rdI x`: read the bit at the cursor into `x`, advance. -/
theorem rdI_ok (he : Enc C a σ) (hW : 1 ≤ C.Wd) (hcap : 2 * C.Wd + 1 ≤ cap) (hcapI : 2 * C.inp.length + 2 ≤ cap)
    (x : Fin V) (hc : a.ip < C.inp.length) :
    ∃ τ, Enc C { a.set x (bitOf C.inp a.ip) with ip := a.ip + 1 } τ ∧
      WXExec cap (compB (.rdI x)) σ τ (1 * KC C) := by
  have hK := KC_ge C
  have hFR := fRne (M := M)
  have s1 := WXExec.fwd cap sIN σ
  have s2 := WXExec.inc cap rIP (σ.seth sIN (σ.sh sIN + 1)) (by simp [he.inR]; omega)
  set σ2 := (σ.seth sIN (σ.sh sIN + 1)).setv rIP ((σ.seth sIN (σ.sh sIN + 1)).val rIP + 1) with hσ2
  have hnA : NumOn σ2 (vs x) C.Wd (a.env x) := numOn_other (he.var x) (by simp [hσ2])
    (by simp [hσ2, Function.update_of_ne (show (vs x : Fin (NS M (TS C) V + 1)) ≠ sIN by lay_ne)])
  have hnZ : NumOn σ2 sZ C.Wd 0 := numOn_other he.zero (by simp [hσ2])
    (by simp [hσ2, Function.update_of_ne (show (sZ : Fin (NS M (TS C) V + 1)) ≠ sIN by lay_ne)])
  have hF2 : σ2.val rF = 0 := by
    simp [hσ2, Function.update_of_ne (show (rF : Fin (NR M)) ≠ rIP by lay_ne), he.zF]
  have hR2 : σ2.val rR = 0 := by
    simp [hσ2, Function.update_of_ne (show (rR : Fin (NR M)) ≠ rIP by lay_ne), he.zR]
  have hbit : wbit σ2 sIN = C.inp.getD a.ip false := by
    simp only [wbit, hσ2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self,
      he.inS, he.inH, readTapeBit]
    exact frame_odd' C.inp a.ip
  set v := bitOf C.inp a.ip with hv
  have s3 : WXExec cap (.ifs sIN (cOne x) (cZero x)) σ2 (σ2.sets (vs x) (frame (binary C.Wd v)))
      (41 * C.Wd + 8) := by
    cases hb : C.inp.getD a.ip false
    · have hv0 : v = 0 := by rw [hv, bitOf, hb]; rfl
      rw [hv0]
      exact WXExec.ifsF (by rw [hbit, hb]) (WXExec.mono (BinW.zero_spec cap C.Wd (vs_ne_Z x) hFR σ2 _ 0 hnA hnZ
        hF2 hR2 hcap) (by omega))
    · have hv1 : v = 1 := by rw [hv, bitOf, hb]; rfl
      rw [hv1]
      exact WXExec.ifsT (by rw [hbit, hb]) (BinW.one_spec cap C.Wd (vs_ne_Z x) hFR σ2 _ 0 hnA hnZ hF2 hR2 hW hcap)
  set σ3 := σ2.sets (vs x) (frame (binary C.Wd v))
  have s4 := WXExec.fwd cap sIN σ3
  have s5 := WXExec.inc cap rIP (σ3.seth sIN (σ3.sh sIN + 1)) (by
    simp [σ3, hσ2, he.inR]; omega)
  have hfin := (he.setVar x v).setIP (a.ip + 1)
  refine ⟨_, hfin, WXExec.cast cap (WXExec.seq' cap s1 (WXExec.seq' cap s2 (WXExec.seq' cap s3
    (WXExec.seq' cap s4 s5 le_rfl) le_rfl) le_rfl) le_rfl) ?_ (by omega)⟩
  have h1 := he.inH
  have h2 := he.inR
  simp only [σ3, hσ2]
  wst_eq

/-- `bkI`: the cursor steps back. -/
theorem bkI_ok (he : Enc C a σ) (hp : 0 < a.ip) (hcapI : 2 * C.inp.length + 2 ≤ cap) (hip : a.ip ≤ C.inp.length) :
    ∃ τ, Enc C { a with ip := a.ip - 1 } τ ∧ WXExec cap (compB (.bkI : Op V M)) σ τ (1 * KC C) := by
  have hK := KC_ge C
  have s1 := WXExec.bwd cap sIN σ
  have s2 := WXExec.dec cap rIP (σ.seth sIN (σ.sh sIN - 1)) (by simp [he.inR]; omega)
  set σ2 := (σ.seth sIN (σ.sh sIN - 1)).setv rIP ((σ.seth sIN (σ.sh sIN - 1)).val rIP - 1) with hσ2
  have s3 := WXExec.bwd cap sIN σ2
  have s4 := WXExec.dec cap rIP (σ2.seth sIN (σ2.sh sIN - 1)) (by simp [hσ2, he.inR]; omega)
  have hfin := he.setIP (a.ip - 1)
  refine ⟨_, hfin, WXExec.cast cap (WXExec.seq' cap s1 (WXExec.seq' cap s2 (WXExec.seq' cap s3 s4 le_rfl) le_rfl)
    le_rfl) ?_ (by omega)⟩
  have h1 := he.inH
  have h2 := he.inR
  simp only [hσ2]
  wst_eq

theorem writeTapeBit_end' (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [writeTapeBit, ih]

/-- `emit b`. -/
theorem emit_ok (he : Enc C a σ) (hcapO : a.out.length + 1 ≤ cap) (bb : Bool) :
    ∃ τ, Enc C { a with out := a.out ++ [bb] } τ ∧ WXExec cap (compB (.emit bb : Op V M)) σ τ (1 * KC C) := by
  have hK := KC_ge C
  have h1 := WXExec.wr cap sOUT bb σ
  rw [he.outS, he.outH, writeTapeBit_end'] at h1
  have h2 := WXExec.fwd cap sOUT (σ.sets sOUT (a.out ++ [bb]))
  have h3 := WXExec.inc cap rOP ((σ.sets sOUT (a.out ++ [bb])).seth sOUT ((σ.sets sOUT (a.out ++ [bb])).sh sOUT + 1))
    (by simp [he.outR]; omega)
  refine ⟨_, he.setOut bb, WXExec.cast cap (WXExec.seq' cap h1 (WXExec.seq' cap h2 h3 le_rfl) le_rfl) ?_
    (by omega)⟩
  simp only [WState.sets_sh, WState.seth_val, WState.sets_val, he.outH, he.outR]

theorem Enc.congrDS {C : Ctx} {a a' : DS V M} {σ : WState (NS M (TS C) V) (NR M)} (h : Enc C a σ) (e : a = a') :
    Enc C a' σ := e ▸ h

theorem enc_take_length (W : ℕ) (l : List ℕ) (i : ℕ) (hi : i ≤ l.length) :
    (enc W (l.take i)).length = (2 * W + 1) * i := by
  rw [enc_length, List.length_take, min_eq_left hi]

/-- `rdM m x`: read the record at the cursor of store `m` into `x`, advance. -/
theorem rdM_ok (he : Enc C a σ) (m : Fin M) (x : Fin V) (hr : a.rc m < (a.ram m).length)
    (hcapM : (2 * C.Wd + 1) * ((a.ram m).length + 1) + 1 ≤ cap) :
    ∃ τ, Enc C ((a.set x ((a.ram m).getD (a.rc m) 0)).adv m) τ ∧
      WXExec cap (compB (.rdM m x)) σ τ (1 * KC C) := by
  have hK := KC_ge C
  set l := a.ram m
  set i := a.rc m
  set v := l.getD i 0
  have hI : σ.st (sM m) = enc C.Wd (l.take i) ++ frameP (binary C.Wd v) ++ false :: encR C.Wd (l.drop (i + 1)) := by
    rw [he.ramS m]; exact encR_split C.Wd l i hr
  have hlen := enc_take_length C.Wd l i hr.le
  have hc := copyRec_spec cap (I := sM m) (Wk := vs x) (CI := rM m) (CW := rC1) (by lay_ne) (by lay_ne) σ
    (enc C.Wd (l.take i)) (binary C.Wd v) (encR C.Wd (l.drop (i + 1))) hI (by rw [he.ramH m, hlen])
    (by rw [he.ramR m, hlen]) (he.var x).2 he.zC1 (by rw [(he.var x).1, frame_binary_length, binary_length])
    (by rw [hlen, binary_length]; nlinarith)
  have hsh : ((σ.sets (vs x) (frame (binary C.Wd v))).st (sS m)).length ≤ (encR C.Wd l).length := by
    simp only [WState.sets_st]; rw [Function.update_of_ne (by lay_ne), ← he.ramS m]; exact he.shL m
  have hfin0 := (he.setVar x v).setRam m l (i + 1) hsh
  have hfin := hfin0.congrDS (show _ = (a.set x v).adv m by simp [DS.adv, DS.set, l, i, Function.update_eq_self])
  refine ⟨_, hfin, WXExec.cast cap (WXExec.wm hc) ?_ (by rw [binary_length]; omega)⟩
  rw [hlen, binary_length]
  have hst : (σ.sets (vs x) (frame (binary C.Wd v))).st (sM m) = encR C.Wd l := by
    simp only [WState.sets_st]; rw [Function.update_of_ne (by lay_ne)]; exact he.ramS m
  rw [BinW.sets_same hst]
  have e2 : (2 * C.Wd + 1) * i + 2 * C.Wd + 1 = (2 * C.Wd + 1) * (i + 1) := by ring
  rw [e2]

theorem write_same : ∀ (l : List Bool) (p : ℕ), p < l.length → writeTapeBit l p (l.getD p false) = l
  | [], _, h => absurd h (by simp)
  | b :: l, 0, _ => rfl
  | b :: l, p + 1, h => by
    simp only [writeTapeBit, List.getD_cons_succ]
    rw [write_same l p (by simp at h; omega)]

theorem enc_frame_true (W : ℕ) (hW : 1 ≤ W) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    readTapeBit (encR W l) ((2 * W + 1) * i) = true := by
  rw [encR_split W l i hi]
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ (by simp [enc_take_length W l i hi.le, frameP, binary_length]; nlinarith)]
  rw [List.getD_append_right _ _ _ _ (by rw [enc_take_length W l i hi.le])]
  rw [enc_take_length W l i hi.le, Nat.sub_self]
  rcases hb : binary W (l.getD i 0) with _ | ⟨b, bs⟩
  · have := binary_length W (l.getD i 0); rw [hb] at this; simp at this; omega
  · simp [frameP]

theorem encR_end_false (W : ℕ) (l : List ℕ) : readTapeBit (encR W l) ((2 * W + 1) * l.length) = false := by
  unfold readTapeBit encR
  rw [List.getD_append_right _ _ _ _ (by rw [enc_length])]
  simp [enc_length]

/-- After `appendRec` at record `i ≤ |l|`, reading the cell at the new head decides the final write. -/
theorem putAt_fix (W : ℕ) (l : List ℕ) (i v : ℕ) (hi : i ≤ l.length) :
    (readTapeBit (overlay (enc W (l.take i) ++ frame (binary W v)) (encR W l)) ((2 * W + 1) * (i + 1)) = true →
      overlay (enc W (l.take i) ++ frame (binary W v)) (encR W l) = encR W (putAt l i v)) ∧
    (readTapeBit (overlay (enc W (l.take i) ++ frame (binary W v)) (encR W l)) ((2 * W + 1) * (i + 1)) = false →
      writeTapeBit (overlay (enc W (l.take i) ++ frame (binary W v)) (encR W l)) ((2 * W + 1) * (i + 1)) false =
        encR W (putAt l i v)) := by
  by_cases hlt : i < l.length
  · have hc : overlay (enc W (l.take i) ++ frame (binary W v)) (encR W l) = encR W (putAt l i v) := by
      show overlay (enc W (l.take i) ++ frame (binary W v)) (enc W l ++ [false]) = enc W (putAt l i v) ++ [false]
      have hlen : (enc W (l.take i) ++ frame (binary W v)).length ≤ (enc W l).length := by
        rw [List.length_append, enc_take_length W l i hi, frame_binary_length, enc_length]; nlinarith
      rw [overlay, List.drop_append_of_le_length hlen, ← List.append_assoc]
      have := enc_putAt W l i v hi
      rw [overlay] at this; rw [this]
    refine ⟨fun _ => hc, fun hf => ?_⟩
    rw [hc]; rw [hc] at hf
    have hl : (2 * W + 1) * (i + 1) < (encR W (putAt l i v)).length := by
      rw [encR_length, putAt_length _ _ _ hi]
      have : max l.length (i + 1) = l.length := by omega
      rw [this]; nlinarith
    have := write_same (encR W (putAt l i v)) _ hl
    unfold readTapeBit at hf
    rwa [hf] at this
  · have hi' : i = l.length := by omega
    subst hi'
    have hc : overlay (enc W (l.take l.length) ++ frame (binary W v)) (encR W l) = enc W (l ++ [v]) := by
      show overlay (enc W (l.take l.length) ++ frame (binary W v)) (enc W l ++ [false]) = enc W (l ++ [v])
      rw [List.take_of_length_le le_rfl, overlay, List.drop_eq_nil_of_le (by simp)]
      simp [enc]
    have hh : (2 * W + 1) * (l.length + 1) = (enc W (l ++ [v])).length := by rw [enc_length]; simp
    refine ⟨fun ht => ?_, fun _ => ?_⟩
    · exfalso; rw [hc, hh] at ht; unfold readTapeBit at ht; simp at ht
    · rw [hc, hh, writeTapeBit_end']
      simp [putAt, encR]

/-- `wrM m x`: write `x` at the cursor of store `m` (appending at the end), advance. -/
theorem wrM_ok (he : Enc C a σ) (m : Fin M) (x : Fin V) (hr : a.rc m ≤ (a.ram m).length)
    (hcapM : (2 * C.Wd + 1) * ((a.ram m).length + 1) + 1 ≤ cap) :
    ∃ τ, Enc C (a.put m (a.env x)) τ ∧ WXExec cap (compB (.wrM m x)) σ τ (1 * KC C) := by
  have hK := KC_ge C
  set l := a.ram m
  set i := a.rc m
  have hlen := enc_take_length C.Wd l i hr
  have hO : OutOn σ (sM m) (rM m) (enc C.Wd (l.take i)) (encR C.Wd l) := by
    refine ⟨?_, by rw [he.ramH m, hlen], by rw [he.ramR m, hlen]⟩
    have hsplit : encR C.Wd l = enc C.Wd (l.take i) ++ encR C.Wd (l.drop i) := by
      simp only [encR]; rw [← List.append_assoc, ← enc_append, List.take_append_drop]
    rw [he.ramS m]
    show encR C.Wd l = overlay (enc C.Wd (l.take i)) (encR C.Wd l)
    conv_rhs => rw [overlay, hsplit, List.drop_left]
    exact hsplit
  have hS : σ.st (vs x) = frameP (binary C.Wd (a.env x)) ++ false :: [] := by
    rw [(he.var x).1, frame_eq_frameP]
  have hc := appendRec_spec cap (Src := vs x) (O := sM m) (CS := rC1) (CO := rM m) (by lay_ne) (by lay_ne) σ
    (binary C.Wd (a.env x)) [] (enc C.Wd (l.take i)) (encR C.Wd l) hS (he.var x).2 he.zC1 hO
    (by rw [hlen, binary_length]; nlinarith)
  set c := overlay (enc C.Wd (l.take i) ++ frame (binary C.Wd (a.env x))) (encR C.Wd l) with hcdef
  have hh : (enc C.Wd (l.take i) ++ frame (binary C.Wd (a.env x))).length = (2 * C.Wd + 1) * (i + 1) := by
    rw [List.length_append, hlen, frame_binary_length]; ring
  set σA := ((σ.sets (sM m) c).seth (sM m) (enc C.Wd (l.take i) ++ frame (binary C.Wd (a.env x))).length).setv (rM m)
    (enc C.Wd (l.take i) ++ frame (binary C.Wd (a.env x))).length with hσA
  have fix := putAt_fix C.Wd l i (a.env x) hr
  have hshl : (σ.st (sS m)).length ≤ (encR C.Wd (putAt l i (a.env x))).length := by
    have h1 : (σ.st (sS m)).length ≤ (2 * C.Wd + 1) * l.length + 1 := by
      have := he.shL m; rw [he.ramS m, encR_length] at this; exact this
    rw [encR_length, putAt_length _ _ _ hr]
    have h2 : (2 * C.Wd + 1) * l.length ≤ (2 * C.Wd + 1) * max l.length (i + 1) :=
      Nat.mul_le_mul_left _ (le_max_left _ _)
    omega
  have hfin := he.setRam m (putAt l i (a.env x)) (i + 1) hshl
  have hbit : wbit σA (sM m) = readTapeBit c ((2 * C.Wd + 1) * (i + 1)) := by
    simp only [wbit, hσA, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
      Function.update_self, hh]
  refine ⟨_, hfin, ?_⟩
  cases hb : readTapeBit c ((2 * C.Wd + 1) * (i + 1))
  · have w1 := WXExec.wr cap (sM m) false σA
    have e : σA.sets (sM m) (writeTapeBit (σA.st (sM m)) (σA.sh (sM m)) false) =
        ((σ.sets (sM m) (encR C.Wd (putAt l i (a.env x)))).seth (sM m) ((2 * C.Wd + 1) * (i + 1))).setv (rM m)
          ((2 * C.Wd + 1) * (i + 1)) := by
      simp only [hσA, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self, hh]
      rw [hcdef, fix.2 hb]
      wst_eq
    rw [e] at w1
    exact WXExec.mono (WXExec.seq' cap (WXExec.wm hc) (WXExec.ifsF (by rw [hbit, hb]) w1) le_rfl)
      (by rw [binary_length]; omega)
  · have e : σA = ((σ.sets (sM m) (encR C.Wd (putAt l i (a.env x)))).seth (sM m) ((2 * C.Wd + 1) * (i + 1))).setv
        (rM m) ((2 * C.Wd + 1) * (i + 1)) := by
      simp only [hσA, hh]; rw [hcdef, fix.1 hb]
    have w0 : WXExec cap WMX.skip σA (((σ.sets (sM m) (encR C.Wd (putAt l i (a.env x)))).seth (sM m)
        ((2 * C.Wd + 1) * (i + 1))).setv (rM m) ((2 * C.Wd + 1) * (i + 1))) 0 := by
      rw [← e]; exact WXExec.skip cap σA
    exact WXExec.mono (WXExec.seq' cap (WXExec.wm hc) (WXExec.ifsT (by rw [hbit, hb]) w0) le_rfl)
      (by rw [binary_length]; omega)

/-- `rwM m`: rewind store `m`. -/
theorem rwM_ok (he : Enc C a σ) (m : Fin M) (hr : a.rc m ≤ (a.ram m).length)
    (hcapM : (2 * C.Wd + 1) * ((a.ram m).length + 1) + 1 ≤ cap) :
    ∃ τ, Enc C (a.rew m) τ ∧ WXExec cap (compB (.rwM m)) σ τ ((a.rc m + 1) * KC C) := by
  have hK := KC_ge C
  have hc := wrewind_spec cap (sM m) (rM m) ((2 * C.Wd + 1) * a.rc m) σ (he.ramR m)
    (by rw [he.ramR m]; nlinarith)
  have hfin0 := he.setRam m (a.ram m) 0 (by rw [← he.ramS m]; exact he.shL m)
  have hfin := hfin0.congrDS (show _ = a.rew m by simp [DS.rew, Function.update_eq_self])
  refine ⟨_, hfin, WXExec.cast cap (WXExec.wm hc) ?_ (by nlinarith)⟩
  rw [he.ramH m, Nat.sub_self, mul_zero, BinW.sets_same (he.ramS m)]
  wst_eq

end IO

end NearCubicGates.Close.Cells
