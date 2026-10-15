import Proof.Wire_3_5.FinalPassWordAux
import Proof.Wire_3_5.FinalPassHashTable
import Proof.Wire_3_5.FinalPassFiltTabRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout -/

scoped notation "qV" => (0 : Fin 12)
scoped notation "qO" => (1 : Fin 12)
scoped notation "qTAU" => (2 : Fin 12)
scoped notation "qPM" => (3 : Fin 12)
scoped notation "qFV" => (4 : Fin 12)
scoped notation "qFU" => (5 : Fin 12)
scoped notation "qPW" => (6 : Fin 12)
scoped notation "qACC" => (7 : Fin 12)
scoped notation "qST" => (8 : Fin 12)
scoped notation "qK" => (9 : Fin 12)
scoped notation "qBW" => (10 : Fin 12)
scoped notation "qEP" => (11 : Fin 12)

scoped notation "gF" => (0 : Fin 19)
scoped notation "gG" => (1 : Fin 19)
scoped notation "gR" => (2 : Fin 19)
scoped notation "gRY" => (3 : Fin 19)
scoped notation "gVP" => (4 : Fin 19)
scoped notation "gOP" => (5 : Fin 19)
scoped notation "gM" => (6 : Fin 19)
scoped notation "gLB" => (7 : Fin 19)
scoped notation "gLB1" => (8 : Fin 19)
scoped notation "gA" => (9 : Fin 19)
scoped notation "gL" => (10 : Fin 19)
scoped notation "gT" => (11 : Fin 19)
scoped notation "gCK" => (12 : Fin 19)
scoped notation "gS" => (13 : Fin 19)
scoped notation "gNS" => (14 : Fin 19)
scoped notation "gTF" => (15 : Fin 19)
scoped notation "gEP" => (16 : Fin 19)
scoped notation "gJ" => (17 : Fin 19)
scoped notation "gBWP" => (18 : Fin 19)

abbrev TState := WState 11 19
abbrev TProg := WM 11 19

/-- The builder's state at a phase boundary. -/
structure TSt where
  vw : List Bool
  ow : List Bool
  tauw : List Bool
  pmw : List Bool
  fv : List Bool
  fu : List Bool
  pw : List Bool
  acc : List Bool
  st : List Bool
  kw : List Bool
  bw : List Bool
  ep : List Bool
  vh : ℕ
  bwh : ℕ
  eph : ℕ
  f : ℕ
  ck : ℕ
  s : ℕ
  ns : ℕ
  tf : ℕ
  j : ℕ
  m : ℕ
  lb : ℕ
  a : ℕ
  L : ℕ
  cell : Bool

/-- The word state of a phase record. -/
def TSt.w (x : TSt) : TState :=
  ⟨![x.vh, x.ow.length, 0, 0, 0, 0, 0, 0, 0, 0, x.bwh, x.eph],
   ![x.vw, x.ow, x.tauw, x.pmw, x.fv, x.fu, x.pw, x.acc, x.st, x.kw, x.bw, x.ep],
   ![x.f, 0, 0, 0, x.vh, x.ow.length, x.m, x.lb, x.lb - 1, x.a, x.L, 0, x.ck, x.s, x.ns, x.tf, x.eph, x.j, x.bwh],
   x.cell⟩

/-- Close an equality of word states against phase records. -/
syntax "tst_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| tst_eq) => `(tactic| tst_eq [])
  | `(tactic| tst_eq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [TSt.w, $ts,*]; done) | (simp [TSt.w, $ts,*] <;> omega))
        | rfl
        | (simp [TSt.w, $ts,*]; done)))

variable (cap : ℕ)

/-! ## Words -/

theorem frameP_append (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

theorem frameP_split (l : List Bool) (n : ℕ) : frameP l = frameP (l.take n) ++ frameP (l.drop n) := by
  rw [← frameP_append, List.take_append_drop]

theorem parW_eq : ∀ (as bs : List Bool), parW as bs = parityDot as bs
  | a :: as, b :: bs => by simp [parW, parityDot, parW_eq as bs]
  | [], _ => by simp [parW, parityDot]
  | _ :: _, [] => by simp [parW, parityDot]

theorem parityDot_comm : ∀ (as bs : List Bool), parityDot as bs = parityDot bs as
  | a :: as, b :: bs => by simp [parityDot, parityDot_comm as bs, Bool.and_comm]
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-! ## Single updates of a phase record -/

theorem w_f (x : TSt) (n : ℕ) : x.w.setv gF n = { x with f := n }.w := by tst_eq
theorem w_ns (x : TSt) (n : ℕ) : x.w.setv gNS n = { x with ns := n }.w := by tst_eq
theorem w_tf (x : TSt) (n : ℕ) : x.w.setv gTF n = { x with tf := n }.w := by tst_eq
theorem w_s (x : TSt) (n : ℕ) : x.w.setv gS n = { x with s := n }.w := by tst_eq
theorem w_ck (x : TSt) (n : ℕ) : x.w.setv gCK n = { x with ck := n }.w := by tst_eq
theorem w_j (x : TSt) (n : ℕ) : x.w.setv gJ n = { x with j := n }.w := by tst_eq
theorem w_bw_fwd (x : TSt) : (x.w.seth qBW (x.w.sh qBW + 1)).setv gBWP (x.w.val gBWP + 1) =
    { x with bwh := x.bwh + 1 }.w := by tst_eq
theorem w_ep_adv (x : TSt) (n : ℕ) : (x.w.seth qEP (x.w.sh qEP + 2 * n)).setv gEP (x.w.val gEP + 2 * n) =
    { x with eph := x.eph + 2 * n }.w := by tst_eq
theorem w_ep_ret (x : TSt) (n : ℕ) : (x.w.seth qEP (x.w.sh qEP - 2 * n)).setv gEP (x.w.val gEP - 2 * n) =
    { x with eph := x.eph - 2 * n }.w := by tst_eq
theorem w_v_adv (x : TSt) (n : ℕ) : (x.w.seth qV (x.w.sh qV + 2 * n)).setv gVP (x.w.val gVP + 2 * n) =
    { x with vh := x.vh + 2 * n }.w := by tst_eq
theorem w_kw (x : TSt) (l : List Bool) : x.w.sets qK l = { x with kw := l }.w := by tst_eq
theorem w_fv (x : TSt) (l : List Bool) : x.w.sets qFV l = { x with fv := l }.w := by tst_eq
theorem w_fu (x : TSt) (l : List Bool) : x.w.sets qFU l = { x with fu := l }.w := by tst_eq
theorem w_pw (x : TSt) (l : List Bool) : x.w.sets qPW l = { x with pw := l }.w := by tst_eq
theorem w_acc (x : TSt) (l : List Bool) : x.w.sets qACC l = { x with acc := l }.w := by tst_eq
theorem w_st (x : TSt) (l : List Bool) : x.w.sets qST l = { x with st := l }.w := by tst_eq
theorem w_bw (x : TSt) (l : List Bool) : x.w.sets qBW l = { x with bw := l }.w := by tst_eq
theorem w_ep (x : TSt) (l : List Bool) : x.w.sets qEP l = { x with ep := l }.w := by tst_eq
theorem w_o_emit (x : TSt) (b : Bool) :
    ((x.w.sets qO (x.w.st qO ++ [b])).seth qO (x.w.sh qO + 1)).setv gOP (x.w.val gOP + 1) =
      { x with ow := x.ow ++ [b] }.w := by tst_eq

/-- Record the comparison of a translation bit with a window parity. -/
def cmpFlag : TProg := .ifs qBW (.ifr gF .skip (setFlag gNS true)) (.ifr gF (setFlag gNS true) .skip)

theorem cmpFlag_spec (x : TSt) (bb pb nb : Bool) (hread : wbit x.w qBW = bb) (hF : x.f = pb.toNat)
    (hns : x.ns = nb.toNat) (hcap : 1 ≤ cap) :
    WExec cap cmpFlag x.w { x with ns := (nb || xor bb pb).toNat }.w 6 := by
  have hsf := setFlag_spec cap gNS true nb x.w hns hcap
  rw [w_ns] at hsf
  have hx : x = { x with ns := nb.toNat } := by rw [← hns]
  have hF' : x.w.val gF = pb.toNat := hF
  unfold cmpFlag
  cases bb <;> cases pb
  · refine WExec.cast cap (WExec.ifsF hread (WExec.ifrF (P := setFlag gNS true) (Q := .skip) hF' (WExec.skip _)))
      ?_ (by omega)
    simp only [Bool.xor_false, Bool.or_false]; rw [← hx]
  · exact WExec.cast cap (WExec.ifsF hread (WExec.ifrT (by rw [hF']; decide) hsf)) (by simp) (by omega)
  · exact WExec.cast cap (WExec.ifsT hread (WExec.ifrF hF' hsf)) (by simp) (by omega)
  · refine WExec.cast cap (WExec.ifsT hread (WExec.ifrT (P := .skip) (Q := setFlag gNS true) (by rw [hF']; decide)
      (WExec.skip _))) ?_ (by omega)
    simp only [Bool.xor_self, Bool.or_false]; rw [← hx]

/-! ## One row of the inclusion test -/

/-- One row: the window parity against the label, compared with the translation bit. -/
def selStep : TProg :=
  .seq (advC qEP gS gT gEP)
  (.seq (mapPass keepA parNxt qK qEP gF gR)
  (.seq (retC qEP gS gT gEP)
  (.seq (WM.fwdC qBW gBWP)
  (.seq cmpFlag
  (.seq (WM.fwdC qBW gBWP)
  (.seq (setFlag gF false)
  (.dec gS)))))))

/-- The window of row `i` in the diagonal word. -/
def winOf (ep : List Bool) (lb i : ℕ) : List Bool := (ep.drop (lb - 1 - i)).take lb

/-- The cost of one row. -/
def selStepCost (lb : ℕ) : ℕ := 90 * lb + 40

theorem selStep_spec (x : TSt) (kb epb bwb : List Bool) (i : ℕ) (nb : Bool)
    (hk : x.kw = frameP kb ++ [false]) (hkl : kb.length = x.lb)
    (hep : x.ep = frameP epb ++ [false]) (hepl : epb.length = 2 * x.lb - 1)
    (hbw : x.bw = frameP bwb ++ [false]) (hbwl : bwb.length = x.lb)
    (hi : i < x.lb) (hs : x.s = x.lb - 1 - i) (heph : x.eph = 0) (hbwh : x.bwh = 2 * i) (hf : x.f = 0)
    (hns : x.ns = nb.toNat) (hcap : 4 * x.lb + 4 ≤ cap) :
    WExec cap selStep x.w
      { x with bwh := 2 * i + 2, s := x.s - 1,
               ns := (nb || xor (bwb.getD i false) (parW kb (winOf epb x.lb i))).toNat }.w (selStepCost x.lb) := by
  obtain ⟨pb, hpb⟩ : ∃ b : Bool, b = parW kb (winOf epb x.lb i) := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ b : Bool, b = bwb.getD i false := ⟨_, rfl⟩
  rw [← hpb, ← hbb]
  -- 1: EP to the window
  have s1 := advC_spec cap qEP gS gT gEP (by decide) (by decide) (by decide) x.s x.w rfl rfl (by omega)
    (by show x.eph + 2 * x.s ≤ cap; omega)
  rw [w_ep_adv] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with eph := x.eph + 2 * x.s } := ⟨_, rfl⟩
  rw [← hx1] at s1
  -- 2: the parity pass
  have hwin : (winOf epb x.lb i).length = x.lb := by unfold winOf; simp [hepl]; omega
  have hsplit : epb = epb.take x.s ++ (winOf epb x.lb i ++ epb.drop (x.s + x.lb)) := by
    have h1 := (List.take_append_drop x.s epb).symm
    have h2 := (List.take_append_drop x.lb (epb.drop x.s)).symm
    have h3 : (epb.drop x.s).drop x.lb = epb.drop (x.s + x.lb) := by rw [List.drop_drop]
    rw [h3] at h2
    rw [winOf, ← hs, ← h2, ← h1]
  have hEP1 : x1.w.st qEP = frameP (epb.take x.s) ++ frameP (winOf epb x.lb i) ++
      (frameP (epb.drop (x.s + x.lb)) ++ [false]) := by
    rw [hx1]
    show x.ep = _
    rw [hep]
    conv_lhs => rw [hsplit]
    rw [frameP_append, frameP_append]
    simp only [List.append_assoc]
  have s2 := mapPassAt_spec cap keepA parNxt qK qEP gF gR (by decide) (by decide) (by omega) kb (winOf epb x.lb i)
    [] (frameP (epb.take x.s)) [] (frameP (epb.drop (x.s + x.lb)) ++ [false]) false x1.w
    (by rw [hkl, hwin]) (by rw [hx1]; show x.kw = _; rw [hk]; simp) (by rw [hx1]; rfl) hEP1
    (by rw [hx1]; show x.eph + 2 * x.s = _; simp [frameP_length]; omega) (by rw [hx1]; show x.f = _; simp [hf])
    (by rw [hx1]; rfl) (by rw [hkl]; omega)
  rw [mapS_par kb _ false (by rw [hkl, hwin]), ← hpb] at s2
  simp only [List.nil_append, Bool.false_xor] at s2
  have hK1 : frameP kb ++ false :: [] = x1.kw := by rw [hx1]; exact hk.symm
  rw [hK1, w_kw, w_f] at s2
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { { x1 with kw := x1.kw } with f := pb.toNat } := ⟨_, rfl⟩
  rw [← hx2] at s2
  -- 3: EP back
  have s3 := retC_spec cap qEP gS gT gEP (by decide) (by decide) (by decide) x.s x2.w
    (by rw [hx2, hx1]; rfl) (by rw [hx2]; rfl) (by omega) (by rw [hx2, hx1]; show x.eph + 2 * x.s ≤ cap; omega)
  rw [w_ep_ret] at s3
  obtain ⟨x3, hx3⟩ : ∃ y : TSt, y = { x2 with eph := x2.eph - 2 * x.s } := ⟨_, rfl⟩
  rw [← hx3] at s3

  have s4 := wfwdC_spec cap qBW gBWP x3.w (by rw [hx3, hx2, hx1]; show x.bwh < cap; omega)
  rw [w_bw_fwd] at s4
  obtain ⟨x4, hx4⟩ : ∃ y : TSt, y = { x3 with bwh := x3.bwh + 1 } := ⟨_, rfl⟩
  rw [← hx4] at s4
  -- 5: compare with the translation bit
  have hread : wbit x4.w qBW = bb := by
    rw [hx4, hx3, hx2, hx1]
    show readTapeBit x.bw (x.bwh + 1) = _
    rw [hbw, hbwh, readTapeBit_frameP _ _ _ (by omega), hbb]
  have s5 := cmpFlag_spec cap x4 bb pb nb hread (by rw [hx4, hx3, hx2]) (by rw [hx4, hx3, hx2, hx1]; exact hns)
    (by omega)
  obtain ⟨x5, hx5⟩ : ∃ y : TSt, y = { x4 with ns := (nb || xor bb pb).toNat } := ⟨_, rfl⟩
  rw [← hx5] at s5

  have s6 := wfwdC_spec cap qBW gBWP x5.w (by rw [hx5, hx4, hx3, hx2, hx1]; show x.bwh + 1 < cap; omega)
  rw [w_bw_fwd] at s6
  obtain ⟨x6, hx6⟩ : ∃ y : TSt, y = { x5 with bwh := x5.bwh + 1 } := ⟨_, rfl⟩
  rw [← hx6] at s6
  -- 7: clear the flag
  have s7 := setFlag_spec cap gF false pb x6.w (by rw [hx6, hx5, hx4, hx3, hx2]; rfl) (by omega)
  rw [w_f] at s7
  obtain ⟨x7, hx7⟩ : ∃ y : TSt, y = { x6 with f := (false).toNat } := ⟨_, rfl⟩
  rw [← hx7] at s7
  -- 8: next row
  have s8 := WExec.dec (cap := cap) gS x7.w (by rw [hx7, hx6, hx5, hx4, hx3, hx2, hx1]; show x.s ≤ cap; omega)
  have e8 : x7.w.setv gS (x7.w.val gS - 1) = { x7 with s := x7.s - 1 }.w := by
    rw [w_s]; rfl
  rw [e8] at s8
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) ?_ ?_
  · have e : ({ x7 with s := x7.s - 1 } : TSt) =
        { x with bwh := 2 * i + 2, s := x.s - 1, ns := (nb || xor bb pb).toNat } := by
      rw [hx7, hx6, hx5, hx4, hx3, hx2, hx1]
      cases x with
      | mk vw ow tauw pmw fv fu pw acc st kw bw ep vh bwh eph f ck s ns tf j m lb a L cell =>
        simp only at hf heph hbwh ⊢
        subst hf heph hbwh
        simp only [TSt.mk.injEq, and_true, true_and, Nat.zero_add, Bool.toNat_false]
        omega
    rw [e]
  · unfold selStepCost; rw [hkl]; omega

/-! ## All rows of the inclusion test -/

/-- Some row `i' ∈ [i, i+n)` of the test fails: its hash bit is one. -/
def mism (kb epb bwb : List Bool) (lb i n : ℕ) : Bool :=
  (List.range' i n).any fun i' => xor (bwb.getD i' false) (parW kb (winOf epb lb i'))

/-- The rows, counted down in `J`. -/
def selLoop : TProg := .whr gJ (.seq selStep (.dec gJ))

theorem selLoop_spec (kb epb bwb : List Bool) (hkl : kb.length = epb.length / 2 + 1)
    (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1) (hbwl : bwb.length = epb.length / 2 + 1) :
    ∀ (n i : ℕ) (x : TSt) (nb : Bool), x.lb = epb.length / 2 + 1 →
      x.kw = frameP kb ++ [false] → x.ep = frameP epb ++ [false] → x.bw = frameP bwb ++ [false] →
      i + n ≤ x.lb → x.j = n → x.s = x.lb - 1 - i → x.eph = 0 → x.bwh = 2 * i → x.f = 0 → x.ns = nb.toNat →
      4 * x.lb + 4 ≤ cap →
      WExec cap selLoop x.w
        { x with j := 0, bwh := 2 * (i + n), s := x.s - n,
                 ns := (nb || mism kb epb bwb x.lb i n).toNat }.w (n * (selStepCost x.lb + 4) + 1)
  | 0, i, x, nb, _, _, _, _, _, hj, _, _, hbwh, _, hns, _ => by
    refine WExec.cast cap (WExec.whrF hj) ?_ (by omega)
    have e : ({ x with j := 0, bwh := 2 * (i + 0), s := x.s - 0, ns := (nb || mism kb epb bwb x.lb i 0).toNat } :
        TSt) = x := by
      cases x
      simp only at hj hns hbwh ⊢
      subst hj hns hbwh
      simp [mism]
    rw [e]
  | n + 1, i, x, nb, hlb, hk, hep, hbw, hin, hj, hs, heph, hbwh, hf, hns, hcap => by
    have s1 := selStep_spec cap x kb epb bwb i nb hk (by omega) hep (by omega) hbw (by omega) (by omega) hs heph hbwh hf
      hns hcap
    obtain ⟨nb1, hnb1⟩ : ∃ b : Bool, b = (nb || xor (bwb.getD i false) (parW kb (winOf epb x.lb i))) := ⟨_, rfl⟩
    rw [← hnb1] at s1
    obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with bwh := 2 * i + 2, s := x.s - 1, ns := nb1.toNat } := ⟨_, rfl⟩
    rw [← hx1] at s1
    have s2 := WExec.dec (cap := cap) gJ x1.w (by rw [hx1]; show x.j ≤ cap; omega)
    rw [w_j] at s2
    obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { x1 with j := x1.w.val gJ - 1 } := ⟨_, rfl⟩
    rw [← hx2] at s2
    have ih := selLoop_spec kb epb bwb hkl hepl hbwl n (i + 1) x2 nb1
      (by rw [hx2, hx1]; exact hlb) (by rw [hx2, hx1]; exact hk) (by rw [hx2, hx1]; exact hep)
      (by rw [hx2, hx1]; exact hbw) (by rw [hx2, hx1]; show i + 1 + n ≤ x.lb; omega)
      (by rw [hx2, hx1]; show x.j - 1 = n; omega) (by rw [hx2, hx1]; show x.s - 1 = x.lb - 1 - (i + 1); omega)
      (by rw [hx2, hx1]; exact heph) (by rw [hx2, hx1]; show 2 * i + 2 = 2 * (i + 1); omega)
      (by rw [hx2, hx1]; exact hf) (by rw [hx2, hx1]) (by rw [hx2, hx1]; exact hcap)
    refine WExec.cast cap (WExec.whrT (by show x.j ≠ 0; omega) (WExec.seq s1 s2) ih) ?_ ?_
    · obtain ⟨nb2, hnb2⟩ : ∃ b : Bool, b = (nb1 || mism kb epb bwb x2.lb (i + 1) n) := ⟨_, rfl⟩
      obtain ⟨nb3, hnb3⟩ : ∃ b : Bool, b = (nb || mism kb epb bwb x.lb i (n + 1)) := ⟨_, rfl⟩
      rw [← hnb2, ← hnb3]
      have hnb : nb2 = nb3 := by
        rw [hnb2, hnb3, hnb1, hx2, hx1]
        have hm : mism kb epb bwb x.lb i (n + 1) =
            (xor (bwb.getD i false) (parW kb (winOf epb x.lb i)) || mism kb epb bwb x.lb (i + 1) n) := by
          simp [mism, List.range'_succ]
        rw [hm, Bool.or_assoc]
      have e : ({ x2 with j := 0, bwh := 2 * (i + 1 + n), s := x2.s - n, ns := nb2.toNat } : TSt) =
          { x with j := 0, bwh := 2 * (i + (n + 1)), s := x.s - (n + 1), ns := nb3.toNat } := by
        rw [hnb, hx2, hx1]
        cases x
        simp only [TSt.mk.injEq, and_true, true_and]
        omega
      rw [e]
    · have hlb2 : x2.lb = x.lb := by rw [hx2, hx1]
      rw [hlb2]; nlinarith

theorem w_bw_rewind (x : TSt) : (x.w.setv gBWP 0).seth qBW (x.w.sh qBW - x.bwh) = { x with bwh := 0 }.w := by
  tst_eq

/-- **The inclusion test**: `NS := [some prefix hash bit is one]`. -/
def selT : TProg :=
  .seq (Hash4.wcopyR gLB1 gS gT) (.seq (Hash4.wcopyR gA gJ gT) (.seq selLoop (.seq (WM.clear gS)
    (WM.rewind qBW gBWP))))

/-- The cost of the inclusion test. -/
def selTCost (lb a : ℕ) : ℕ := 18 * lb + 18 * a + a * (selStepCost lb + 4) + 3 * lb + 5 * (2 * a) + 16

theorem selT_spec (x : TSt) (kb epb bwb : List Bool) (hlb : x.lb = epb.length / 2 + 1)
    (hkl : kb.length = epb.length / 2 + 1) (hepl : 1 ≤ epb.length ∧ epb.length % 2 = 1)
    (hbwl : bwb.length = epb.length / 2 + 1)
    (hk : x.kw = frameP kb ++ [false]) (hep : x.ep = frameP epb ++ [false]) (hbw : x.bw = frameP bwb ++ [false])
    (ha : x.a ≤ x.lb) (hs : x.s = 0) (hj : x.j = 0) (heph : x.eph = 0) (hbwh : x.bwh = 0) (hf : x.f = 0)
    (hns : x.ns = 0) (hcap : 4 * x.lb + 4 ≤ cap) :
    WExec cap selT x.w { x with ns := (mism kb epb bwb x.lb 0 x.a).toNat }.w (selTCost x.lb x.a) := by
  have s1 := Hash4.wcopyR_spec cap gLB1 gS gT (by decide) (by decide) (by decide) x.w (by exact hs) rfl
    (by show x.lb - 1 ≤ cap; omega)
  rw [w_s] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { x with s := x.w.val gLB1 } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have s2 := Hash4.wcopyR_spec cap gA gJ gT (by decide) (by decide) (by decide) x1.w (by rw [hx1]; exact hj)
    (by rw [hx1]; rfl) (by rw [hx1]; show x.a ≤ cap; omega)
  rw [w_j] at s2
  obtain ⟨x2, hx2⟩ : ∃ y : TSt, y = { x1 with j := x1.w.val gA } := ⟨_, rfl⟩
  rw [← hx2] at s2
  have s3 := selLoop_spec cap kb epb bwb hkl hepl hbwl x.a 0 x2 false (by rw [hx2, hx1]; exact hlb)
    (by rw [hx2, hx1]; exact hk) (by rw [hx2, hx1]; exact hep) (by rw [hx2, hx1]; exact hbw)
    (by rw [hx2, hx1]; show 0 + x.a ≤ x.lb; omega) (by rw [hx2, hx1]; rfl)
    (by rw [hx2, hx1]; show x.lb - 1 = x.lb - 1 - 0; omega) (by rw [hx2, hx1]; exact heph)
    (by rw [hx2, hx1]; exact hbwh) (by rw [hx2, hx1]; exact hf) (by rw [hx2, hx1]; exact hns)
    (by rw [hx2, hx1]; exact hcap)
  obtain ⟨m3, hm3⟩ : ∃ b : Bool, b = (false || mism kb epb bwb x2.lb 0 x.a) := ⟨_, rfl⟩
  rw [← hm3] at s3
  obtain ⟨x3, hx3⟩ : ∃ y : TSt, y = { x2 with j := 0, bwh := 2 * (0 + x.a), s := x2.s - x.a, ns := m3.toNat } :=
    ⟨_, rfl⟩
  rw [← hx3] at s3
  have s4 := wclear_spec cap gS (x3.s) x3.w rfl (by rw [hx3, hx2, hx1]; show x.lb - 1 - x.a ≤ cap; omega)
  rw [w_s] at s4
  obtain ⟨x4, hx4⟩ : ∃ y : TSt, y = { x3 with s := 0 } := ⟨_, rfl⟩
  rw [← hx4] at s4
  have s5 := wrewind_spec cap qBW gBWP x4.bwh x4.w rfl (by rw [hx4, hx3]; show 2 * (0 + x.a) ≤ cap; omega)
  have e5 : (x4.w.setv gBWP 0).seth qBW (x4.w.sh qBW - x4.bwh) = { x4 with bwh := 0 }.w := w_bw_rewind x4
  rw [e5] at s5
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · have e : ({ x4 with bwh := 0 } : TSt) = { x with ns := (mism kb epb bwb x.lb 0 x.a).toNat } := by
      rw [hx4, hx3, hm3, hx2, hx1]
      cases x
      simp only at hs hj hbwh ⊢
      subst hs hj hbwh
      simp only [Bool.false_or]
    rw [e]
  · rw [hx4, hx3, hx2, hx1]
    show 18 * (x.lb - 1) + 3 + 1 + (18 * x.a + 3 + 1 + (x.a * (selStepCost x.lb + 4) + 1 + 1 + (3 * (x.lb - 1 - x.a) +
      1 + 1 + (5 * (2 * (0 + x.a)) + 1)))) ≤ selTCost x.lb x.a
    unfold selTCost; omega

end NearCubicWires.WireExponent3_5.FinalPass.Filt
