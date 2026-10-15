import Proof.Wire_3_5.FinalPassMajRef
import Proof.Wire_3_5.FinalPassListEvalMainI
import Proof.Wire_3_5.FinalPassLiftR

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Maj
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ListEval

abbrev MProg := WM 3 26

scoped notation "sPT" => (0 : Fin 4)
scoped notation "sT5" => (1 : Fin 4)
scoped notation "sSS" => (2 : Fin 4)
scoped notation "sFT" => (3 : Fin 4)
scoped notation "mC" => (3 : Fin 26)
scoped notation "mA" => (15 : Fin 26)
scoped notation "mV" => (16 : Fin 26)
scoped notation "mS" => (17 : Fin 26)
scoped notation "mR" => (18 : Fin 26)
scoped notation "mMC" => (19 : Fin 26)
scoped notation "mFP" => (20 : Fin 26)
scoped notation "mTP" => (21 : Fin 26)
scoped notation "mSP" => (22 : Fin 26)
scoped notation "mT" => (23 : Fin 26)
scoped notation "mF" => (24 : Fin 26)
scoped notation "mT2" => (25 : Fin 26)

/-- The phase record of the majority machine. -/
structure MSt where
  pt : List Bool
  t5 : List Bool
  t5h : ℕ
  ss : List Bool
  ssh : ℕ
  ft : List Bool
  fth : ℕ
  c : ℕ
  a : ℕ
  v : ℕ
  s : ℕ
  r : ℕ
  mc : ℕ
  tt : ℕ
  f : ℕ
  t2 : ℕ
  cell : Bool

/-- The word state of a phase record. -/
def MSt.w (x : MSt) : WState 3 26 :=
  ⟨![0, x.t5h, x.ssh, x.fth], ![x.pt, x.t5, x.ss, x.ft],
   ![0, 0, 0, x.c, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x.a, x.v, x.s, x.r, x.mc, x.fth, x.t5h, x.ssh, x.tt, x.f, x.t2],
   x.cell⟩

/-- Close an equality of word states against phase records. -/
syntax "mst_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| mst_eq) => `(tactic| mst_eq [])
  | `(tactic| mst_eq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [MSt.w, $ts,*]; done) | (simp [MSt.w, $ts,*] <;> omega))
        | rfl
        | (simp [MSt.w, $ts,*]; done)))

variable (cap : ℕ)

/-! ## Single updates -/

theorem m_t5_fwd (x : MSt) : (x.w.seth sT5 (x.w.sh sT5 + 1)).setv mTP (x.w.val mTP + 1) = { x with t5h := x.t5h + 1 }.w := by
  mst_eq
theorem m_ft_fwd (x : MSt) : (x.w.seth sFT (x.w.sh sFT + 1)).setv mFP (x.w.val mFP + 1) = { x with fth := x.fth + 1 }.w := by
  mst_eq
theorem m_ss_fwd (x : MSt) : (x.w.seth sSS (x.w.sh sSS + 1)).setv mSP (x.w.val mSP + 1) = { x with ssh := x.ssh + 1 }.w := by
  mst_eq
theorem m_t5_rew (x : MSt) : (x.w.setv mTP 0).seth sT5 (x.w.sh sT5 - x.t5h) = { x with t5h := 0 }.w := by
  mst_eq
theorem m_ft_rew (x : MSt) : (x.w.setv mFP 0).seth sFT (x.w.sh sFT - x.fth) = { x with fth := 0 }.w := by
  mst_eq
theorem m_ss_rew (x : MSt) : (x.w.setv mSP 0).seth sSS (x.w.sh sSS - x.ssh) = { x with ssh := 0 }.w := by
  mst_eq
theorem m_t5_wr (x : MSt) (l : List Bool) : x.w.sets sT5 l = { x with t5 := l }.w := by mst_eq
theorem m_ss_wr (x : MSt) (l : List Bool) : x.w.sets sSS l = { x with ss := l }.w := by mst_eq
theorem m_a (x : MSt) (n : ℕ) : x.w.setv mA n = { x with a := n }.w := by mst_eq
theorem m_v (x : MSt) (n : ℕ) : x.w.setv mV n = { x with v := n }.w := by mst_eq
theorem m_s (x : MSt) (n : ℕ) : x.w.setv mS n = { x with s := n }.w := by mst_eq
theorem m_r (x : MSt) (n : ℕ) : x.w.setv mR n = { x with r := n }.w := by mst_eq
theorem m_mc (x : MSt) (n : ℕ) : x.w.setv mMC n = { x with mc := n }.w := by mst_eq
theorem m_tt (x : MSt) (n : ℕ) : x.w.setv mT n = { x with tt := n }.w := by mst_eq
theorem m_f (x : MSt) (n : ℕ) : x.w.setv mF n = { x with f := n }.w := by mst_eq
theorem m_t2 (x : MSt) (n : ℕ) : x.w.setv mT2 n = { x with t2 := n }.w := by mst_eq
theorem m_c (x : MSt) (n : ℕ) : x.w.setv mC n = { x with c := n }.w := by mst_eq

theorem wbit_t5 (x : MSt) : wbit x.w sT5 = readTapeBit x.t5 x.t5h := rfl
theorem wbit_ft (x : MSt) : wbit x.w sFT = readTapeBit x.ft x.fth := rfl
theorem wbit_ss (x : MSt) : wbit x.w sSS = readTapeBit x.ss x.ssh := rfl

/-- Forward on the template, counted. -/
def fwdT5 : MProg := WM.fwdC sT5 mTP
/-- Forward on the flat table, counted. -/
def fwdFT : MProg := WM.fwdC sFT mFP

theorem fwdT5_spec (x : MSt) (h : x.t5h < cap) : WExec cap fwdT5 x.w { x with t5h := x.t5h + 1 }.w 5 := by
  have s := wfwdC_spec cap sT5 mTP x.w h
  rwa [m_t5_fwd] at s

theorem fwdFT_spec (x : MSt) (h : x.fth < cap) : WExec cap fwdFT x.w { x with fth := x.fth + 1 }.w 5 := by
  have s := wfwdC_spec cap sFT mFP x.w h
  rwa [m_ft_fwd] at s

/-! ## Skipping a unary word on the template -/

/-- Skip `1^n 0` on the template. -/
def skipU : MProg := .seq (.whs sT5 fwdT5) fwdT5

theorem skipLoop_spec (pre post : List Bool) : ∀ (k n : ℕ) (x : MSt), x.t5 = pre ++ List.replicate n true ++ false :: post →
    x.t5h = pre.length + (n - k) → k ≤ n → pre.length + n < cap →
    WExec cap (.whs sT5 fwdT5) x.w { x with t5h := pre.length + n }.w (7 * k + 1)
  | 0, n, x, ht, hh, _, _ => by
    have hb : wbit x.w sT5 = false := by
      rw [wbit_t5, ht, hh, Nat.sub_zero]
      have := readTapeBit_mid (pre ++ List.replicate n true) post false
      simpa using this
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    rw [← Nat.sub_zero n, ← hh]
  | k + 1, n, x, ht, hh, hk, hc => by
    have hb : wbit x.w sT5 = true := by
      rw [wbit_t5, ht, hh]
      unfold readTapeBit
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), List.getD_append _ _ _ _ (by simp; omega)]
      have h0 : 0 < n := by omega
      simp [h0]
    have s1 := fwdT5_spec cap x (by omega)
    have s2 := skipLoop_spec pre post k n { x with t5h := x.t5h + 1 } ht (by simp only; omega) (by omega) hc
    refine WExec.cast cap (WExec.whsT hb s1 s2) ?_ (by omega)
    rfl

theorem skipU_spec (pre post : List Bool) (n : ℕ) (x : MSt) (ht : x.t5 = pre ++ List.replicate n true ++ false :: post)
    (hh : x.t5h = pre.length) (hc : pre.length + n + 1 < cap) :
    WExec cap skipU x.w { x with t5h := pre.length + n + 1 }.w (7 * n + 7) := by
  have s1 := skipLoop_spec cap pre post n n x ht (by rw [hh]; simp) (le_refl _) (by omega)
  have s2 := fwdT5_spec cap { x with t5h := pre.length + n } (by simp only; omega)
  exact WExec.cast cap (WExec.seq s1 s2) rfl (by omega)

/-! ## Copying a framed row over the template's row -/

/-- One bit: the marker, the bit written on the template, both heads on. -/
def bitStep : MProg := .seq fwdFT (.seq (.ifs sFT (.wr sT5 true) (.wr sT5 false)) (.seq fwdFT fwdT5))

/-- The bits of a framed row, until the frame's end. -/
def bitLoop : MProg := .whs sFT bitStep

theorem writeTapeBit_mid'' (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [writeTapeBit, ih]

theorem bitLoop_spec (postF post : List Bool) : ∀ (bs old preF pre : List Bool) (x : MSt),
    x.ft = preF ++ frameP bs ++ false :: postF → x.fth = preF.length → x.t5 = pre ++ old ++ post →
    x.t5h = pre.length → old.length = bs.length → preF.length + 2 * bs.length < cap → pre.length + bs.length < cap →
    WExec cap bitLoop x.w
      { x with t5 := pre ++ bs ++ post, t5h := pre.length + bs.length, fth := preF.length + 2 * bs.length }.w
      (22 * bs.length + 1)
  | [], old, preF, pre, x, hf, hfh, ht, hth, hl, _, _ => by
    have hb : wbit x.w sFT = false := by
      rw [wbit_ft, hf, hfh]
      simpa [frameP] using readTapeBit_mid preF postF false
    have ho : old = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst ho
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    cases x
    simp only at hf hfh ht hth ⊢
    subst hfh hth ht
    simp
  | b :: bs, old, preF, pre, x, hf, hfh, ht, hth, hl, hc1, hc2 => by
    obtain ⟨o, old', rfl⟩ : ∃ o old', old = o :: old' := by
      cases old with
      | nil => simp at hl
      | cons o old' => exact ⟨o, old', rfl⟩
    simp only [List.length_cons] at hl hc1 hc2
    have hf' : x.ft = preF ++ true :: b :: (frameP bs ++ false :: postF) := by
      rw [hf]; simp [frameP]
    have hb0 : wbit x.w sFT = true := by rw [wbit_ft, hf', hfh]; exact readTapeBit_mid preF _ true
    have s1 := fwdFT_spec cap x (by omega)
    have hb1 : wbit ({ x with fth := x.fth + 1 } : MSt).w sFT = b := by
      show readTapeBit x.ft (x.fth + 1) = b
      rw [hf', hfh]
      have := readTapeBit_mid (preF ++ [true]) (frameP bs ++ false :: postF) b
      simpa using this
    have hw : writeTapeBit x.t5 x.t5h b = pre ++ b :: (old' ++ post) := by
      rw [ht, hth, List.append_assoc, List.cons_append]
      exact writeTapeBit_mid'' pre (old' ++ post) o b
    have s2 : WExec cap (.ifs sFT (.wr sT5 true) (.wr sT5 false)) ({ x with fth := x.fth + 1 } : MSt).w
        ({ x with fth := x.fth + 1, t5 := pre ++ b :: (old' ++ post) } : MSt).w 2 := by
      cases b
      · have h := WExec.wr (cap := cap) sT5 false ({ x with fth := x.fth + 1 } : MSt).w
        rw [show (({ x with fth := x.fth + 1 } : MSt).w).st sT5 = x.t5 from rfl,
          show (({ x with fth := x.fth + 1 } : MSt).w).sh sT5 = x.t5h from rfl, hw, m_t5_wr] at h
        exact WExec.ifsF hb1 h
      · have h := WExec.wr (cap := cap) sT5 true ({ x with fth := x.fth + 1 } : MSt).w
        rw [show (({ x with fth := x.fth + 1 } : MSt).w).st sT5 = x.t5 from rfl,
          show (({ x with fth := x.fth + 1 } : MSt).w).sh sT5 = x.t5h from rfl, hw, m_t5_wr] at h
        exact WExec.ifsT hb1 h
    have s3 := fwdFT_spec cap ({ x with fth := x.fth + 1, t5 := pre ++ b :: (old' ++ post) } : MSt) (by simp only; omega)
    have s4 := fwdT5_spec cap ({ x with fth := x.fth + 1 + 1, t5 := pre ++ b :: (old' ++ post) } : MSt)
      (by simp only; omega)
    have hbody : WExec cap bitStep x.w
        ({ x with fth := x.fth + 1 + 1, t5 := pre ++ b :: (old' ++ post), t5h := x.t5h + 1 } : MSt).w 20 :=
      WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) rfl (by omega)
    have ih := bitLoop_spec postF post bs old' (preF ++ [true, b]) (pre ++ [b])
      ({ x with fth := x.fth + 1 + 1, t5 := pre ++ b :: (old' ++ post), t5h := x.t5h + 1 } : MSt)
      (by show x.ft = _; rw [hf]; simp [frameP]) (by show x.fth + 1 + 1 = _; rw [hfh]; simp)
      (by show pre ++ b :: (old' ++ post) = _; simp) (by show x.t5h + 1 = _; rw [hth]; simp) (by omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    refine WExec.cast cap (WExec.whsT hb0 hbody ih) ?_ (by simp only [List.length_cons]; omega)
    cases x
    simp only at hfh hth ⊢
    congr 1
    simp
    omega

/-! ## One record -/

/-- One record of the template: its marker, the two unary words, the row copied from the framed row, the frame's end. -/
def recCopy : MProg := .seq fwdT5 (.seq skipU (.seq skipU (.seq bitLoop fwdFT)))

def recCost (a b L : ℕ) : ℕ := 5 + 1 + ((7 * a + 7) + 1 + ((7 * b + 7) + 1 + ((22 * L + 1) + 1 + 5)))

theorem recCopy_spec (preF postF pre post old new : List Bool) (a b : ℕ) (x : MSt)
    (hf : x.ft = preF ++ frameP new ++ false :: postF) (hfh : x.fth = preF.length)
    (ht : x.t5 = pre ++ (true :: (unary a ++ unary b ++ old)) ++ post) (hth : x.t5h = pre.length)
    (hl : old.length = new.length) (hc1 : preF.length + 2 * new.length + 1 < cap)
    (hc2 : pre.length + a + b + new.length + 3 < cap) :
    WExec cap recCopy x.w
      { x with t5 := pre ++ (true :: (unary a ++ unary b ++ new)) ++ post,
               t5h := pre.length + (1 + (a + 1) + (b + 1) + new.length),
               fth := preF.length + (2 * new.length + 1) }.w
      (recCost a b new.length) := by
  have s1 := fwdT5_spec cap x (by omega)
  have s2 := skipU_spec cap (pre ++ [true]) (List.replicate b true ++ false :: (old ++ post)) a
    ({ x with t5h := x.t5h + 1 } : MSt) (by show x.t5 = _; rw [ht]; simp [unary])
    (by show x.t5h + 1 = _; rw [hth]; simp) (by simp; omega)
  have s3 := skipU_spec cap (pre ++ [true] ++ List.replicate a true ++ [false]) (old ++ post) b
    ({ x with t5h := (pre ++ [true]).length + a + 1 } : MSt) (by show x.t5 = _; rw [ht]; simp [unary])
    (by show (pre ++ [true]).length + a + 1 = _; simp; omega) (by simp; omega)
  obtain ⟨P6, hP6⟩ : ∃ l : List Bool, l = pre ++ [true] ++ List.replicate a true ++ [false] ++
      List.replicate b true ++ [false] := ⟨_, rfl⟩
  have s4 := bitLoop_spec cap postF post new old preF P6
    ({ x with t5h := (pre ++ [true] ++ List.replicate a true ++ [false]).length + b + 1 } : MSt) hf hfh
    (by show x.t5 = _; rw [ht, hP6]; simp [unary]) (by rw [hP6]; simp; omega) hl (by omega) (by rw [hP6]; simp; omega)
  have s5 := fwdFT_spec cap
    ({ x with t5h := P6.length + new.length, t5 := P6 ++ new ++ post, fth := preF.length + 2 * new.length } : MSt)
    (by simp only; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (by unfold recCost; omega)
  subst hP6
  cases x
  simp only at hth ⊢
  congr 1
  simp [unary]
  omega

/-! ## The records of a table -/

/-- The records, while the template reads a record marker. -/
def recLoop : MProg := .whs sT5 recCopy

/-- The records' cost. -/
def recLoopCost (J : ℕ) (W : ℕ → ℕ) (L : ℕ) (js : List ℕ) : ℕ :=
  (js.map fun j => recCost (pow (topW J W j)) (topW J W j) L + 2).sum + 1

theorem record_len (J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (j : ℕ) :
    (record J W row j).length = 1 + (pow (topW J W j) + 1) + (topW J W j + 1) + (row j).length := by
  simp [record, unary]; omega

theorem recLoop_spec (J : ℕ) (W : ℕ → ℕ) (L : ℕ) (rowOld rowNew : ℕ → List Bool) (post postF : List Bool) :
    ∀ (js : List ℕ) (pre preF : List Bool) (x : MSt),
    (∀ j ∈ js, (rowOld j).length = L) → (∀ j ∈ js, (rowNew j).length = L) →
    x.t5 = pre ++ js.flatMap (record J W rowOld) ++ false :: post → x.t5h = pre.length →
    x.ft = preF ++ js.flatMap (fun j => frame (rowNew j)) ++ postF → x.fth = preF.length →
    (pre ++ js.flatMap (record J W rowNew)).length < cap →
    (preF ++ js.flatMap (fun j => frame (rowNew j))).length < cap →
    WExec cap recLoop x.w
      { x with t5 := pre ++ js.flatMap (record J W rowNew) ++ false :: post,
               t5h := (pre ++ js.flatMap (record J W rowNew)).length,
               fth := (preF ++ js.flatMap (fun j => frame (rowNew j))).length }.w
      (recLoopCost J W L js)
  | [], pre, preF, x, _, _, ht, hth, _, hfh, _, _ => by
    have hb : wbit x.w sT5 = false := by rw [wbit_t5, ht, hth]; simpa using readTapeBit_mid pre post false
    refine WExec.cast cap (WExec.whsF hb) ?_ (by simp [recLoopCost])
    cases x
    simp only at ht hth hfh ⊢
    subst ht hth hfh
    simp
  | j :: js, pre, preF, x, hO, hN, ht, hth, hf, hfh, hcT, hcF => by
    have hOj := hO j List.mem_cons_self
    have hNj := hN j List.mem_cons_self
    have hb : wbit x.w sT5 = true := by
      rw [wbit_t5, ht, hth]
      have := readTapeBit_mid pre ((unary (pow (topW J W j)) ++ unary (topW J W j) ++ rowOld j) ++
        js.flatMap (record J W rowOld) ++ false :: post) true
      simpa [record] using this
    have hlenT : (pre ++ (j :: js).flatMap (record J W rowNew)).length =
        pre.length + (1 + (pow (topW J W j) + 1) + (topW J W j + 1) + L) +
          (js.flatMap (record J W rowNew)).length := by
      simp only [List.flatMap_cons, List.length_append, record_len, hNj]; omega
    have hlenF : (preF ++ (j :: js).flatMap (fun j => frame (rowNew j))).length =
        preF.length + (2 * L + 1) + (js.flatMap (fun j => frame (rowNew j))).length := by
      simp only [List.flatMap_cons, List.length_append, frame_eq_frameP, frameP, List.length_flatMap]
      simp; omega
    have s1 := recCopy_spec cap preF (js.flatMap (fun j => frame (rowNew j)) ++ postF) pre
      (js.flatMap (record J W rowOld) ++ false :: post) (rowOld j) (rowNew j) (pow (topW J W j)) (topW J W j) x
      (by rw [hf]; simp [frame_eq_frameP]) hfh (by rw [ht]; simp [record]) hth (by rw [hOj, hNj])
      (by rw [hNj]; omega) (by rw [hNj]; omega)
    have ih := recLoop_spec J W L rowOld rowNew post postF js (pre ++ record J W rowNew j)
      (preF ++ frame (rowNew j))
      { x with t5 := pre ++ (true :: (unary (pow (topW J W j)) ++ unary (topW J W j) ++ rowNew j)) ++
                 (js.flatMap (record J W rowOld) ++ false :: post),
               t5h := pre.length + (1 + (pow (topW J W j) + 1) + (topW J W j + 1) + (rowNew j).length),
               fth := preF.length + (2 * (rowNew j).length + 1) }
      (fun j' hj' => hO j' (List.mem_cons_of_mem _ hj')) (fun j' hj' => hN j' (List.mem_cons_of_mem _ hj'))
      (by simp [record]) (by simp only [record_len, List.length_append])
      (by show x.ft = _; rw [hf]; simp) (by simp [frame_eq_frameP, frameP, hNj]; omega)
      (by simp only [List.flatMap_cons, List.append_assoc] at hcT ⊢; simpa using hcT)
      (by simp only [List.flatMap_cons, List.append_assoc] at hcF ⊢; simpa using hcF)
    refine WExec.cast cap (WExec.whsT hb s1 ih) ?_ (by simp [recLoopCost, hNj]; omega)
    cases x
    congr 1
    simp

/-! ## A visit's rows into the template -/

/-- **The copy of a visit**: its marker, the template's `M`, the records, the template rewound. -/
def copyRows : MProg := .seq fwdFT (.seq skipU (.seq recLoop (WM.rewind sT5 mTP)))

def copyCost (M J : ℕ) (W : ℕ → ℕ) (L T : ℕ) : ℕ :=
  5 + 1 + ((7 * M + 7) + 1 + (recLoopCost J W L (levels J) + 1 + (5 * T + 1)))

/-- **The template holds the visit's rows**: from `levelWord M J W rowOld` (head at `0`) and the flat table at a visit
word `true :: …frame (rowNew j)…`, the template becomes `levelWord M J W rowNew` (head at `0`) and the table's head
passes the visit word. -/
theorem copyRows_spec (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) (rowOld rowNew : ℕ → List Bool) (preF postF : List Bool)
    (x : MSt) (hO : ∀ j ≤ J, (rowOld j).length = L) (hN : ∀ j ≤ J, (rowNew j).length = L)
    (ht : x.t5 = levelWord M J W rowOld) (hth : x.t5h = 0)
    (hf : x.ft = preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j))) ++ postF) (hfh : x.fth = preF.length)
    (hcT : (levelWord M J W rowNew).length < cap)
    (hcF : (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length < cap) :
    WExec cap copyRows x.w
      { x with t5 := levelWord M J W rowNew,
               fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length }.w
      (copyCost M J W L (levelWord M J W rowNew).length) := by
  have hmem : ∀ j ∈ levels J, j ≤ J := by intro j hj; simp [levels] at hj; omega
  have hlen : (levelWord M J W rowNew).length = (levelWord M J W rowOld).length := by
    simp only [levelWord, List.length_append, List.length_flatMap, record_len]
    congr 2
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [hO j (hmem j hj), hN j (hmem j hj)]
  have s1 := fwdFT_spec cap x (by simp at hcF; omega)
  have s2 := skipU_spec cap [] ((levels J).flatMap (record J W rowOld) ++ [false]) M { x with fth := x.fth + 1 }
    (by show x.t5 = _; rw [ht]; simp [levelWord, unary]) (by show x.t5h = _; rw [hth]; rfl)
    (by simp [levelWord, unary] at hcT ⊢; omega)
  have s3 := recLoop_spec cap J W L rowOld rowNew [] postF (levels J) (unary M) (preF ++ [true])
    { x with fth := x.fth + 1, t5h := ([] : List Bool).length + M + 1 }
    (fun j hj => hO j (hmem j hj)) (fun j hj => hN j (hmem j hj))
    (by show x.t5 = _; rw [ht]; simp [levelWord]) (by simp [unary])
    (by show x.ft = _; rw [hf]; simp) (by show x.fth + 1 = _; rw [hfh]; simp)
    (by simp [levelWord] at hcT ⊢; omega) (by simpa using hcF)
  have s4 := wrewind_spec cap sT5 mTP (unary M ++ (levels J).flatMap (record J W rowNew)).length
    ({ x with fth := (preF ++ [true] ++ (levels J).flatMap (fun j => frame (rowNew j))).length,
              t5 := unary M ++ (levels J).flatMap (record J W rowNew) ++ [false],
              t5h := (unary M ++ (levels J).flatMap (record J W rowNew)).length } : MSt).w rfl
    (by show (unary M ++ (levels J).flatMap (record J W rowNew)).length ≤ cap; simp [levelWord] at hcT ⊢; omega)
  rw [m_t5_rew] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · cases x
    simp only at hth ⊢
    congr 1
    all_goals simp [levelWord, hth]
  · unfold copyCost
    have : (unary M ++ (levels J).flatMap (record J W rowNew)).length ≤ (levelWord M J W rowNew).length := by
      simp [levelWord]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.Maj
