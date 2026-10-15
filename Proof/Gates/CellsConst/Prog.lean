import Proof.Gates.Cells.ConstSpec
import Proof.Gates.CounterMachine.CellTablesCst2
import Proof.Gates.Cells.Forms

set_option autoImplicit false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-! ## Scratch variables (all in `50 … 69`) -/

def kT1 : Fin VV := ⟨50, by decide⟩
def kT2 : Fin VV := ⟨51, by decide⟩
def kI : Fin VV := ⟨52, by decide⟩
def kKB : Fin VV := ⟨53, by decide⟩
def kKL : Fin VV := ⟨54, by decide⟩
def kKW : Fin VV := ⟨55, by decide⟩
def kVW : Fin VV := ⟨56, by decide⟩
def kDB : Fin VV := ⟨57, by decide⟩
def kS : Fin VV := ⟨58, by decide⟩
def kX : Fin VV := ⟨59, by decide⟩
def kAc : Fin VV := ⟨60, by decide⟩
def kE : Fin VV := ⟨61, by decide⟩
def kP : Fin VV := ⟨62, by decide⟩
def kQ : Fin VV := ⟨63, by decide⟩
def kJ : Fin VV := ⟨64, by decide⟩
def kU : Fin VV := ⟨65, by decide⟩
def kN : Fin VV := ⟨66, by decide⟩
def kF : Fin VV := ⟨67, by decide⟩
def kPos : Fin VV := ⟨68, by decide⟩

/-! ## The constants `vZ v1 v2` -/

theorem cstS {a : DS VV MM} (h : Cst a) (x : Fin VV) (v : ℕ) (hx : 3 ≤ x.val) : Cst (a.set x v) :=
  ⟨by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at hx; simp [vZ] at hx)]; exact h.z,
   by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at hx; simp [v1] at hx)]; exact h.one,
   by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at hx; simp [v2] at hx)]; exact h.two⟩

theorem cstF {a b : DS VV MM} {T : List (Fin VV)} (h : Cst a) (hf : Fr a b T) (hT : ∀ y ∈ T, 3 ≤ y.val) :
    Cst b :=
  ⟨by rw [hf vZ (fun h' => by have := hT _ h'; simp [vZ] at this)]; exact h.z,
   by rw [hf v1 (fun h' => by have := hT _ h'; simp [v1] at this)]; exact h.one,
   by rw [hf v2 (fun h' => by have := hT _ h'; simp [v2] at this)]; exact h.two⟩

/-! ## Agreement outside the workspace -/

/-- Everything but the variables `T` and the cursor of `sN` agrees. -/
structure AgN (a b : DS VV MM) (T : List (Fin VV)) : Prop where
  ram : b.ram = a.ram
  rc : ∀ m, m ≠ sN → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

/-! ## Reading a list stored at an offset -/

theorem getD_of_drop {L X R : List ℕ} {b : ℕ} (h : L.drop b = X ++ R) (i : ℕ) (hi : i < X.length) :
    L.getD (b + i) 0 = X.getD i 0 := by
  have : L.getD (b + i) 0 = (L.drop b).getD i 0 := by simp [List.getD_eq_getElem?_getD]
  rw [this, h, List.getD_append _ _ _ _ hi]

theorem len_of_drop {L X R : List ℕ} {b : ℕ} (h : L.drop b = X ++ R) (hX : 0 < X.length) :
    b + X.length ≤ L.length := by
  have := congrArg List.length h
  simp at this; omega

theorem le_of_drop {L X R : List ℕ} {b : ℕ} (h : L.drop b = X ++ R) (hb : b ≤ L.length) :
    b + X.length ≤ L.length := by
  have := congrArg List.length h
  simp at this; omega

/-! ## One assignment, abstracted (keeps the states opaque) -/

theorem Hs.setx {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {x : Fin VV} {v : ℕ}
    (h : Hs C s a t (· = a.set x v)) : Hs C s a t (fun b => b.env x = v ∧ b.sh = a.sh ∧ Fr a b [x]) :=
  Hs.mono h le_rfl (by rintro b rfl; exact ⟨by simp, rfl, Fr.set a v (by simp)⟩)

/-- Accumulate a frame and the non-variable part. -/
theorem frA {a b d : DS VV MM} {T T' : List (Fin VV)} (F : Fr a b T) (f : Fr b d T') (hT : ∀ y ∈ T', y ∈ T) :
    Fr a d T := Fr.trans F (Fr.weaken f hT)

/-! ## Small arithmetic -/

theorem min_mul_cap (x c h : ℕ) : min (min x c * h) c = min (x * h) c := by
  rcases le_total x c with hx | hx
  · rw [min_eq_left hx]
  · rw [min_eq_right hx]
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · simp [h0]
    · have h1 : c ≤ c * h := Nat.le_mul_of_pos_right c hpos
      have h2 : c ≤ x * h := hx.trans (Nat.le_mul_of_pos_right x hpos)
      rw [min_eq_right h1, min_eq_right h2]

theorem lt_pow_of_le {x W : ℕ} (h : x + 1 ≤ W) : x < 2 ^ W :=
  lt_of_lt_of_le (Nat.lt_two_pow_self (n := x)) (Nat.pow_le_pow_right (by norm_num) (by omega))

end NearCubicGates.Close.CellsConst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-! ## `keyBits`, `2^{keyBits}` -/

def keys1 : St VV MM :=
  .seq (.op (.copy kT1 wP)) (.seq (.op (.add kT1 gJ)) (.seq (.op (.inc kT1)) (.seq (.op (.inc kT1))
  (.seq (.op (.inc kT1)) (.seq (CellTablesProg.sizeP kT1 kKB) (CellTablesProg.pow2P vKB kI kKB))))))

theorem keys1_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (P J : ℕ) (hP : a.env wP = P) (hJ : a.env gJ = J)
    (hW : P + J + 4 ≤ C.Wd) :
    Hs C keys1 a (10 * (P + J) + 60) (fun e => e.env vKB = 2 ^ Nat.size (P + J + 3) ∧
      e.env kKB = Nat.size (P + J + 3) ∧ e.sh = a.sh ∧ Fr a e [kT1, kKB, vKB, kI]) := by
  have hlt : P + J + 3 < 2 ^ C.Wd := lt_pow_of_le (by omega)
  have hsz : Nat.size (P + J + 3) ≤ P + J + 3 := Nat.size_le.mpr Nat.lt_two_pow_self
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kT1 wP a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 [kT1, kKB, vKB, kI] := Fr.weaken f1 (by decide)
  rw [hP] at e1
  refine Hs.then (Hs.setx (hs_add C kT1 gJ b1 (by decide) (by rw [e1, F1 gJ (by decide), hJ]; omega)))
    (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  rw [e1, F1 gJ (by decide), hJ] at e2
  refine Hs.then (Hs.setx (hs_inc C kT1 b2 (by rw [e2]; omega))) (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  rw [e2] at e3
  refine Hs.then (Hs.setx (hs_inc C kT1 b3 (by rw [e3]; omega))) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  rw [e3] at e4
  refine Hs.then (Hs.setx (hs_inc C kT1 b4 (by rw [e4]; omega))) (fun b5 ⟨e5, s5, f5⟩ n5 hn5 => ?_)
  have F5 := frA F4 f5 (by decide)
  rw [e4] at e5
  refine Hs.then (CellTablesProg.sizeP_spec C kT1 kKB (by decide) (by decide) (by decide) b5 (cstF hc F5 (by decide))
    (P + J + 3) (by rw [e5]) (lt_of_le_of_lt hsz hlt)) (fun b6 ⟨v6, _, s6, f6⟩ n6 hn6 => ?_)
  have F6 := frA F5 f6 (by decide)
  refine Hs.last (CellTablesProg.pow2P_spec C vKB kI kKB (by decide) (by decide) (by decide) (by decide) b6
    (cstF hc F6 (by decide)) _ v6 (by omega)) (fun b7 ⟨v7, s7, f7⟩ n7 hn7 => ?_)
  refine ⟨⟨v7, by rw [f7 kKB (by decide)]; exact v6, by rw [s7, s6, s5, s4, s3, s2, s1], frA F6 f7 (by decide)⟩,
    by omega⟩

/-! ## `keyLen`, `keyW`, `2^{keyW}`, `2^{keyW − keyBits}` -/

def keys2 : St VV MM :=
  .seq (.op (.copy kT1 gJ)) (.seq (.op (.inc kT1)) (.seq (.op (.mul gRC kT1 kKL)) (.seq (.op (.inc kKL))
  (.seq (.op (.inc kKL)) (.seq (.op (.inc kKL)) (.seq (.op (.mul kKB kKL kKW)) (.seq (CellTablesProg.pow2P p2K kI kKW)
  (.seq (.op (.copy kT1 kKW)) (.seq (.op (.sub kT1 kKB)) (CellTablesProg.pow2P p2KF kI kT1))))))))))

theorem keys2_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (J R KB : ℕ) (hJ : a.env gJ = J) (hR : a.env gRC = R)
    (hKB : a.env kKB = KB) (hW : KB * (R * (J + 1) + 3) + R * (J + 1) + 4 ≤ C.Wd) (hWJ : J + 2 ≤ C.Wd) :
    Hs C keys2 a (10 * (KB * (R * (J + 1) + 3)) + 40) (fun e => e.env p2K = 2 ^ (KB * (R * (J + 1) + 3)) ∧
      e.env p2KF = 2 ^ (KB * (R * (J + 1) + 3) - KB) ∧ e.sh = a.sh ∧
      Fr a e [kT1, kKL, kKW, p2K, kI, p2KF]) := by
  have hm : R * (J + 1) + 3 < 2 ^ C.Wd := lt_pow_of_le (by omega)
  have hJ1 : J + 1 < 2 ^ C.Wd := lt_pow_of_le (by omega)
  obtain ⟨KL, hKL⟩ : ∃ KL, KL = R * (J + 1) + 3 := ⟨_, rfl⟩
  have hkw : KB * KL < 2 ^ C.Wd := lt_pow_of_le (by rw [hKL]; omega)
  have hkw' : KB * KL < C.Wd := by rw [hKL]; omega
  rw [← hKL]
  have hKBle : KB ≤ KB * KL := Nat.le_mul_of_pos_right KB (by omega)
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kT1 gJ a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 [kT1, kKL, kKW, p2K, kI, p2KF] := Fr.weaken f1 (by decide)
  rw [hJ] at e1
  refine Hs.then (Hs.setx (hs_inc C kT1 b1 (by rw [e1]; omega))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  rw [e1] at e2
  refine Hs.then (Hs.setx (hs_mul C gRC kT1 kKL b2 (by decide) (by decide) (by decide)
    (by rw [e2, F2 gRC (by decide), hR]; omega))) (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  rw [e2, F2 gRC (by decide), hR] at e3
  refine Hs.then (Hs.setx (hs_inc C kKL b3 (by rw [e3]; omega))) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  rw [e3] at e4
  refine Hs.then (Hs.setx (hs_inc C kKL b4 (by rw [e4]; omega))) (fun b5 ⟨e5, s5, f5⟩ n5 hn5 => ?_)
  have F5 := frA F4 f5 (by decide)
  rw [e4] at e5
  refine Hs.then (Hs.setx (hs_inc C kKL b5 (by rw [e5]; omega))) (fun b6 ⟨e6, s6, f6⟩ n6 hn6 => ?_)
  have F6 := frA F5 f6 (by decide)
  rw [e5, show R * (J + 1) + 1 + 1 + 1 = KL by omega] at e6
  have b6KB : b6.env kKB = KB := by rw [F6 kKB (by decide), hKB]
  refine Hs.then (Hs.setx (hs_mul C kKB kKL kKW b6 (by decide) (by decide) (by decide)
    (by rw [e6, b6KB]; exact hkw))) (fun b7 ⟨e7, s7, f7⟩ n7 hn7 => ?_)
  have F7 := frA F6 f7 (by decide)
  rw [e6, b6KB] at e7
  refine Hs.then (CellTablesProg.pow2P_spec C p2K kI kKW (by decide) (by decide) (by decide) (by decide) b7
    (cstF hc F7 (by decide)) (KB * KL) e7 (by omega)) (fun b8 ⟨v8, s8, f8⟩ n8 hn8 => ?_)
  have F8 := frA F7 f8 (by decide)
  have b8KW : b8.env kKW = KB * KL := by rw [f8 kKW (by decide), e7]
  have b8KB : b8.env kKB = KB := by rw [F8 kKB (by decide), hKB]
  refine Hs.then (Hs.setx (hs_copy C kT1 kKW b8 (by decide))) (fun b9 ⟨e9, s9, f9⟩ n9 hn9 => ?_)
  have F9 := frA F8 f9 (by decide)
  rw [b8KW] at e9
  refine Hs.then (Hs.setx (hs_sub C kT1 kKB b9 (by decide) (by rw [e9, f9 kKB (by decide), b8KB]; exact hKBle)))
    (fun b10 ⟨e10, s10, f10⟩ n10 hn10 => ?_)
  have F10 := frA F9 f10 (by decide)
  rw [e9, f9 kKB (by decide), b8KB] at e10
  refine Hs.last (CellTablesProg.pow2P_spec C p2KF kI kT1 (by decide) (by decide) (by decide) (by decide) b10
    (cstF hc F10 (by decide)) (KB * KL - KB) e10 (by omega)) (fun b11 ⟨v11, s11, f11⟩ n11 hn11 => ?_)
  refine ⟨⟨by rw [f11 p2K (by decide), f10 p2K (by decide), f9 p2K (by decide)]; exact v8, v11,
    by rw [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1], frA F10 f11 (by decide)⟩, ?_⟩
  have : KB * KL - KB ≤ KB * KL := Nat.sub_le _ _
  omega

/-! ## `(2h_E − 1)^{roleCount·J}` -/

def bnP : St VV MM :=
  .seq (.op (.copy kT1 vHE)) (.seq (.op (.shl kT1)) (.seq (.op (.sub kT1 v1)) (.seq (.op (.mul gRC gJ kE))
  (.seq (.op (.copy vBN v1)) (CellTablesProg.powP vBN kT1 kU kE kT2)))))

theorem bnP_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (H J R : ℕ) (hH : a.env vHE = H) (hJ : a.env gJ = J)
    (hR : a.env gRC = R) (hH1 : 1 ≤ H) (hW2 : 2 * H < 2 ^ C.Wd) (hRJ : R * J < 2 ^ C.Wd)
    (hfit : (2 * H - 1) ^ (R * J) < 2 ^ C.Wd) :
    Hs C bnP a (7 * (R * J) + 20) (fun e => e.env vBN = (2 * H - 1) ^ (R * J) ∧ e.sh = a.sh ∧
      Fr a e [kT1, kE, vBN, kU, kT2]) := by
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kT1 vHE a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 [kT1, kE, vBN, kU, kT2] := Fr.weaken f1 (by decide)
  rw [hH] at e1
  refine Hs.then (Hs.setx (hs_shl C kT1 b1 (by rw [e1]; exact hW2))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  rw [e1] at e2
  have b2one : b2.env v1 = 1 := by rw [F2 v1 (by decide)]; exact hc.one
  refine Hs.then (Hs.setx (hs_sub C kT1 v1 b2 (by decide) (by rw [e2, b2one]; omega)))
    (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  rw [e2, b2one] at e3
  refine Hs.then (Hs.setx (hs_mul C gRC gJ kE b3 (by decide) (by decide) (by decide)
    (by rw [F3 gRC (by decide), F3 gJ (by decide), hR, hJ]; exact hRJ))) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  rw [F3 gRC (by decide), F3 gJ (by decide), hR, hJ] at e4
  refine Hs.then (Hs.setx (hs_copy C vBN v1 b4 (by decide))) (fun b5 ⟨e5, s5, f5⟩ n5 hn5 => ?_)
  have F5 := frA F4 f5 (by decide)
  rw [F4 v1 (by decide), hc.one] at e5
  refine Hs.last (CellTablesProg.powP_spec C vBN kT1 kU kE kT2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b5 (R * J) 1 (2 * H - 1) (by rw [f5 kE (by decide), e4])
    e5 (by rw [f5 kT1 (by decide), f4 kT1 (by decide), e3]) hRJ (by rw [one_mul]; exact hfit))
    (fun b6 ⟨v6, s6, f6⟩ n6 hn6 => ?_)
  refine ⟨⟨by rw [v6, one_mul], by rw [s6, s5, s4, s3, s2, s1], frA F5 f6 (by decide)⟩, by omega⟩

/-! ## `2^{n − |I|}` -/

def ncP : St VV MM := .seq (.op (.copy kT1 gN)) (.seq (.op (.sub kT1 wCo)) (CellTablesProg.pow2P gNC kI kT1))

theorem ncP_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (n w : ℕ) (hn : a.env gN = n) (hw : a.env wCo = w)
    (hwn : w ≤ n) (hW : n < C.Wd) :
    Hs C ncP a (5 * n + 10) (fun e => e.env gNC = 2 ^ (n - w) ∧ e.sh = a.sh ∧ Fr a e [kT1, gNC, kI]) := by
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kT1 gN a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  rw [hn] at e1
  refine Hs.then (Hs.setx (hs_sub C kT1 wCo b1 (by decide) (by rw [e1, f1 wCo (by decide), hw]; exact hwn)))
    (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  rw [e1, f1 wCo (by decide), hw] at e2
  have F2 : Fr a b2 [kT1, gNC, kI] := frA (Fr.weaken f1 (by decide)) f2 (by decide)
  refine Hs.last (CellTablesProg.pow2P_spec C gNC kI kT1 (by decide) (by decide) (by decide) (by decide) b2
    (cstF hc F2 (by decide)) (n - w) e2 (by omega)) (fun b3 ⟨v3, s3, f3⟩ n3 hn3 => ?_)
  refine ⟨⟨v3, by rw [s3, s2, s1], frA F2 f3 (by decide)⟩, by omega⟩

end NearCubicGates.Close.CellsConst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-! ## The sum of the factors -/

def sumF : St VV MM :=
  .seq (.op (.copy kPos gFS)) (.seq (.op (.inc kPos)) (.seq (seekP sN kPos) (.seq (.op (.zero kAc))
  (forS kU wNF (.seq (.op (.rdM sN kX)) (.op (.add kAc kX)))))))

theorem sum_take_step (F : List ℕ) (u : ℕ) (hu : u < F.length) :
    (F.take (u + 1)).sum = (F.take u).sum + F.getD u 0 := by
  rw [List.sum_take_succ _ _ hu, List.getD_eq_getElem _ _ hu]

theorem sum_take_le (F : List ℕ) (u : ℕ) : (F.take u).sum ≤ F.sum := by
  have := List.sum_take_add_sum_drop F u
  omega

theorem sumF_spec (C : Ctx) (a : DS VV MM) (L F R : List ℕ) (g : ℕ) (hN : a.ram sN = L)
    (hrc : a.rc sN ≤ L.length) (hg : a.env gFS = g) (hF : L.drop (g + 1) = F ++ R) (hnf : a.env wNF = F.length)
    (hg1 : g + 1 ≤ L.length) (hLW : L.length < 2 ^ C.Wd) (hS : F.sum < 2 ^ C.Wd) :
    Hs C sumF a (6 * L.length + 7 * F.length + 30) (fun e => e.env kAc = F.sum ∧ e.ram = a.ram ∧
      e.rc sN ≤ L.length ∧ AgN a e [kPos, c0, vJ, kAc, kU, kX]) := by
  have hgF := le_of_drop hF hg1
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kPos gFS a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  rw [hg] at e1
  refine Hs.then (Hs.setx (hs_inc C kPos b1 (by rw [e1]; omega))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  rw [e1] at e2
  have F2 : Fr a b2 [kPos, c0, vJ, kAc, kU, kX] := frA (Fr.weaken f1 (by decide)) f2 (by decide)
  have s2a : b2.sh = a.sh := by rw [s2, s1]
  simp only [DS.sh, Prod.mk.injEq] at s2a
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := s2a
  refine Hs.then (seekP_spec sN kPos (by decide) (by decide) b2 (by rw [e2, q3, hN]; exact hg1)
    (by rw [e2]; omega)) (fun b3 ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ n3 hn3 => ?_)
  have F3 := frA F2 r8 (by decide)
  rw [e2] at r2
  refine Hs.then (Hs.setx (hs_zero C kAc b3)) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  simp only [DS.sh, Prod.mk.injEq] at s4
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := s4
  let I : ℕ → DS VV MM → Prop := fun u e => e.env kAc = (F.take u).sum ∧ e.ram = a.ram ∧
    e.rc = Function.update a.rc sN (g + 1 + u) ∧ e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧
    e.kc = a.kc ∧ Fr a e [kPos, c0, vJ, kAc, kU, kX]
  have h0 : I 0 b4 := ⟨by rw [e4]; simp, by rw [p3, r1, q3], by rw [p4, r2, q4], by rw [p1, r3, q1],
    by rw [p2, r4, q2], by rw [p5, r5, q5], by rw [p6, r6, q6], by rw [p7, r7, q7], F4⟩
  refine Hs.last (forS_spec' (C := C) kU wNF (by decide) _ b4 F.length (by omega) I 3
    (fun u e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2, i3, i4,
      i5, i6, i7, i8, Fr.trans i9 (Fr.set e v (by decide))⟩) h0
    (by rw [F4 wNF (by decide), hnf]) ?_) (fun b5 ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩, _, w5⟩ n5 hn5 => ?_)
  · intro u hu e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ heu hem
    have hrcu : e.rc sN = g + 1 + u := by rw [i3]; simp
    have hlt : e.rc sN < (e.ram sN).length := by rw [hrcu, i2, hN]; omega
    have hrd : (e.ram sN).getD (e.rc sN) 0 = F.getD u 0 := by rw [i2, hN, hrcu]; exact getD_of_drop hF u hu
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdM C sN kX e hlt) (fun f hf => ?_)
    subst hf
    have hst := sum_take_step F u hu
    have hle := sum_take_le F (u + 1)
    refine Hs.mono (Hs.setx (hs_add C kAc kX _ (by decide) (by
      simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, i1, hrd]; omega))) le_rfl ?_
    rintro d ⟨g1, g2, g3⟩
    simp only [DS.sh, DS.adv, DS.set, Prod.mk.injEq] at g2
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := g2
    have dX : ∀ y, y ≠ kAc → d.env y = Function.update e.env kX ((e.ram sN).getD (e.rc sN) 0) y := by
      intro y hy; rw [g3 y (by simp [hy])]; rfl
    refine ⟨⟨?_, by rw [d3, i2], ?_, by rw [d1, i4], by rw [d2, i5], by rw [d5, i6], by rw [d6, i7], by rw [d7, i8],
      ?_⟩, ?_, ?_⟩
    · rw [g1]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, i1, hrd, hst]
    · rw [d4, i3]; funext m; by_cases hm : m = sN
      · subst hm; simp; omega
      · simp [Function.update_of_ne hm]
    · intro y hy
      have hyA : y ≠ kAc := fun h => hy (by rw [h]; decide)
      have hyX : y ≠ kX := fun h => hy (by rw [h]; decide)
      rw [dX y hyA, Function.update_of_ne hyX]; exact i9 y hy
    · rw [dX kU (by decide), Function.update_of_ne (by decide)]; exact heu
    · rw [dX wNF (by decide), Function.update_of_ne (by decide)]; exact hem
  · have hq4 : b2.rc sN = a.rc sN := by rw [q4]
    refine ⟨⟨by rw [i1, List.take_of_length_le le_rfl], i2, ?_, ?_⟩, by omega⟩
    · rw [i3]; simp; omega
    · exact ⟨i2, fun m hm => by rw [i3, Function.update_of_ne hm], i4, i5, i6, i7, i8, i9⟩

/-! ## `deltaBound` and its size -/

def vwA : St VV MM :=
  .seq (.op (.add kAc vM1)) (.seq (.op (.add kAc vA)) (.seq (.op (.inc kAc)) (.seq (.op (.shl kAc))
  (.seq (.op (.copy kT1 wW)) (.seq (.op (.inc kT1)) (.seq (.op (.mul kAc kT1 kDB)) (CellTablesProg.sizeP kDB kS)))))))

theorem vwA_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (Sf M1 A W : ℕ) (hS : a.env kAc = Sf)
    (hM : a.env vM1 = M1) (hA : a.env vA = A) (hWv : a.env wW = W)
    (hDB : 2 * (M1 + A + Sf + 1) * (W + 1) < 2 ^ C.Wd) :
    Hs C vwA a (5 * Nat.size (2 * (M1 + A + Sf + 1) * (W + 1)) + 20) (fun e =>
      e.env kS = Nat.size (2 * (M1 + A + Sf + 1) * (W + 1)) ∧ e.sh = a.sh ∧ Fr a e [kAc, kT1, kDB, kS]) := by
  obtain ⟨X, hX⟩ : ∃ X, X = M1 + A + Sf + 1 := ⟨_, rfl⟩
  rw [← hX] at hDB ⊢
  have h1 : 2 * X ≤ 2 * X * (W + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : W + 1 ≤ 2 * X * (W + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hsz : Nat.size (2 * X * (W + 1)) ≤ 2 * X * (W + 1) := Nat.size_le.mpr Nat.lt_two_pow_self
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_add C kAc vM1 a (by decide) (by rw [hS, hM]; omega)))
    (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 [kAc, kT1, kDB, kS] := Fr.weaken f1 (by decide)
  rw [hS, hM] at e1
  refine Hs.then (Hs.setx (hs_add C kAc vA b1 (by decide) (by rw [e1, F1 vA (by decide), hA]; omega)))
    (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  rw [e1, F1 vA (by decide), hA] at e2
  refine Hs.then (Hs.setx (hs_inc C kAc b2 (by rw [e2]; omega))) (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  rw [e2, show Sf + M1 + A + 1 = X by omega] at e3
  refine Hs.then (Hs.setx (hs_shl C kAc b3 (by rw [e3]; omega))) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  rw [e3] at e4
  refine Hs.then (Hs.setx (hs_copy C kT1 wW b4 (by decide))) (fun b5 ⟨e5, s5, f5⟩ n5 hn5 => ?_)
  have F5 := frA F4 f5 (by decide)
  rw [F4 wW (by decide), hWv] at e5
  refine Hs.then (Hs.setx (hs_inc C kT1 b5 (by rw [e5]; omega))) (fun b6 ⟨e6, s6, f6⟩ n6 hn6 => ?_)
  have F6 := frA F5 f6 (by decide)
  rw [e5] at e6
  have b6A : b6.env kAc = 2 * X := by rw [f6 kAc (by decide), f5 kAc (by decide), e4]
  refine Hs.then (Hs.setx (hs_mul C kAc kT1 kDB b6 (by decide) (by decide) (by decide) (by rw [b6A, e6]; exact hDB)))
    (fun b7 ⟨e7, s7, f7⟩ n7 hn7 => ?_)
  have F7 := frA F6 f7 (by decide)
  rw [b6A, e6] at e7
  refine Hs.last (CellTablesProg.sizeP_spec C kDB kS (by decide) (by decide) (by decide) b7 (cstF hc F7 (by decide))
    (2 * X * (W + 1)) e7 (lt_of_le_of_lt hsz hDB)) (fun b8 ⟨v8, _, s8, f8⟩ n8 hn8 => ?_)
  exact ⟨⟨v8, by rw [s8, s7, s6, s5, s4, s3, s2, s1], frA F7 f8 (by decide)⟩, by omega⟩

/-! ## `valueWidth`, `2^{valueWidth}` -/

def vwB : St VV MM :=
  .seq (.op (.mul wK kS kT1)) (.seq (.op (.shl kT1)) (.seq (.op (.add kT1 wK)) (.seq (.op (.inc kT1))
  (.seq (.op (.copy kVW kT1)) (CellTablesProg.pow2P p2VW kI kVW)))))

theorem vwB_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (k S : ℕ) (hk : a.env wK = k) (hS : a.env kS = S)
    (hW : k + 2 * k * S + 1 < C.Wd) :
    Hs C vwB a (5 * (k + 2 * k * S + 1) + 20) (fun e => e.env p2VW = 2 ^ (k + 2 * k * S + 1) ∧
      e.sh = a.sh ∧ Fr a e [kT1, kVW, p2VW, kI]) := by
  have hlt : k + 2 * k * S + 1 < 2 ^ C.Wd := lt_pow_of_le (by omega)
  have hkS : 2 * (k * S) = 2 * k * S := by ring
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_mul C wK kS kT1 a (by decide) (by decide) (by decide) (by rw [hk, hS]; nlinarith)))
    (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 [kT1, kVW, p2VW, kI] := Fr.weaken f1 (by decide)
  rw [hk, hS] at e1
  refine Hs.then (Hs.setx (hs_shl C kT1 b1 (by rw [e1, hkS]; omega))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  rw [e1, hkS] at e2
  refine Hs.then (Hs.setx (hs_add C kT1 wK b2 (by decide) (by rw [e2, F2 wK (by decide), hk]; omega)))
    (fun b3 ⟨e3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  rw [e2, F2 wK (by decide), hk] at e3
  refine Hs.then (Hs.setx (hs_inc C kT1 b3 (by rw [e3]; omega))) (fun b4 ⟨e4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  rw [e3, show 2 * k * S + k + 1 = k + 2 * k * S + 1 by ring] at e4
  refine Hs.then (Hs.setx (hs_copy C kVW kT1 b4 (by decide))) (fun b5 ⟨e5, s5, f5⟩ n5 hn5 => ?_)
  have F5 := frA F4 f5 (by decide)
  rw [e4] at e5
  refine Hs.last (CellTablesProg.pow2P_spec C p2VW kI kVW (by decide) (by decide) (by decide) (by decide) b5
    (cstF hc F5 (by decide)) _ e5 hW) (fun b6 ⟨v6, s6, f6⟩ n6 hn6 => ?_)
  exact ⟨⟨v6, by rw [s6, s5, s4, s3, s2, s1], frA F5 f6 (by decide)⟩, by omega⟩

/-! ## The saturating power -/

def capB (d h : Fin VV) : St VV MM :=
  .seq (.op (.mul d h kT1)) (.seq (.op (.copy d kT1)) (.ite (.lt p2VW d) (.op (.copy d p2VW)) skipS))

def capP (d h : Fin VV) : St VV MM := .seq (.op (.copy d v1)) (forS kU kE (capB d h))

theorem capP_spec (C : Ctx) (d h : Fin VV) (hdh : d ≠ h) (hdT : d ≠ kT1) (hhT : h ≠ kT1) (hdU : d ≠ kU)
    (hhU : h ≠ kU) (hdE : d ≠ kE) (hdP : d ≠ p2VW) (hd1 : d ≠ v1) (hdJ : d ≠ vJ) (hhJ : h ≠ vJ)
    (a : DS VV MM) (hc : Cst a) (H E V B : ℕ) (hH : a.env h = H) (hE : a.env kE = E) (hV : a.env p2VW = 2 ^ V)
    (hHB : H < 2 ^ B) (hVB : V + B ≤ C.Wd) (hEW : E < 2 ^ C.Wd) :
    Hs C (capP d h) a (10 * E + 6) (fun e => e.env d = min (H ^ E) (2 ^ V) ∧ e.sh = a.sh ∧
      Fr a e [d, kU, kT1, vJ]) := by
  have hpow : 2 ^ V * 2 ^ B ≤ 2 ^ C.Wd := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hVB
  have hV1 : 1 ≤ 2 ^ V := Nat.one_le_two_pow
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := E * (6 + 4) + 4) (Hs.setx (hs_copy C d v1 a hd1))
    (fun b1 ⟨e1, s1, f1⟩ => ?_)) (by omega) (fun _ h => h)
  rw [hc.one] at e1
  let I : ℕ → DS VV MM → Prop := fun k e => e.env d = min (H ^ k) (2 ^ V) ∧ e.env h = H ∧ e.env p2VW = 2 ^ V ∧
    e.sh = a.sh ∧ Fr a e [d, kU, kT1, vJ]
  have h0 : I 0 b1 := ⟨by rw [e1, pow_zero, min_eq_left hV1], by rw [f1 h (by simp [Ne.symm hdh]), hH],
    by rw [f1 p2VW (by simp [Ne.symm hdP]), hV], s1, Fr.weaken f1 (by simp)⟩
  refine Hs.mono (forS_spec' (C := C) kU kE (by decide) (capB d h) b1 E hEW I 6
    (fun k e v ⟨i1, i2, i3, i4, i5⟩ => ⟨by rw [DS.set_env_ne _ _ hdU]; exact i1,
      by rw [DS.set_env_ne _ _ hhU]; exact i2, by rw [DS.set_env_ne _ _ (by decide)]; exact i3, by simpa using i4,
      Fr.trans i5 (Fr.set e v (by simp))⟩) h0 (by rw [f1 kE (by simp [Ne.symm hdE]), hE]) ?_) le_rfl
    (fun e ⟨⟨i1, _, _, i4, i5⟩, _, _⟩ => ⟨i1, i4, i5⟩)
  intro k hk e ⟨i1, i2, i3, i4, i5⟩ hek hem
  have hmin : min (H ^ k) (2 ^ V) ≤ 2 ^ V := min_le_right _ _
  have hmul : e.env d * e.env h < 2 ^ C.Wd := by
    rw [i1, i2]
    calc min (H ^ k) (2 ^ V) * H ≤ 2 ^ V * H := Nat.mul_le_mul_right _ hmin
      _ < 2 ^ V * 2 ^ B := Nat.mul_lt_mul_of_pos_left hHB (by positivity)
      _ ≤ 2 ^ C.Wd := hpow
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (1 + 1) + 1) (Hs.setx (hs_mul C d h kT1 e hdh hdT hhT hmul))
    (fun f1 ⟨g1, s1, r1⟩ => ?_)) (by omega) (fun _ h => h)
  refine Hs.seq (t1 := 1) (t2 := 1 + 1) (Hs.setx (hs_copy C d kT1 f1 hdT)) (fun f2 ⟨g2, s2, r2⟩ => ?_)
  rw [g1, i1, i2] at g2
  have f2P : f2.env p2VW = 2 ^ V := by rw [r2 p2VW (by simp [Ne.symm hdP]), r1 p2VW (by decide), i3]
  have f2h : f2.env h = H := by rw [r2 h (by simp [Ne.symm hdh]), r1 h (by simp [hhT]), i2]
  have fr2 : Fr a f2 [d, kU, kT1, vJ] := Fr.trans i5 (Fr.trans (Fr.weaken r1 (by simp)) (Fr.weaken r2 (by simp)))
  have hcap := min_mul_cap (H ^ k) (2 ^ V) H
  rw [← pow_succ] at hcap
  refine Hs.ite (c := .lt p2VW d) (show p2VW ≠ d from Ne.symm hdP) (fun ht => ?_) (fun hf => ?_)
  · simp only [Cnd.eval, decide_eq_true_eq, f2P, g2] at ht
    refine Hs.mono (Hs.setx (hs_copy C d p2VW f2 hdP)) le_rfl (fun g ⟨g3, s3, r3⟩ => ?_)
    rw [f2P] at g3
    refine ⟨⟨by rw [g3, ← hcap, min_eq_right ht.le], by rw [r3 h (by simp [Ne.symm hdh]), f2h],
      by rw [r3 p2VW (by simp [Ne.symm hdP]), f2P], by rw [s3, s2, s1, i4], Fr.trans fr2 (Fr.weaken r3 (by simp))⟩,
      ?_, ?_⟩
    · rw [r3 kU (by simp [Ne.symm hdU]), r2 kU (by simp [Ne.symm hdU]), r1 kU (by decide)]; exact hek
    · rw [r3 kE (by simp [Ne.symm hdE]), r2 kE (by simp [Ne.symm hdE]), r1 kE (by decide)]; exact hem
  · simp only [Cnd.eval, decide_eq_false_iff_not, not_lt, f2P, g2] at hf
    refine Hs.mono (Hs.setx (skip_spec f2)) le_rfl (fun g ⟨g3, s3, r3⟩ => ?_)
    refine ⟨⟨by rw [r3 d (by simp [hdJ]), g2, ← hcap, min_eq_left hf], by rw [r3 h (by simp [hhJ]), f2h],
      by rw [r3 p2VW (by decide), f2P], by rw [s3, s2, s1, i4], Fr.trans fr2 (Fr.weaken r3 (by simp))⟩, ?_, ?_⟩
    · rw [r3 kU (by decide), r2 kU (by simp [Ne.symm hdU]), r1 kU (by decide)]; exact hek
    · rw [r3 kE (by decide), r2 kE (by simp [Ne.symm hdE]), r1 kE (by decide)]; exact hem

end NearCubicGates.Close.CellsConst

