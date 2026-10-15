import Proof.Gates.Succinct.EvalSub

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

/-- The evaluator's registers (paper lem:succinct-verifier, stage (3)). -/
inductive EReg where
  | f (r : FReg)
  | lb | lp | cb | s | j | tg | a | b | g1 | rv | y | z | t2 | b1 | b2
  deriving DecidableEq

/-- The value of a gate from its fields (paper lem:succinct-verifier, stage (3)). -/
def valueOf (t av bv gf : ℕ) (pt rd : ℕ → Bool) : Bool :=
  if t = 0 then decide (av ≠ 0)
  else if t = 1 then decide (gf = 0) && pt av
  else if t = 2 then !(rd av)
  else if t = 3 then rd av && rd bv
  else rd av || rd bv

/-- The constant gate. -/
def constW (E : EReg → Fin nr) : WM ns nr := .ifr (E .a) (.inc (E .rv)) .skip
/-- The input gate: the point's bit, unless the index tripped its guard. -/
def inputW (P : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .ifr (E .g1) .skip (seekRead P (E .a) (E .y) (E .rv))
/-- The negation gate. -/
def notW (V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (seekRead V (E .a) (E .y) (E .b1)) (.seq (.ifr (E .b1) .skip (.inc (E .rv))) (WM.clear (E .b1)))
/-- The two argument values into `b1`, `b2`. -/
def twoW (V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (seekRead V (E .a) (E .y) (E .b1)) (seekRead V (E .b) (E .y) (E .b2))
/-- The conjunction gate. -/
def andW (V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (twoW V E) (.seq (.ifr (E .b1) (.ifr (E .b2) (.inc (E .rv)) .skip) .skip)
    (.seq (WM.clear (E .b1)) (WM.clear (E .b2))))
/-- The disjunction gate. -/
def orW (V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (twoW V E) (.seq (.ifr (E .b1) (.inc (E .rv)) (.ifr (E .b2) (.inc (E .rv)) .skip))
    (.seq (WM.clear (E .b1)) (WM.clear (E .b2))))

/-- The gate value by its tag, then the gate's field registers cleared. -/
def valueW (P V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (.ifr (E .tg) (.seq (.dec (E .tg)) (.ifr (E .tg) (.seq (.dec (E .tg)) (.ifr (E .tg)
      (.seq (.dec (E .tg)) (.ifr (E .tg) (orW V E) (andW V E))) (notW V E))) (inputW P E))) (constW E))
    (.seq (WM.clear (E .tg)) (.seq (WM.clear (E .a)) (.seq (WM.clear (E .b)) (WM.clear (E .g1)))))

/-! ## The arms -/

def ArmPost (E : EReg → Fin nr) (σ τ : WState ns nr) (v : Bool) : Prop :=
  τ.val (E .rv) = v.toNat ∧ τ.val (E .a) ≤ σ.val (E .a) ∧ τ.val (E .b) ≤ σ.val (E .b) ∧
    SameExcept σ τ [] [E .rv, E .a, E .b]

theorem arm_const (cap : ℕ) (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (hrv : σ.val (E .rv) = 0) (hcap : 1 ≤ cap) :
    ∃ τ, WExec cap (constW E) σ τ 4 ∧ ArmPost E σ τ (decide (σ.val (E .a) ≠ 0)) := by
  by_cases ha : σ.val (E .a) = 0
  · refine ⟨σ, WExec.mono (WExec.ifrF ha (WExec.skip σ)) (by omega), by simp [ha, hrv], le_rfl, le_rfl,
      SameExcept.refl _ _ _⟩
  · refine ⟨σ.setv (E .rv) (σ.val (E .rv) + 1), WExec.ifrT ha (WExec.inc (E .rv) σ (by omega)), ?_, ?_, ?_,
      sameExcept_setv σ (by simp) _⟩
    · simp [hrv, ha]
    · simp [Function.update_apply, hE.eq_iff]
    · simp [Function.update_apply, hE.eq_iff]

theorem arm_input (cap : ℕ) (P : Fin (ns + 1)) (E : EReg → Fin nr) (hE : Function.Injective E)
    (σ : WState ns nr) (gf : ℕ) (hg : σ.val (E .g1) = gf) (hrv : σ.val (E .rv) = 0)
    (hy : σ.val (E .y) = 0) (hP : σ.sh P = 0) (hcap : σ.val (E .a) + 2 ≤ cap) :
    ∃ τ, WExec cap (inputW P E) σ τ (σ.val (E .a) * 14 + 11) ∧
      ArmPost E σ τ (decide (gf = 0) && readTapeBit (σ.st P) (σ.val (E .a))) := by
  by_cases hg0 : gf = 0
  · have e := seekRead_spec cap P (E .a) (E .y) (E .rv) (hE.ne (by decide)) (hE.ne (by decide))
      (hE.ne (by decide)) σ hy (by rw [hrv]; omega)
    refine ⟨_, WExec.ifrF (by rw [hg, hg0]) e, ?_, ?_, ?_, ?_⟩
    · simp [hrv, hP, hg0]
    · simp [Function.update_apply, hE.eq_iff]
    · simp [Function.update_apply, hE.eq_iff]
    · refine SameExcept.trans (sameExcept_setv σ (by simp) _) (sameExcept_setv _ (by simp) _)
  · refine ⟨σ, WExec.mono (WExec.ifrT (by rw [hg]; exact hg0) (WExec.skip σ)) (by omega), ?_, le_rfl, le_rfl,
      SameExcept.refl _ _ _⟩
    simp [hrv, hg0]

theorem arm_not (cap : ℕ) (V : Fin (ns + 1)) (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (hrv : σ.val (E .rv) = 0) (hy : σ.val (E .y) = 0) (hb1 : σ.val (E .b1) = 0)
    (hV : σ.sh V = 0) (hcap : σ.val (E .a) + 4 ≤ cap) :
    ∃ τ, WExec cap (notW V E) σ τ (σ.val (E .a) * 14 + 20) ∧ ArmPost E σ τ (!readTapeBit (σ.st V) (σ.val (E .a))) := by
  have e1 := seekRead_spec cap V (E .a) (E .y) (E .b1) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) σ hy (by rw [hb1]; omega)
  set bit := readTapeBit (σ.st V) (σ.sh V + σ.val (E .a)) with hbit
  set σ1 := (σ.setv (E .a) 0).setv (E .b1) (σ.val (E .b1) + bit.toNat) with hσ1
  have h1 : σ1.val (E .b1) = bit.toNat := by simp [σ1, hb1]
  have hrv1 : σ1.val (E .rv) = 0 := by simp [σ1, Function.update_apply, hE.eq_iff, hrv]
  have hb' : bit = readTapeBit (σ.st V) (σ.val (E .a)) := by rw [hbit, hV, Nat.zero_add]
  cases hb : bit with
  | true =>
    have e2 : WExec cap (.ifr (E .b1) .skip (.inc (E .rv))) σ1 σ1 1 :=
      WExec.ifrT (by rw [h1, hb]; simp) (WExec.skip σ1)
    have e3 := wclear_spec cap (E .b1) 1 σ1 (by rw [h1, hb]; rfl) (by rw [h1, hb]; simp; omega)
    refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), ?_, ?_, ?_, ?_⟩
    · rw [← hb', hb]; simp [Function.update_apply, hE.eq_iff, hrv1]
    · simp [σ1, Function.update_apply, hE.eq_iff]
    · simp [σ1, Function.update_apply, hE.eq_iff]
    · refine ⟨fun x _ => by simp [σ1], fun r hr => ?_, by simp [σ1]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases h : r = E .b1
      · subst h; simp [σ1, hb1]
      · simp [σ1, Function.update_apply, hr.2.1, h]
  | false =>
    have hrvc : σ1.val (E .rv) < cap := by rw [hrv1]; omega
    have e2 : WExec cap (.ifr (E .b1) .skip (.inc (E .rv))) σ1 (σ1.setv (E .rv) (σ1.val (E .rv) + 1)) 4 :=
      WExec.ifrF (by rw [h1, hb]; rfl) (WExec.inc (E .rv) σ1 hrvc)
    have hb1' : (σ1.setv (E .rv) (σ1.val (E .rv) + 1)).val (E .b1) = 0 := by
      simp [Function.update_apply, hE.eq_iff, h1, hb]
    have e3 := wclear_spec cap (E .b1) 0 (σ1.setv (E .rv) (σ1.val (E .rv) + 1)) hb1' (by rw [hb1']; omega)
    refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), ?_, ?_, ?_, ?_⟩
    · rw [← hb', hb]; simp [Function.update_apply, hE.eq_iff, hrv1]
    · simp [σ1, Function.update_apply, hE.eq_iff]
    · simp [σ1, Function.update_apply, hE.eq_iff]
    · refine ⟨fun x _ => by simp [σ1], fun r hr => ?_, by simp [σ1]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases h : r = E .b1
      · subst h; simp [σ1, Function.update_apply, hE.eq_iff, hb1]
      · simp [σ1, Function.update_apply, hr.1, hr.2.1, h]

theorem arm_two (cap : ℕ) (V : Fin (ns + 1)) (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (hy : σ.val (E .y) = 0) (hb1 : σ.val (E .b1) = 0) (hb2 : σ.val (E .b2) = 0)
    (hV : σ.sh V = 0) (hcap : σ.val (E .a) + σ.val (E .b) + 4 ≤ cap) :
    WExec cap (twoW V E) σ
      ((((σ.setv (E .a) 0).setv (E .b1) (readTapeBit (σ.st V) (σ.val (E .a))).toNat).setv (E .b) 0).setv (E .b2)
        (readTapeBit (σ.st V) (σ.val (E .b))).toNat) ((σ.val (E .a) + σ.val (E .b)) * 14 + 21) := by
  have e1 := seekRead_spec cap V (E .a) (E .y) (E .b1) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) σ hy (by rw [hb1]; omega)
  set σ1 := (σ.setv (E .a) 0).setv (E .b1) (σ.val (E .b1) + (readTapeBit (σ.st V) (σ.sh V + σ.val (E .a))).toNat)
    with hσ1
  have e2 := seekRead_spec cap V (E .b) (E .y) (E .b2) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) σ1 (by simp [σ1, Function.update_apply, hE.eq_iff, hy])
    (by simp [σ1, Function.update_apply, hE.eq_iff, hb2]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
  · simp [σ1, Function.update_apply, hE.eq_iff, hb1, hb2, hV]
  · simp [σ1, Function.update_apply, hE.eq_iff]; omega

theorem arm_and (cap : ℕ) (V : Fin (ns + 1)) (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr)
    (hrv : σ.val (E .rv) = 0) (hy : σ.val (E .y) = 0) (hb1 : σ.val (E .b1) = 0) (hb2 : σ.val (E .b2) = 0)
    (hV : σ.sh V = 0) (hcap : σ.val (E .a) + σ.val (E .b) + 4 ≤ cap) :
    ∃ τ, WExec cap (andW V E) σ τ ((σ.val (E .a) + σ.val (E .b)) * 14 + 40) ∧
      ArmPost E σ τ (readTapeBit (σ.st V) (σ.val (E .a)) && readTapeBit (σ.st V) (σ.val (E .b))) := by
  have e1 := arm_two cap V E hE σ hy hb1 hb2 hV hcap
  set x := readTapeBit (σ.st V) (σ.val (E .a)) with hx
  set w := readTapeBit (σ.st V) (σ.val (E .b)) with hw
  set σ1 := (((σ.setv (E .a) 0).setv (E .b1) x.toNat).setv (E .b) 0).setv (E .b2) w.toNat with hσ1
  have v1 : σ1.val (E .b1) = x.toNat := by simp [σ1, Function.update_apply, hE.eq_iff]
  have v2 : σ1.val (E .b2) = w.toNat := by simp [σ1]
  have vr : σ1.val (E .rv) = 0 := by simp [σ1, Function.update_apply, hE.eq_iff, hrv]
  set σ2 := σ1.setv (E .rv) (x && w).toNat with hσ2
  have e2 : WExec cap (.ifr (E .b1) (.ifr (E .b2) (.inc (E .rv)) .skip) .skip) σ1 σ2 5 := by
    cases hxv : x <;> cases hwv : w
    · exact WExec.mono (WExec.ifrF (by rw [v1, hxv]; rfl) (by rw [hσ2, hxv]; simp [← vr, wsetv_same]; exact WExec.skip σ1)) (by omega)
    · exact WExec.mono (WExec.ifrF (by rw [v1, hxv]; rfl) (by rw [hσ2, hxv]; simp [← vr, wsetv_same]; exact WExec.skip σ1)) (by omega)
    · exact WExec.mono (WExec.ifrT (by rw [v1, hxv]; simp) (WExec.ifrF (by rw [v2, hwv]; rfl)
        (by rw [hσ2, hxv, hwv]; simp [← vr, wsetv_same]; exact WExec.skip σ1))) (by omega)
    · have := WExec.inc (cap := cap) (E .rv) σ1 (by rw [vr]; omega)
      rw [vr] at this
      exact WExec.ifrT (by rw [v1, hxv]; simp) (WExec.ifrT (by rw [v2, hwv]; simp)
        (by rw [hσ2, hxv, hwv]; exact this))
  have e3 := wclear_spec cap (E .b1) x.toNat σ2 (by simp [σ2, Function.update_apply, hE.eq_iff, v1])
    (by simp [σ2, Function.update_apply, hE.eq_iff, v1]; cases x <;> simp <;> omega)
  have e4 := wclear_spec cap (E .b2) w.toNat (σ2.setv (E .b1) 0)
    (by simp [σ2, Function.update_apply, hE.eq_iff, v2]) (by simp [σ2, Function.update_apply, hE.eq_iff, v2]; cases w <;> simp <;> omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)))
    (by have := Bool.toNat_le x; have := Bool.toNat_le w; omega), ?_, ?_, ?_, ?_⟩
  · simp [σ2, Function.update_apply, hE.eq_iff]
  · simp [σ2, σ1, Function.update_apply, hE.eq_iff]
  · simp [σ2, σ1, Function.update_apply, hE.eq_iff]
  · refine ⟨fun x _ => by simp [σ2, σ1], fun r hr => ?_, by simp [σ2, σ1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases h1 : r = E .b1
    · subst h1; simp [Function.update_apply, hE.eq_iff, hb1]
    · by_cases h2 : r = E .b2
      · subst h2; simp [hE.eq_iff, hb2]
      · simp [σ2, σ1, Function.update_apply, hr.1, hr.2.1, hr.2.2, h1, h2]

theorem arm_or (cap : ℕ) (V : Fin (ns + 1)) (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr)
    (hrv : σ.val (E .rv) = 0) (hy : σ.val (E .y) = 0) (hb1 : σ.val (E .b1) = 0) (hb2 : σ.val (E .b2) = 0)
    (hV : σ.sh V = 0) (hcap : σ.val (E .a) + σ.val (E .b) + 4 ≤ cap) :
    ∃ τ, WExec cap (orW V E) σ τ ((σ.val (E .a) + σ.val (E .b)) * 14 + 40) ∧
      ArmPost E σ τ (readTapeBit (σ.st V) (σ.val (E .a)) || readTapeBit (σ.st V) (σ.val (E .b))) := by
  have e1 := arm_two cap V E hE σ hy hb1 hb2 hV hcap
  set x := readTapeBit (σ.st V) (σ.val (E .a)) with hx
  set w := readTapeBit (σ.st V) (σ.val (E .b)) with hw
  set σ1 := (((σ.setv (E .a) 0).setv (E .b1) x.toNat).setv (E .b) 0).setv (E .b2) w.toNat with hσ1
  have v1 : σ1.val (E .b1) = x.toNat := by simp [σ1, Function.update_apply, hE.eq_iff]
  have v2 : σ1.val (E .b2) = w.toNat := by simp [σ1]
  have vr : σ1.val (E .rv) = 0 := by simp [σ1, Function.update_apply, hE.eq_iff, hrv]
  set σ2 := σ1.setv (E .rv) (x || w).toNat with hσ2
  have hinc := WExec.inc (cap := cap) (E .rv) σ1 (by rw [vr]; omega)
  rw [vr] at hinc
  have e2 : WExec cap (.ifr (E .b1) (.inc (E .rv)) (.ifr (E .b2) (.inc (E .rv)) .skip)) σ1 σ2 5 := by
    cases hxv : x <;> cases hwv : w
    · exact WExec.mono (WExec.ifrF (by rw [v1, hxv]; rfl) (WExec.ifrF (by rw [v2, hwv]; rfl)
        (by rw [hσ2, hxv, hwv]; simp [← vr, wsetv_same]; exact WExec.skip σ1))) (by omega)
    · exact WExec.mono (WExec.ifrF (by rw [v1, hxv]; rfl) (WExec.ifrT (by rw [v2, hwv]; simp)
        (by rw [hσ2, hxv, hwv]; exact hinc))) (by omega)
    · exact WExec.mono (WExec.ifrT (by rw [v1, hxv]; simp) (by rw [hσ2, hxv, hwv]; exact hinc)) (by omega)
    · exact WExec.mono (WExec.ifrT (by rw [v1, hxv]; simp) (by rw [hσ2, hxv, hwv]; exact hinc)) (by omega)
  have e3 := wclear_spec cap (E .b1) x.toNat σ2 (by simp [σ2, Function.update_apply, hE.eq_iff, v1])
    (by simp [σ2, Function.update_apply, hE.eq_iff, v1]; cases x <;> simp <;> omega)
  have e4 := wclear_spec cap (E .b2) w.toNat (σ2.setv (E .b1) 0)
    (by simp [σ2, Function.update_apply, hE.eq_iff, v2]) (by simp [σ2, Function.update_apply, hE.eq_iff, v2]; cases w <;> simp <;> omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)))
    (by have := Bool.toNat_le x; have := Bool.toNat_le w; omega), ?_, ?_, ?_, ?_⟩
  · simp [σ2, Function.update_apply, hE.eq_iff]
  · simp [σ2, σ1, Function.update_apply, hE.eq_iff]
  · simp [σ2, σ1, Function.update_apply, hE.eq_iff]
  · refine ⟨fun x _ => by simp [σ2, σ1], fun r hr => ?_, by simp [σ2, σ1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases h1 : r = E .b1
    · subst h1; simp [Function.update_apply, hE.eq_iff, hb1]
    · by_cases h2 : r = E .b2
      · subst h2; simp [hE.eq_iff, hb2]
      · simp [σ2, σ1, Function.update_apply, hr.1, hr.2.1, hr.2.2, h1, h2]

/-- The four clears after the dispatch. -/
theorem clears_spec (cap : ℕ) (E : EReg → Fin nr) (hE : Function.Injective E) (τ : WState ns nr) (A B : ℕ)
    (ha : τ.val (E .a) ≤ A) (hb : τ.val (E .b) ≤ B) (hcap : τ.val (E .tg) + A + B + τ.val (E .g1) ≤ cap) :
    ∃ ρ, WExec cap (.seq (WM.clear (E .tg)) (.seq (WM.clear (E .a)) (.seq (WM.clear (E .b)) (WM.clear (E .g1))))) τ ρ
        (3 * (τ.val (E .tg) + A + B + τ.val (E .g1)) + 7) ∧
      ρ.val (E .tg) = 0 ∧ ρ.val (E .a) = 0 ∧ ρ.val (E .b) = 0 ∧ ρ.val (E .g1) = 0 ∧
      SameExcept τ ρ [] [E .tg, E .a, E .b, E .g1] := by
  have e1 := wclear_spec cap (E .tg) _ τ rfl (by omega)
  have e2 := wclear_spec cap (E .a) _ (τ.setv (E .tg) 0) rfl
    (by simp [Function.update_apply, hE.eq_iff]; omega)
  have e3 := wclear_spec cap (E .b) _ ((τ.setv (E .tg) 0).setv (E .a) 0) rfl
    (by simp [Function.update_apply, hE.eq_iff]; omega)
  have e4 := wclear_spec cap (E .g1) _ (((τ.setv (E .tg) 0).setv (E .a) 0).setv (E .b) 0) rfl
    (by simp [Function.update_apply, hE.eq_iff]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, hE.eq_iff]; omega
  · simp [Function.update_apply, hE.eq_iff]
  · simp [Function.update_apply, hE.eq_iff]
  · simp [Function.update_apply, hE.eq_iff]
  · simp
  · exact SameExcept.trans (sameExcept_setv τ (by simp) _) (SameExcept.trans (sameExcept_setv _ (by simp) _)
      (SameExcept.trans (sameExcept_setv _ (by simp) _) (sameExcept_setv _ (by simp) _)))

theorem valueW_spec (cap : ℕ) (P V : Fin (ns + 1)) (E : EReg → Fin nr) (hE : Function.Injective E)
    (σ : WState ns nr) (gf : ℕ) (hg : σ.val (E .g1) = gf) (hrv : σ.val (E .rv) = 0) (hy : σ.val (E .y) = 0)
    (hb1 : σ.val (E .b1) = 0) (hb2 : σ.val (E .b2) = 0) (hP : σ.sh P = 0) (hV : σ.sh V = 0)
    (hcap : σ.val (E .tg) + σ.val (E .a) + σ.val (E .b) + gf + 4 ≤ cap) :
    ∃ τ, WExec cap (valueW P V E) σ τ (17 * (σ.val (E .a) + σ.val (E .b)) + 3 * σ.val (E .tg) + 3 * gf + 120) ∧
      τ.val (E .rv) = (valueOf (σ.val (E .tg)) (σ.val (E .a)) (σ.val (E .b)) gf (readTapeBit (σ.st P))
        (readTapeBit (σ.st V))).toNat ∧
      τ.val (E .tg) = 0 ∧ τ.val (E .a) = 0 ∧ τ.val (E .b) = 0 ∧ τ.val (E .g1) = 0 ∧
      SameExcept σ τ [] [E .rv, E .tg, E .a, E .b, E .g1] := by
  set t := σ.val (E .tg) with ht
  set av := σ.val (E .a) with hav
  set bv := σ.val (E .b) with hbv
  -- the dispatch, by the tag
  have hdisp : ∃ τ1, WExec cap (.ifr (E .tg) (.seq (.dec (E .tg)) (.ifr (E .tg) (.seq (.dec (E .tg)) (.ifr (E .tg)
        (.seq (.dec (E .tg)) (.ifr (E .tg) (orW V E) (andW V E))) (notW V E))) (inputW P E))) (constW E)) σ τ1
        (14 * (av + bv) + 50) ∧
      τ1.val (E .rv) = (valueOf t av bv gf (readTapeBit (σ.st P)) (readTapeBit (σ.st V))).toNat ∧
      τ1.val (E .tg) ≤ t ∧ τ1.val (E .a) ≤ av ∧ τ1.val (E .b) ≤ bv ∧ τ1.val (E .g1) = gf ∧
      SameExcept σ τ1 [] [E .rv, E .tg, E .a, E .b] := by
    have se_dec : ∀ (ρ : WState ns nr) (x : ℕ), SameExcept ρ (ρ.setv (E .tg) x) [] [E .rv, E .tg, E .a, E .b] :=
      fun ρ x => sameExcept_setv ρ (by simp) x
    have widen : ∀ {ρ τ : WState ns nr}, SameExcept ρ τ [] [E .rv, E .a, E .b] →
        SameExcept ρ τ [] [E .rv, E .tg, E .a, E .b] :=
      fun h => h.weaken (fun _ h => h) (fun r hr => by simp at hr ⊢; tauto)
    rcases Nat.lt_or_ge t 4 with h4 | h4
    · interval_cases ht' : t
      · -- constant
        obtain ⟨τ, e, hr, ha, hb, hse⟩ := arm_const cap E hE σ hrv (by omega)
        refine ⟨τ, WExec.mono (WExec.ifrF (by omega) e) (by omega), ?_, ?_, ha, hb, ?_, widen hse⟩
        · rw [hr]; simp [valueOf] <;> rfl
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩)]; omega
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩), hg]
      · -- input
        have ed := WExec.dec (cap := cap) (E .tg) σ (by omega)
        set σ1 := σ.setv (E .tg) (σ.val (E .tg) - 1) with hσ1
        have h0 : σ1.val (E .tg) = 0 := by simp [σ1]; omega
        obtain ⟨τ, e, hr, ha, hb, hse⟩ := arm_input cap P E hE σ1 gf (by simp [σ1, Function.update_apply, hE.eq_iff, hg])
          (by simp [σ1, Function.update_apply, hE.eq_iff, hrv]) (by simp [σ1, Function.update_apply, hE.eq_iff, hy])
          (by simp [σ1, hP]) (by simp [σ1, Function.update_apply, hE.eq_iff]; omega)
        refine ⟨τ, WExec.mono (WExec.ifrT (by omega) (WExec.seq ed (WExec.ifrF h0 e))) ?_, ?_, ?_, ?_, ?_, ?_,
          (se_dec σ _).trans (widen hse)⟩
        · simp [σ1, Function.update_apply, hE.eq_iff]; omega
        · rw [hr]; simp [valueOf, σ1, Function.update_apply, hE.eq_iff] <;> rfl
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩), h0]; omega
        · simpa [σ1, Function.update_apply, hE.eq_iff] using ha
        · simpa [σ1, Function.update_apply, hE.eq_iff] using hb
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩)]
          simp [σ1, Function.update_apply, hE.eq_iff, hg]
      · -- not
        have ed1 := WExec.dec (cap := cap) (E .tg) σ (by omega)
        set σ1 := σ.setv (E .tg) (σ.val (E .tg) - 1) with hσ1
        have h1 : σ1.val (E .tg) = 1 := by simp [σ1]; omega
        have ed2 := WExec.dec (cap := cap) (E .tg) σ1 (by omega)
        set σ2 := σ1.setv (E .tg) (σ1.val (E .tg) - 1) with hσ2
        have h0 : σ2.val (E .tg) = 0 := by simp [σ2, h1]
        obtain ⟨τ, e, hr, ha, hb, hse⟩ := arm_not cap V E hE σ2 (by simp [σ2, σ1, Function.update_apply, hE.eq_iff, hrv])
          (by simp [σ2, σ1, Function.update_apply, hE.eq_iff, hy])
          (by simp [σ2, σ1, Function.update_apply, hE.eq_iff, hb1]) (by simp [σ2, σ1, hV])
          (by simp [σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
        refine ⟨τ, WExec.mono (WExec.ifrT (by omega) (WExec.seq ed1 (WExec.ifrT (by omega)
          (WExec.seq ed2 (WExec.ifrF h0 e))))) ?_, ?_, ?_, ?_, ?_, ?_,
          ((se_dec σ _).trans (se_dec σ1 _)).trans (widen hse)⟩
        · simp [σ2, σ1, Function.update_apply, hE.eq_iff]; omega
        · rw [hr]; simp [valueOf, σ2, σ1, Function.update_apply, hE.eq_iff] <;> rfl
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩), h0]; omega
        · simpa [σ2, σ1, Function.update_apply, hE.eq_iff] using ha
        · simpa [σ2, σ1, Function.update_apply, hE.eq_iff] using hb
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩)]
          simp [σ2, σ1, Function.update_apply, hE.eq_iff, hg]
      · -- and
        have ed1 := WExec.dec (cap := cap) (E .tg) σ (by omega)
        set σ1 := σ.setv (E .tg) (σ.val (E .tg) - 1) with hσ1
        have h2 : σ1.val (E .tg) = 2 := by simp [σ1]; omega
        have ed2 := WExec.dec (cap := cap) (E .tg) σ1 (by omega)
        set σ2 := σ1.setv (E .tg) (σ1.val (E .tg) - 1) with hσ2
        have h1 : σ2.val (E .tg) = 1 := by simp [σ2, h2]
        have ed3 := WExec.dec (cap := cap) (E .tg) σ2 (by omega)
        set σ3 := σ2.setv (E .tg) (σ2.val (E .tg) - 1) with hσ3
        have h0 : σ3.val (E .tg) = 0 := by simp [σ3, h1]
        obtain ⟨τ, e, hr, ha, hb, hse⟩ := arm_and cap V E hE σ3
          (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hrv])
          (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hy])
          (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hb1])
          (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hb2]) (by simp [σ3, σ2, σ1, hV])
          (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
        refine ⟨τ, WExec.mono (WExec.ifrT (by omega) (WExec.seq ed1 (WExec.ifrT (by omega)
          (WExec.seq ed2 (WExec.ifrT (by omega) (WExec.seq ed3 (WExec.ifrF h0 e))))))) ?_, ?_, ?_, ?_, ?_, ?_,
          (((se_dec σ _).trans (se_dec σ1 _)).trans (se_dec σ2 _)).trans (widen hse)⟩
        · simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff]; omega
        · rw [hr]; simp [valueOf, σ3, σ2, σ1, Function.update_apply, hE.eq_iff] <;> rfl
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩), h0]; omega
        · simpa [σ3, σ2, σ1, Function.update_apply, hE.eq_iff] using ha
        · simpa [σ3, σ2, σ1, Function.update_apply, hE.eq_iff] using hb
        · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩)]
          simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hg]
    · -- or
      have ed1 := WExec.dec (cap := cap) (E .tg) σ (by omega)
      set σ1 := σ.setv (E .tg) (σ.val (E .tg) - 1) with hσ1
      have h2 : σ1.val (E .tg) = t - 1 := by simp [σ1]; rfl
      have ed2 := WExec.dec (cap := cap) (E .tg) σ1 (by omega)
      set σ2 := σ1.setv (E .tg) (σ1.val (E .tg) - 1) with hσ2
      have h1 : σ2.val (E .tg) = t - 2 := by simp [σ2, h2]; omega
      have ed3 := WExec.dec (cap := cap) (E .tg) σ2 (by omega)
      set σ3 := σ2.setv (E .tg) (σ2.val (E .tg) - 1) with hσ3
      have h0 : σ3.val (E .tg) = t - 3 := by simp [σ3, h1]; omega
      obtain ⟨τ, e, hr, ha, hb, hse⟩ := arm_or cap V E hE σ3
        (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hrv])
        (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hy])
        (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hb1])
        (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hb2]) (by simp [σ3, σ2, σ1, hV])
        (by simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff]; omega)
      refine ⟨τ, WExec.mono (WExec.ifrT (by omega) (WExec.seq ed1 (WExec.ifrT (by omega)
        (WExec.seq ed2 (WExec.ifrT (by omega) (WExec.seq ed3 (WExec.ifrT (by omega) e))))))) ?_, ?_, ?_, ?_, ?_, ?_,
        (((se_dec σ _).trans (se_dec σ1 _)).trans (se_dec σ2 _)).trans (widen hse)⟩
      · simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff]; omega
      · rw [hr]
        have e0 : ¬ t = 0 := by omega
        have e1 : ¬ t = 1 := by omega
        have e2 : ¬ t = 2 := by omega
        have e3 : ¬ t = 3 := by omega
        simp only [valueOf, if_neg e0, if_neg e1, if_neg e2, if_neg e3]
        simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff] <;> rfl
      · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩), h0]; omega
      · simpa [σ3, σ2, σ1, Function.update_apply, hE.eq_iff] using ha
      · simpa [σ3, σ2, σ1, Function.update_apply, hE.eq_iff] using hb
      · rw [hse.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩)]
        simp [σ3, σ2, σ1, Function.update_apply, hE.eq_iff, hg]
  obtain ⟨τ1, e1, hr1, ht1, ha1, hb1', hg1, hse1⟩ := hdisp
  obtain ⟨ρ, e2, h1, h2, h3, h4, hse2⟩ := clears_spec cap E hE τ1 av bv ha1 hb1' (by omega)
  refine ⟨ρ, WExec.mono (WExec.seq e1 e2) (by omega), ?_, h1, h2, h3, h4, ?_⟩
  · rw [hse2.val (by simp; exact ⟨hE.ne (by decide), hE.ne (by decide), hE.ne (by decide), hE.ne (by decide)⟩), hr1]
  · exact (hse1.weaken (fun _ h => h) (fun r hr => by simp at hr ⊢; tauto)).trans
      (hse2.weaken (fun _ h => h) (fun r hr => by simp at hr ⊢; tauto))

end NearCubicGates.Close.Succinct
