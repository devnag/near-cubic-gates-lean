import Proof.Gates.Recovery.AfterParts
import Proof.Gates.OuterM.ARun

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms NearCubicGates.Close.OuterM

/-- A word on stream `0`, every other stream empty, heads and registers `0`. -/
def startOne (ns nr : ℕ) (w : List Bool) : WState ns nr :=
  ⟨fun _ => 0, fun i => if i.val = 0 then w else [], fun _ => 0, false⟩

open NearCubicWires.WireExponent3_5.PrimAsm.DockW in
/-- The cold bank of `startOne` is the one-port bank on stream `0`. -/
theorem bank_one (ns nr : ℕ) (w : List Bool) :
    Fin.addCases (motive := fun _ => List Bool) (CheckedPCPP.coldBank (startOne ns nr w)) (fun _ : Fin 1 => []) =
      oneBank (Fin.castAdd 1 (sTape (nr := nr) (0 : Fin (ns + 1)))) w := by
  funext j
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left]
    unfold oneBank
    rcases tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [CheckedPCPP.coldBank_s]
      simp only [startOne, Fin.ext_iff, Fin.val_castAdd, sTape_val]
      by_cases h0 : i.val = 0
      · simp [h0]
      · rw [if_neg h0, if_neg (by simp [h0])]
    · rw [CheckedPCPP.coldBank_c]
      simp [Fin.ext_iff, Fin.val_castAdd, sTape_val, cTape_val]
    · rw [CheckedPCPP.coldBank_r]
      simp only [Fin.ext_iff, Fin.val_castAdd, sTape_val, rTape_val]
      rw [if_neg (by simp <;> omega)]
  · rw [Fin.addCases_right]
    unfold oneBank
    simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, sTape_val]
    rw [if_neg (by simp <;> omega)]

/-! ## `1^ν` -/

/-- `frame x ↦ 1^{⌊log₂ |x|⌋}` on stream `1` (registers as in `OuterM.WidthW`: `0` count, `1` halvings, `2` scratch,
`3` the unary counter, `7` the output position). -/
def nuProg : WMX 1 9 :=
  .wm (.seq cntL (.seq (hcW 0 1 2) (.seq (.dec 1) (.seq (WM.move 1 3) unaL))))

/-- The cost of `nuProg` on a word of length `n`. -/
def nuCost (n : ℕ) : ℕ :=
  (9 * n + 1) + 1 + ((30 * n + 20 * hc n + 1) + 1 + (1 + 1 + ((7 * (hc n - 1) + 1) + 1 + (11 * (hc n - 1) + 1))))

theorem nuProg_spec (x : List Bool) :
    ∃ τ, WXExec (2 * x.length + 4) nuProg (startOne 1 9 (RepairOrdinary.frame x)) τ (nuCost x.length) ∧
      τ.st 1 = List.replicate (Nat.log 2 x.length) true := by
  set cap := 2 * x.length + 4 with hcap
  set σ := startOne 1 9 (RepairOrdinary.frame x) with hσ
  have hcN := hc_le x.length
  have e1 := cntL_spec cap x x.length 0 σ (by omega) (by simp [σ, startOne]) (by simp [σ, startOne])
    (by simp [σ, startOne]) (by omega)
  set σ1 := (σ.seth 0 (2 * x.length)).setv 0 x.length with hσ1
  have e2 := hcW_spec cap (0 : Fin 9) 1 2 (by decide) (by decide) (by decide) x.length σ1 (by simp [σ1])
    (by simp [σ1, σ, startOne]) (by simp [σ1, σ, startOne]; omega) (by omega)
  set σ2 := (σ1.setv 0 0).setv 1 (σ1.val 1 + hc x.length) with hσ2
  have e3 := WExec.dec (cap := cap) (1 : Fin 9) σ2 (by simp [σ2, σ1, σ, startOne]; omega)
  set σ3 := σ2.setv 1 (σ2.val 1 - 1) with hσ3
  have h3 : σ3.val 1 = hc x.length - 1 := by simp [σ3, σ2, σ1, σ, startOne]
  have e4 := wmove_spec cap (1 : Fin 9) 3 (by decide) (hc x.length - 1) σ3 h3 (by rw [h3]; omega)
    (by simp [σ3, σ2, σ1, σ, startOne]; omega)
  set σ4 := (σ3.setv 1 0).setv 3 (σ3.val 3 + σ3.val 1) with hσ4
  have e5 := unaL_spec cap (hc x.length - 1) σ4 [] (by simp [σ4, h3, σ3, σ2, σ1, σ, startOne])
    (by simp [σ4, σ3, σ2, σ1, σ, startOne]) (by simp [σ4, σ3, σ2, σ1, σ, startOne])
    (by simp [σ4, σ3, σ2, σ1, σ, startOne]) (by simp; omega) (by omega)
  refine ⟨_, WXExec.wm (WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))))
    (by unfold nuCost; omega)), ?_⟩
  simp [log_eq_hc]

theorem readyRun_budget {t s : ℕ} {p : Machine t s} {f f' : ℕ} {input out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p f input out) (hf : f ≤ f') : ClockJoin.ReadyRun p f' input out :=
  OuterM.readyRun_mono h hf

open NearCubicWires.WireExponent3_5.PrimAsm.DockW in
/-- **`1^ν`** (paper §11.4): `frame x ↦ 1^{⌊log₂ |x|⌋}` within `200 (|x| + 1)` steps. -/
noncomputable def nuDonor : NuDonor where
  t := 1 + 2 + 9 + 1
  st := nuProg.size + 2
  M := Rewind.machine nuProg.compile
  inp := Fin.castAdd 1 (sTape (nr := 9) (0 : Fin 2))
  outp := Fin.castAdd 1 (sTape (nr := 9) (1 : Fin 2))
  ne := by simp [Fin.ext_iff, sTape_val]
  K := 200
  run := fun x => by
    obtain ⟨τ, h, hout⟩ := nuProg_spec x
    obtain ⟨out, hr, hst⟩ := CheckedPCPP.WXExec.readyRewound h (fun _ => rfl) (fun _ => rfl) rfl
    rw [bank_one] at hr
    refine ⟨out, readyRun_budget hr ?_, by rw [hst, hout]⟩
    have := hc_le x.length
    unfold nuCost
    omega

/-! ## Unframe -/

/-- One data cell of the framed stream `0` onto the raw stream `1`. -/
def unBody : WM 1 1 := .seq (.fwd 0) (.seq (.ifs 0 (.wr 1 true) (.wr 1 false)) (.seq (.fwd 0) (.fwd 1)))

/-- `frame d ↦ d`. -/
def unLoop : WM 1 1 := .whs 0 unBody

theorem unLoop_spec (cap : ℕ) (d : List Bool) : ∀ (m j : ℕ) (σ : WState 1 1), j + m = d.length →
    σ.st 0 = RepairOrdinary.frame d → σ.sh 0 = 2 * j → σ.st 1 = d.take j → σ.sh 1 = j →
    WExec cap unLoop σ (((σ.seth 0 (2 * d.length)).sets 1 d).seth 1 d.length) (10 * m + 1)
  | 0, j, σ, hj, hst, hsh, h1, h1h => by
    have hb : wbit σ 0 = false := by unfold wbit; rw [hst, hsh, frame_even]; simp; omega
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    have hjd : j = d.length := by omega
    subst hjd
    rw [List.take_length] at h1
    refine WState.eq ?_ ?_ rfl rfl
    · funext x; fin_cases x <;> simp [Function.update_apply, hsh, h1h]
    · funext x; fin_cases x <;> simp [Function.update_apply, h1]
  | m + 1, j, σ, hj, hst, hsh, h1, h1h => by
    have hb : wbit σ 0 = true := by unfold wbit; rw [hst, hsh, frame_even]; simp; omega
    have e1 := WExec.fwd (cap := cap) (0 : Fin 2) σ
    set σ1 := σ.seth 0 (σ.sh 0 + 1) with hσ1
    have e2 := wrBit_spec cap (0 : Fin 2) 1 σ1
    have hb1 : wbit σ1 0 = d.getD j false := by
      unfold wbit; simp only [σ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hst, hsh, frame_odd d j (by omega)]
    set σ2 := σ1.sets 1 (writeTapeBit (σ1.st 1) (σ1.sh 1) (wbit σ1 0)) with hσ2
    have hw : writeTapeBit (σ1.st 1) (σ1.sh 1) (wbit σ1 0) = d.take (j + 1) := by
      have e : σ1.st 1 = d.take j := by simp [σ1, h1]
      have e' : σ1.sh 1 = (d.take j).length := by
        simp [σ1, Function.update_apply, h1h]; omega
      rw [e, e', writeTapeBit_end, hb1, take_succ_getD d j (by omega)]
    have e3 := WExec.fwd (cap := cap) (0 : Fin 2) σ2
    have e4 := WExec.fwd (cap := cap) (1 : Fin 2) (σ2.seth 0 (σ2.sh 0 + 1))
    set σ4 := (σ2.seth 0 (σ2.sh 0 + 1)).seth 1 ((σ2.seth 0 (σ2.sh 0 + 1)).sh 1 + 1) with hσ4
    have ih := unLoop_spec cap d m (j + 1) σ4 (by omega) (by simp [σ4, σ2, σ1, hst])
      (by simp [σ4, σ2, σ1, hsh]; omega) (by simp [σ4, σ2, hw]) (by simp [σ4, σ2, σ1, h1h])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) ?_ (by omega)
    refine WState.eq ?_ ?_ rfl rfl
    · funext x; fin_cases x <;> simp [σ4, σ2, σ1, Function.update_apply]
    · funext x; fin_cases x <;> simp [σ4, σ2, σ1, Function.update_apply]

open NearCubicWires.WireExponent3_5.PrimAsm.DockW in
/-- **Unframe** (paper §11.6): `frame d ↦ d` within `30 (|d| + 1)` steps. -/
noncomputable def unframe : Unframe where
  t := 1 + 2 + 1 + 1
  st := (WMX.wm unLoop : WMX 1 1).size + 2
  M := Rewind.machine (WMX.wm unLoop : WMX 1 1).compile
  src := Fin.castAdd 1 (sTape (nr := 1) (0 : Fin 2))
  dst := Fin.castAdd 1 (sTape (nr := 1) (1 : Fin 2))
  ne := by simp [Fin.ext_iff, sTape_val]
  K := 30
  run := fun d => by
    have e := unLoop_spec 0 d d.length 0 (startOne 1 1 (RepairOrdinary.frame d)) (by omega)
      (by simp [startOne]) (by simp [startOne]) (by simp [startOne]) (by simp [startOne])
    obtain ⟨out, hr, hst⟩ := CheckedPCPP.WXExec.readyRewound (WXExec.wm e) (fun _ => rfl) (fun _ => rfl) rfl
    rw [bank_one] at hr
    refine ⟨out, readyRun_budget hr (by omega), by rw [hst]; simp⟩

end NearCubicGates.Close.Recovery.After
