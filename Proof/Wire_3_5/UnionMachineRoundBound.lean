import Proof.Wire_3_5.UnionMachineCallRound

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

local notation "sR" => (1 : Fin 3)
local notation "sD" => (2 : Fin 3)
local notation "rF" => (0 : Fin 14)
local notation "rRC" => (1 : Fin 14)
local notation "rQ" => (2 : Fin 14)
local notation "rK" => (8 : Fin 14)
local notation "rPC" => (9 : Fin 14)
local notation "rMP" => (10 : Fin 14)
local notation "rMN" => (11 : Fin 14)

variable (cap : ℕ)

/-- The rounded answer's positive register: `⌊|v|·2^p⌋` for `v ≥ 0`. -/
def mpOf (v : ℚ) (p : ℕ) : ℕ := if sgn v then 0 else (divRef v.num.natAbs v.den p).2

/-- The rounded answer's negative register: `⌈|v|·2^p⌉` for `v < 0`. -/
def mnOf (v : ℚ) (p : ℕ) : ℕ :=
  if sgn v then (divRef v.num.natAbs v.den p).2 + (if (divRef v.num.natAbs v.den p).1 = 0 then 0 else 1) else 0

theorem mpOf_le (v : ℚ) (p : ℕ) (hv : v.num.natAbs < 4 * v.den) : mpOf v p ≤ 4 * 2 ^ p := by
  have := divRef_q_lt v.num.natAbs v.den p v.den_pos hv
  unfold mpOf; split_ifs <;> omega

theorem mnOf_le (v : ℚ) (p : ℕ) (hv : v.num.natAbs < 4 * v.den) : mnOf v p ≤ 4 * 2 ^ p := by
  have := divRef_q_lt v.num.natAbs v.den p v.den_pos hv
  unfold mnOf; split_ifs <;> omega

theorem signP_bound (w den p : ℕ) (sg : Bool) (r q : ℕ) (σ : RS) (hσ : DivSt w den p sg.toNat r q σ)
    (hr : r < 2 ^ w) (hcap : 2 * w + q + 2 ≤ cap) :
    ∃ τ, WExec cap signP σ τ (w * 41 + 7 * q + 16) ∧
      ((τ.val rMP : ℤ) - τ.val rMN = floorVal sg (r, q)) ∧ τ.val rPC = p ∧ τ.cell = σ.cell ∧
      τ.val rMP = (if sg then 0 else q) ∧ τ.val rMN = (if sg then q + (if r = 0 then 0 else 1) else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hσ
  cases sg
  · have e := wmove_spec cap rQ rMP (by decide) q σ h7 (by omega) (by omega)
    refine ⟨_, WExec.mono (WExec.ifrF (by simpa using h10) e) (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_apply, h7, h11, h12, floorVal]
    · simp [Function.update_apply, h9]
    · rfl
    · simp [Function.update_apply, h7, h11]
    · simp [Function.update_apply, h12]
  · have e1 := mapPass_spec cap keepA anyN sR sD rF rRC (by decide) (by decide) (by omega) (binary w r)
      (binary w den) [] [false] false σ (by simp) (by simp [h1]) h2 (by simp [h3]) h4 (by simp [h5]) h6
      (by simp; omega)
    rw [mapS_keepA anyN _ _ _ (by simp), mapS_any w r _ false (by simp), Nat.mod_eq_of_lt hr, binary_length] at e1
    simp only [Bool.false_or] at e1
    set σ1 := (σ.sets sR (frameP (binary w r) ++ [false])).setv rF (decide (r ≠ 0)).toNat with hσ1
    have e2 := wmove_spec cap rQ rMN (by decide) q σ1 (by simp [σ1, Function.update_apply, h7])
      (by simp [σ1, Function.update_apply, h7]; omega) (by simp [σ1, Function.update_apply, h7, h12]; omega)
    set σ2 := (σ1.setv rQ 0).setv rMN (σ1.val rMN + σ1.val rQ) with hσ2
    by_cases hr0 : r = 0
    · have hF : σ2.val rF = 0 := by simp [σ2, σ1, Function.update_apply, hr0]
      refine ⟨σ2, WExec.mono (WExec.ifrT (by simp [h10]) (e1.seq (e2.seq (WExec.ifrF hF (WExec.skip σ2)))))
        (by omega), ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ2, σ1, Function.update_apply, h7, h11, h12, floorVal, hr0]
      · simp [σ2, σ1, Function.update_apply, h9]
      · rfl
      · simp [σ2, σ1, Function.update_apply, h11]
      · simp [σ2, σ1, Function.update_apply, h7, h12, hr0]
    · have hF : σ2.val rF ≠ 0 := by simp [σ2, σ1, Function.update_apply, hr0]
      have e3 := WExec.inc (cap := cap) rMN σ2 (by simp [σ2, σ1, Function.update_apply, h7, h12]; omega)
      refine ⟨_, WExec.mono (WExec.ifrT (by simp [h10]) (e1.seq (e2.seq (WExec.ifrT hF e3)))) (by omega),
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ2, σ1, Function.update_apply, h7, h11, h12, floorVal, hr0]
      · simp [σ2, σ1, Function.update_apply, h9]
      · rfl
      · simp [σ2, σ1, Function.update_apply, h11]
      · simp [σ2, σ1, Function.update_apply, h7, h12, hr0]

theorem round_bound (v : ℚ) (p : ℕ) (c : Bool) (hv : v.num.natAbs < 4 * v.den)
    (hcap : 4 * lb v + 8 * 2 ^ p + 20 ≤ cap) :
    ∃ τ, WExec cap roundP (parseIn v p c) τ (roundCost (lb v) p) ∧
      ((τ.val rMP : ℤ) - τ.val rMN = ⌊v * 2 ^ p⌋) ∧ τ.val rPC = p ∧ τ.cell = c ∧
      τ.val rMP = mpOf v p ∧ τ.val rMN = mnOf v p ∧ mpOf v p ≤ 4 * 2 ^ p ∧ mnOf v p ≤ 4 * 2 ^ p := by
  have hd0 : 0 < v.den := v.den_pos
  have hdw : 4 * v.den ≤ 2 ^ (lb v + 2) := by
    have := natBitLength_lt v.den
    rw [pow_add]; unfold lb at *; omega
  have hnw : v.num.natAbs < 2 ^ (lb v + 2) := by omega
  have hdw' : v.den < 2 ^ (lb v + 2) := by omega
  have e0 := parse_spec cap v p c hv (by omega)
  have hP : DivSt (lb v + 2) v.den p (sgn v).toNat v.num.natAbs 0 (parseOut v p c) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [parseOut, st3]
  obtain ⟨τ1, e1, hτ1, hK1⟩ := intP_spec cap (lb v + 2) v.den p _ _ _ hP hnw hdw' (by omega)
  rw [intStep3 _ _ hd0 hv] at hτ1
  obtain ⟨τ2, e2, hτ2⟩ := fracP_spec cap (lb v + 2) v.num.natAbs v.den p _ τ1 hτ1
    (by rw [hK1]; simp [parseOut, st3]) hd0 hv hdw (by omega)
  have hq := divRef_q_lt v.num.natAbs v.den p hd0 hv
  obtain ⟨_, hrlt⟩ := divRef_inv v.num.natAbs v.den hd0 hv p
  obtain ⟨τ3, e3, hval, hpc, hcell, hmp, hmn⟩ := signP_bound cap (lb v + 2) v.den p (sgn v) _ _ τ2 hτ2 (by omega)
    (by omega)
  refine ⟨τ3, WExec.mono (e0.seq (e1.seq (e2.seq e3))) ?_, ?_, hpc, ?_, by rw [hmp]; rfl, by rw [hmn]; rfl,
    mpOf_le v p hv, mnOf_le v p hv⟩
  · unfold roundCost; nlinarith
  · rw [hval, floorVal_eq v p hv]
  · rw [hcell]
    exact (cellFree_cell cap (by decide) e2).trans ((cellFree_cell cap (by decide) e1).trans
      (by simp [parseOut, st3]))

end NearCubicWires.WireExponent3_5.UnionMachine.Round

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires.WireExponent3_5.Cost

section CallRoundBound
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

theorem callRound_bound {N : ℕ} (es : Fin (estRW P).program.tapeCount → Fin N) (rs : Fin (2 + 2 + 14) → Fin N)
    (hes : Function.Injective es) (hrs : Function.Injective rs)
    (hshare : rs 0 = es (estRW P).program.outputTape)
    (hdisj : ∀ j k, es j = rs k → k = 0)
    (req : {req : PrimRequest // I.Call req}) (p cap : ℕ) (c : Bool) (H : Fin N → ℕ) (A : Fin N → List Bool)
    (hH : ∀ j, H (es j) = 0) (hin : A (es (C10WordFunctionDock.inSlot (estRW P).program)) = frame req.1.word)
    (hblank : ∀ j, j ≠ C10WordFunctionDock.inSlot (estRW P).program → A (es j) = [])
    (hRH : ∀ k, k ≠ 0 → H (rs k) = (wenc cap (parseIn (P.value req.1) p c)).H k)
    (hRA : ∀ k, k ≠ 0 → A (rs k) = (wenc cap (parseIn (P.value req.1) p c)).A k)
    (hcap : 4 * lb (P.value req.1) + 8 * 2 ^ p + 20 ≤ cap) :
    ∃ (H' : Fin N → ℕ) (A' : Fin N → List Bool),
      Step (callRoundM P es rs) (2 * B.callBudget req.1.n + 2 + 1 + roundCost (lb (P.value req.1)) p) H A H' A' ∧
      (∃ τ : RS, ((τ.val 10 : ℤ) - τ.val 11 = ⌊P.value req.1 * 2 ^ p⌋) ∧ τ.val 9 = p ∧ τ.cell = c ∧
        τ.val 10 = mpOf (P.value req.1) p ∧ τ.val 11 = mnOf (P.value req.1) p ∧
        ∀ k, H' (rs k) = (wenc cap τ).H k ∧ A' (rs k) = (wenc cap τ).A k) ∧
      (∀ i, (∀ j, es j ≠ i) → (∀ k, rs k ≠ i) → H' i = H i ∧ A' i = A i) := by
  set v := P.value req.1 with hv
  -- the call
  obtain ⟨tout, hout, hcall⟩ := C10WordFunctionDock.rewound_dock (estRW P) es hes H A req hH hin hblank
  set H1 := dockH es H (fun _ => 0) with hH1
  set A1 := install es A tout with hA1
  -- the rounding
  obtain ⟨τ, hτ, hval, hpc, hcell, hmp, hmn, -, -⟩ := round_bound cap v p c (value_small I P req.1 req.2) hcap
  have hstep := (WExec.exec cap hτ).step
  have hR0H : H1 (rs 0) = (wenc cap (parseIn v p c)).H 0 := by
    rw [hshare, hH1, dockH_slot es hes]
    show 0 = (wenc cap (parseIn v p c)).H (sTape (0 : Fin 3))
    rw [wenc_H_s]; simp [parseIn, st3]
  have hR0A : A1 (rs 0) = (wenc cap (parseIn v p c)).A 0 := by
    rw [hshare, hA1, install_slot es hes, hout]
    show ratWord v = (wenc cap (parseIn v p c)).A (sTape (0 : Fin 3))
    rw [wenc_A_s]; simp [parseIn, st3]
  have hRHk : ∀ k, H1 (rs k) = (wenc cap (parseIn v p c)).H k := by
    intro k
    by_cases hk : k = 0
    · subst hk; exact hR0H
    · rw [hH1, dockH_other es H _ (rs k) (fun j hj => hk (hdisj j k hj))]; exact hRH k hk
  have hRAk : ∀ k, A1 (rs k) = (wenc cap (parseIn v p c)).A k := by
    intro k
    by_cases hk : k = 0
    · subst hk; exact hR0A
    · rw [hA1, install_other es A tout (rs k) (fun j hj => hk (hdisj j k hj))]; exact hRA k hk
  have hdock := hstep.dock rs hrs H1 A1 hRHk hRAk
  refine ⟨dockH rs H1 (wenc cap τ).H, install rs A1 (wenc cap τ).A, Step.seq hcall hdock, ⟨τ, hval, hpc, hcell,
    hmp, hmn, fun k => ⟨dockH_slot rs hrs _ _ k, install_slot rs hrs _ _ k⟩⟩, ?_⟩
  intro i hi1 hi2
  refine ⟨?_, ?_⟩
  · rw [dockH_other rs H1 _ i hi2, hH1, dockH_other es H _ i hi1]
  · rw [install_other rs A1 _ i hi2, hA1, install_other es A tout i hi1]

end CallRoundBound

end NearCubicWires.WireExponent3_5.UnionMachine
