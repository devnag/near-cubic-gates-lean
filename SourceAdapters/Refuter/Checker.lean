import SourceAdapters.Refuter.CheckerGood

/-!
# All passes: the checker decides `TraceChecks` (input 7, F01 machine layer, part 15)

SFM78 l.227–233: "This can be checked independently for each tape in turn … Clearly M' runs for
time proportional to the length of the sequence it guesses." `passes` runs pass `i` for every
simulated tape `i < t_M` (the counter is a copy of `T`). `passes_spec`: the flag `ALL` ends set iff it
was set and the decoded guessed trace passes `TraceChecks` on the framed tapes `fr(x), fr(w)` with the
requested acceptance bit — within `t_M · (passCost + 12) + O(t_M)` steps, i.e. `a_M + b_M(n + r + 1)`.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

def passesBody : Pg := .seq pass (WMX.inc rI)

def passes : Pg := .seq (addR rT rTD rTA) (.seq (repK rTD rTI passesBody) (.seq (clr rI) (clr rTD)))

abbrev allR : List (Fin NR) :=
  [rOK, rQ, rH, rWP, rMK, rOFF, rQN, rW0, rW1, rM0, rM1, rCONT, rBIT, rALL, rWS, rI1, rI, rTD, rTI]

theorem se_idx (σ : St) (K : Fin NR) (hK : K ∈ idxR) (n : ℕ) :
    SameExcept (σ.setv rI 0) ((σ.setv K n).setv rI 0) [] idxR := by
  refine ⟨fun x _ => ⟨rfl, rfl⟩, fun x hx => ?_, rfl⟩
  have : x ≠ K := fun e => hx (e ▸ hK)
  simp [Function.update_apply, this]

theorem se_idx' (σ : St) : SameExcept (σ.setv rI 0) σ [] idxR := by
  refine ⟨fun x _ => ⟨rfl, rfl⟩, fun x hx => ?_, rfl⟩
  have : x ≠ rI := fun e => hx (e ▸ by decide)
  simp [Function.update_apply, this]

/-- The invariant after `k` passes. -/
def PassesInv (v : RepairOrdinary.Verifier) (r : ℕ) (wD : List Bool) (p : ℕ) (x w : List Bool) (σ0 : St)
    (k : ℕ) (σ : St) : Prop :=
  σ.val rI = k ∧ k ≤ v.tapeCount ∧
    RestEnc v r ⟨0, by have := v.twoTapes; omega⟩ wD p (σ.setv rI 0) ∧
    (σ.val rALL ≠ 0 ↔ σ0.val rALL ≠ 0 ∧ ∀ j : Fin v.tapeCount, j.val < k →
      passGood v r (v.inputTapes x w) (ptrace wD v.tapeCount p) (decide (σ0.val rVD ≠ 0)) j) ∧
    σ.st sXS = RepairOrdinary.frame x ∧ σ.st sYS = RepairOrdinary.frame w ∧ σ.st sZ = [] ∧
    (0 < k → σ.val rWS = witMoves wD p (pend wD v.tapeCount p)) ∧
    SameExcept σ0 σ passS allR ∧ σ.val rVD = σ0.val rVD

theorem PassesInv.setK {v : RepairOrdinary.Verifier} {r : ℕ} {wD : List Bool} {p : ℕ} {x w : List Bool}
    {σ0 : St} {k : ℕ} {σ : St} (h : PassesInv v r wD p x w σ0 k σ) (K : Fin NR) (hK : K = rTD ∨ K = rTI)
    (n : ℕ) : PassesInv v r wD p x w σ0 k (σ.setv K n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold PassesInv
  rcases hK with rfl | rfl
  · refine ⟨by simp [h1], h2, h3.congr _ (se_idx σ rTD (by decide) n) (by simp), ?_, by simp [h5],
      by simp [h6], by simp [h7], fun hk => by simp [h8 hk], se_setv h9 (by decide) n, by simp [h10]⟩
    simpa using h4
  · refine ⟨by simp [h1], h2, h3.congr _ (se_idx σ rTI (by decide) n) (by simp), ?_, by simp [h5],
      by simp [h6], by simp [h7], fun hk => by simp [h8 hk], se_setv h9 (by decide) n, by simp [h10]⟩
    simpa using h4

set_option maxHeartbeats 400000 in
theorem passes_step (v : RepairOrdinary.Verifier) (r : ℕ) (wD : List Bool) (p : ℕ) (x w : List Bool)
    (σ0 : St) (hcap : 64 * ((VerifierEncoding.code v).length + 4 * wD.length + r + 8) ≤ cap)
    (k : ℕ) (hk : k < v.tapeCount) (σ : St) (hI : PassesInv v r wD p x w σ0 k σ) :
    Runs cap passesBody σ (passCost v r (ptrace wD v.tapeCount p).length + 4)
      (fun τ => PassesInv v r wD p x w σ0 (k + 1) τ ∧ τ.val rTD = σ.val rTD ∧ τ.val rTI = σ.val rTI) := by
  obtain ⟨h1, _, h3, h4, h5, h6, h7, _, h9, h10⟩ := hI
  have hR : RestEnc v r ⟨k, hk⟩ wD p σ := h3.congr ⟨k, hk⟩ (se_idx' σ) h1
  obtain ⟨τ, e1, hR1, hall, hws, hf⟩ := pass_spec cap v r ⟨k, hk⟩ wD p σ hR hcap
  have b3 := tapeCount_le_code v
  have hi1 : τ.val rI = k := by rw [hf.2.1 rI (by decide)]; exact h1
  have e2 := WXExec.inc cap rI τ (by rw [hi1]; omega)
  refine ⟨_, (WXExec.seq e1 e2).mono (by omega), ?_⟩
  refine ⟨?_, by simp [Function.update_apply, hf.2.1 rTD (by decide)],
    by simp [Function.update_apply, hf.2.1 rTI (by decide)]⟩
  unfold PassesInv
  refine ⟨by simp [hi1], by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hR1.congr _ ⟨fun x _ => ⟨rfl, rfl⟩, fun x hx => ?_, rfl⟩ (by simp)
    have : x ≠ rI := fun e => hx (e ▸ by decide)
    simp [Function.update_apply, this]
  · have hsrc := srcOf_eq v σ x w h5 h6 h7 ⟨k, hk⟩
    rw [hsrc] at hall
    have hag := wcopy_agree (σ.st sSIM) ((v.inputTapes x w) ⟨k, hk⟩) r
    have hiff := passOk_iff_good v r (v.inputTapes x w) (ptrace wD v.tapeCount p)
      (decide (σ.val rVD ≠ 0)) ⟨k, hk⟩ _ hag
    rw [h10] at hiff hall
    simp only [WState.setv_val, Function.update_apply, show rALL ≠ rI by decide, if_false, hall]
    by_cases hg : passGood v r (v.inputTapes x w) (ptrace wD v.tapeCount p) (decide (σ0.val rVD ≠ 0)) ⟨k, hk⟩
    · rw [if_pos (hiff.mpr hg), h4]
      constructor
      · rintro ⟨h0, hj⟩
        refine ⟨h0, fun j hj' => ?_⟩
        by_cases hjk : j.val = k
        · have e : j = ⟨k, hk⟩ := Fin.ext hjk
          subst e; exact hg
        · exact hj j (by omega)
      · rintro ⟨h0, hj⟩
        exact ⟨h0, fun j hj' => hj j (by omega)⟩
    · rw [if_neg (fun hh => hg (hiff.mp hh))]
      simp only [ne_eq, not_true_eq_false, false_iff, not_and]
      intro _ hj
      exact hg (hj ⟨k, hk⟩ (by simp))
  · simp [(hf.1 sXS (by decide)).1, h5]
  · simp [(hf.1 sYS (by decide)).1, h6]
  · simp [(hf.1 sZ (by decide)).1, h7]
  · intro _; simp [Function.update_apply, hws]
  · exact se_setv (h9.trans (hf.weaken (by decide) (by decide))) (by decide) _
  · simp [Function.update_apply, hf.2.1 rVD (by decide), h10]

/-- The cost of all passes: `t_M · (passCost + 50) + 20`. -/
def passesCost (v : RepairOrdinary.Verifier) (r n : ℕ) : ℕ := v.tapeCount * (passCost v r n + 50) + 20

set_option maxHeartbeats 400000 in
/-- **All passes** (the BGW tape-by-tape check, SFM78 l.227–233): from a reset state, `ALL` ends set iff
it was set and the decoded guessed trace passes `TraceChecks` on the framed tapes with acceptance bit
`VD`, within `passesCost v r n` steps. -/
theorem passes_spec (v : RepairOrdinary.Verifier) (r : ℕ) (wD : List Bool) (p : ℕ) (x w : List Bool)
    (σ : St) (hR : RestEnc v r ⟨0, by have := v.twoTapes; omega⟩ wD p σ) (hI0 : σ.val rI = 0)
    (hTD : σ.val rTD = 0) (hTI : σ.val rTI = 0) (hx : σ.st sXS = RepairOrdinary.frame x)
    (hy : σ.st sYS = RepairOrdinary.frame w) (hz : σ.st sZ = [])
    (hcap : 64 * ((VerifierEncoding.code v).length + 4 * wD.length + r + 8) ≤ cap) :
    ∃ τ, WXExec cap passes σ τ (passesCost v r (ptrace wD v.tapeCount p).length) ∧
      (τ.val rALL ≠ 0 ↔ σ.val rALL ≠ 0 ∧
        TraceChecks v.machine r (v.inputTapes x w)
          (traceOfD v.machine v.machine.start (ptrace wD v.tapeCount p)) ∧
        v.accepting (controlAfter v.machine.start
          (traceOfD v.machine v.machine.start (ptrace wD v.tapeCount p))) = decide (σ.val rVD ≠ 0)) ∧
      RestEnc v r ⟨0, by have := v.twoTapes; omega⟩ wD p τ ∧
      τ.val rWS = witMoves wD p (pend wD v.tapeCount p) ∧
      τ.st sXS = RepairOrdinary.frame x ∧ τ.st sYS = RepairOrdinary.frame w ∧ τ.st sZ = [] ∧
      τ.val rI = 0 ∧ τ.val rTD = 0 ∧ τ.val rTI = 0 ∧ SameExcept σ τ passS allR := by
  have b3 := tapeCount_le_code v
  have ht2 := v.twoTapes
  have e1 := addR_spec cap (A := rT) (B := rTD) (T := rTA) (by decide) (by decide) (by decide) σ hR.enc.zTA
    (by rw [hTD, hR.enc.t]; lomega)
  obtain ⟨σ1, e1, h1⟩ := exEq cap e1
  have hInv0 : PassesInv v r wD p x w σ 0 σ1 := by
    unfold PassesInv
    refine ⟨by simp [h1, hI0], by omega, ?_, by simp [h1], by simp [h1, hx], by simp [h1, hy], by simp [h1, hz],
      fun h => absurd h (lt_irrefl 0), by rw [h1]; peel, by simp [h1]⟩
    refine hR.congr _ ⟨fun x _ => ⟨by simp [h1], by simp [h1]⟩, fun x hx => ?_, by simp [h1]⟩ (by simp)
    have h1' : x ≠ rI := fun e => hx (e ▸ by decide)
    have h2' : x ≠ rTD := fun e => hx (e ▸ by decide)
    simp [h1, Function.update_apply, h1', h2']
  obtain ⟨τ2, e2, hI2, hTD2, hTI2⟩ := Runs.rep (cap := cap) (K := rTD) (K2 := rTI) (body := passesBody)
    (by decide) (passCost v r (ptrace wD v.tapeCount p).length + 4) v.tapeCount (PassesInv v r wD p x w σ)
    (by lomega) (fun k σ' n h => h.setK rTD (Or.inl rfl) n) (fun k σ' n h => h.setK rTI (Or.inr rfl) n)
    (fun k hk σ' h => passes_step cap v r wD p x w σ hcap k hk σ' h) σ1 hInv0
    (by simp [h1, hTD, hR.enc.t]) (by simp [h1, hTI])
  obtain ⟨g1, _, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hI2
  have e3 := clr_spec cap rI τ2 (by rw [g1]; lomega)
  obtain ⟨τ3, e3, h3⟩ := exEq cap e3
  have e4 := clr_spec cap rTD τ3 (by rw [h3]; simp [hTD2]; lomega)
  obtain ⟨τ4, e4, h4⟩ := exEq cap e4
  refine ⟨τ4, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold passesCost
    simp [h3, h1, g1, hTD2, hR.enc.t, Function.update_apply]
    ring_nf; omega
  · have hall : τ4.val rALL = τ2.val rALL := by simp [h4, h3]
    rw [hall, g4, ← goods_iff]
    constructor
    · rintro ⟨h0, hj⟩; exact ⟨h0, fun j => hj j j.isLt⟩
    · rintro ⟨h0, hj⟩; exact ⟨h0, fun j _ => hj j⟩
  · refine g3.congr _ ⟨fun x _ => ⟨by simp [h4, h3], by simp [h4, h3]⟩, fun x hx => ?_, by simp [h4, h3]⟩
      (by simp [h4, h3])
    have h1' : x ≠ rI := fun e => hx (e ▸ by decide)
    have h2' : x ≠ rTD := fun e => hx (e ▸ by decide)
    simp [h4, h3, Function.update_apply, h1', h2']
  · simp [h4, h3, g8 (by omega)]
  · simp [h4, h3, g5]
  · simp [h4, h3, g6]
  · simp [h4, h3, g7]
  · simp [h4, h3]
  · simp [h4]
  · simp [h4, h3, hTI2]
  · rw [h4, h3]; exact se_setv (se_setv g9 (by decide) _) (by decide) _

end NearCubicGates.Adapters.Refuter.Mach
