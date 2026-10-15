import Proof.Gates.Solve.Out4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open NearCubicWires.RepairRepresentation (natWord)

/-! ## Registers stay below the cap -/

theorem wexec_val_le {ns nr cap : ℕ} {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    (∀ r, σ.val r ≤ cap) → ∀ r, τ.val r ≤ cap := by
  induction h with
  | skip => exact id
  | inc r σ hc =>
    intro hσ q
    by_cases hq : q = r
    · subst hq; simp; omega
    · simp [Function.update_of_ne hq]; exact hσ q
  | dec r σ _ =>
    intro hσ q
    by_cases hq : q = r
    · subst hq; simp; have := hσ q; omega
    · simp [Function.update_of_ne hq]; exact hσ q
  | fwd i σ => intro hσ q; simpa using hσ q
  | bwd i σ => intro hσ q; simpa using hσ q
  | wr i b σ => intro hσ q; simpa using hσ q
  | setc c σ => intro hσ q; simpa using hσ q
  | seq _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | ifrT _ _ ih => exact ih
  | ifrF _ _ ih => exact ih
  | ifsT _ _ ih => exact ih
  | ifsF _ _ ih => exact ih
  | whrF _ => exact id
  | whrT _ _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | whsF _ => exact id
  | whsT _ _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | mono _ _ ih => exact ih

theorem WXExec.val_le {ns nr cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) :
    (∀ r, σ.val r ≤ cap) → ∀ r, τ.val r ≤ cap := by
  induction h with
  | wm e => exact wexec_val_le e
  | mach σ _ _ => exact id
  | seq _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | ifrT _ _ ih => exact ih
  | ifrF _ _ ih => exact ih
  | ifsT _ _ ih => exact ih
  | ifsF _ _ ih => exact ih
  | whrF _ => exact id
  | whrT _ _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | whsF _ => exact id
  | whsT _ _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | mono _ _ ih => exact ih

/-! ## Clearing every register -/

def clearAll : List Reg → WMX NS NR
  | [] => WMX.skip
  | r :: rs => .seq (.wm (WM.clear r)) (clearAll rs)

theorem clearAll_spec (cap : ℕ) : ∀ (rs : List Reg) (σ : MS), (∀ r, σ.val r ≤ cap) →
    ∃ τ, WXExec cap (clearAll rs) σ τ (rs.length * (3 * cap + 2)) ∧ τ.sh = σ.sh ∧ τ.st = σ.st ∧
      ∀ r, τ.val r = if r ∈ rs then 0 else σ.val r
  | [], σ, _ => ⟨σ, WXExec.mono (WXExec.skip cap σ) (by simp), rfl, rfl, fun r => by simp⟩
  | r :: rs, σ, hσ => by
    have e1 := WXExec.wm (wclear_spec (cap := cap) r (σ.val r) σ rfl (hσ r))
    obtain ⟨τ, e2, hsh, hst, hv⟩ := clearAll_spec cap rs (σ.setv r 0) (fun q => by
      by_cases hq : q = r
      · subst hq; simp
      · simp [Function.update_of_ne hq]; exact hσ q)
    refine ⟨τ, WXExec.mono (WXExec.seq e1 e2) ?_, by rw [hsh]; rfl, by rw [hst]; rfl, fun q => ?_⟩
    · have := hσ r; simp only [List.length_cons]; nlinarith
    · rw [hv q]
      by_cases hq : q = r
      · subst hq; simp
      · by_cases hm : q ∈ rs
        · simp [hm]
        · simp [hm, hq, Function.update_of_ne hq]

/-! ## Rewinding the output -/

abbrev rRW : Reg := 59

def rewBody : WMX NS NR := .seq (addR rR2 rCS rTa) (.wm (WM.rewind sOUT rCS))

def rewBodyCost (W : ℕ) : ℕ := 18 * (2 * (W + 1) + 1) + 3 + 1 + (5 * (2 * (W + 1) + 1) + 1)

theorem opRewO (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (hR2 : σ0.val rR2 = 2 * (W + 1) + 1)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap rewBody σ (rewBodyCost W) (fun τ => At (σ0.seth sOUT (σ0.sh sOUT - (2 * (W + 1) + 1))) τ W v) := by
  have hCS : σ.val rCS = 0 := h.zero (by decide)
  have hR2' : σ.val rR2 = 2 * (W + 1) + 1 := by rw [h.val (by decide), hR2]
  have e1 := addR_spec cap (A := rR2) (B := rCS) (T := rTa) (by decide) (by decide) (by decide) σ (h.zero (by decide))
    (by rw [hCS, hR2']; omega)
  rw [hCS, hR2', Nat.zero_add] at e1
  have e2 := wrewind_spec (cap := cap) sOUT rCS (2 * (W + 1) + 1) (σ.setv rCS (2 * (W + 1) + 1)) (by simp)
    (by simp; omega)
  refine Runs.of (WXExec.seq e1 (WXExec.wm e2)) ?_
  have e : ((σ.setv rCS (2 * (W + 1) + 1)).setv rCS 0).seth sOUT ((σ.setv rCS (2 * (W + 1) + 1)).sh sOUT -
      (2 * (W + 1) + 1)) = σ.seth sOUT (σ.sh sOUT - (2 * (W + 1) + 1)) := by
    apply WState.eq
    · simp
    · simp
    · funext q; by_cases hq : q = rCS
      · subst hq; simp [hCS]
      · simp [Function.update_of_ne hq]
    · simp
  rw [e, h.sh (by decide)]
  exact h.sethO (by decide) _

def rewOutP : WMX NS NR :=
  .seq (addR rNN rRW rTa) (.seq (WMX.inc rRW) (.whr rRW (.seq (WMX.dec rRW) (.seq rewBody (.seq rewBody rewBody)))))

def rewOutCost (W n : ℕ) : ℕ :=
  18 * n + 3 + 1 + (3 + 1 + ((n + 1) * (rewBodyCost W + 1 + (rewBodyCost W + 1 + rewBodyCost W) + 4) + 1))

/-- The rewind-loop invariant after `k` rounds. -/
def WInv (σA : MS) (W : ℕ) (v : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1, At σ1 τ W v ∧ σ1.sh sOUT = σA.sh sOUT - k * (3 * (2 * (W + 1) + 1)) ∧ σ1.st sOUT = σA.st sOUT ∧
    SameExcept σA σ1 [sOUT] [rRW]

theorem rewOut_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {n : ℕ} (hRW : σ0.val rRW = 0)
    (hNN : σ0.val rNN = n) (hR2 : σ0.val rR2 = 2 * (W + 1) + 1) (hL : σ0.sh sOUT ≤ 3 * (n + 1) * (2 * (W + 1) + 1))
    (hcap : n + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap rewOutP σ (rewOutCost W n) (fun τ => ∃ σ1, At σ1 τ W v ∧ σ1.sh sOUT = 0 ∧ σ1.st sOUT = σ0.st sOUT ∧
      SameExcept σ0 σ1 [sOUT] [rRW]) := by
  refine Runs.seq ((opAddR cap h (A := rNN) (B := rRW) (by decide) (by decide) (by decide)
    (by rw [hRW, hNN]; omega)).cost (show 18 * σ0.val rNN + 3 ≤ 18 * n + 3 by rw [hNN])) (fun τ1 h1 => ?_)
  rw [hRW, hNN, Nat.zero_add] at h1
  refine Runs.seq (opIncR cap h1 (r := rRW) (by decide) (by simp; omega)) (fun τ2 h2 => ?_)
  set σA := (σ0.setv rRW n).setv rRW ((σ0.setv rRW n).val rRW + 1) with hσA
  have hAn : σA.val rRW = n + 1 := by simp [hσA]
  have hfrA : SameExcept σ0 σA [sOUT] [rRW] :=
    (sameExcept_setv σ0 (by simp) _).trans (sameExcept_setv _ (by simp) _)
  have hR2A : σA.val rR2 = 2 * (W + 1) + 1 := by rw [hfrA.val (by decide), hR2]
  set N := 2 * (W + 1) + 1 with hN
  have hloop := Runs.count (cap := cap) (K := rRW) (body := .seq rewBody (.seq rewBody rewBody))
    (rewBodyCost W + 1 + (rewBodyCost W + 1 + rewBodyCost W)) (n + 1) (WInv σA W v) (by omega)
    (fun k _ τ ⟨σ1, hτ, hsh, hst, hfr⟩ _ => by
      have hτ' := hτ.setv (r := rRW) (by decide) (n + 1 - k - 1)
      have hR : ∀ (ρ : MS), (∀ r, r ≠ rRW → ρ.val r = σA.val r) → ρ.val rR2 = N := fun ρ hρ => by
        rw [hρ _ (by decide), hR2A]
      set σ2 := σ1.setv rRW (n + 1 - k - 1) with hσ2
      have hv2 : ∀ r, r ≠ rRW → σ2.val r = σA.val r := fun r hr => by
        rw [hσ2, WState.setv_val, Function.update_of_ne hr, hfr.val (by simp [hr])]
      refine Runs.seq (opRewO cap hτ' (hR σ2 hv2) (by omega)) (fun τ3 h3 => ?_)
      refine Runs.seq (opRewO cap h3 (by simp; exact hR σ2 hv2) (by omega)) (fun τ4 h4 => ?_)
      refine (opRewO cap h4 (by simp; exact hR σ2 hv2) (by omega)).post (fun τ5 h5 =>
        ⟨⟨_, h5, ?_, ?_, ?_⟩, ?_⟩)
      · simp [hσ2, hsh]
        rw [Nat.sub_sub, Nat.sub_sub, Nat.sub_sub]; congr 1; ring
      · simp [hσ2, hst]
      · exact hfr.trans ((sameExcept_setv σ1 (by simp) _).trans (((sameExcept_seth _ (by simp) _).trans
          (sameExcept_seth _ (by simp) _)).trans (sameExcept_seth _ (by simp) _)))
      · rw [h5.val (by decide)]; simp [hσ2]) τ2
    ⟨σA, h2, by simp, rfl, SameExcept.refl _ _ _⟩ (by rw [h2.val (by decide), hAn])
  refine hloop.post (fun τ ⟨⟨σ1, h3, hsh, hst, hfr⟩, _⟩ => ⟨σ1, h3, ?_, ?_, hfrA.trans hfr⟩)
  · rw [hsh]
    have : σA.sh sOUT = σ0.sh sOUT := by simp [hσA]
    rw [this]; apply Nat.sub_eq_zero_of_le; nlinarith
  · rw [hst]; simp [hσA]

/-! ## The output length -/

theorem natWord_len_le (x W : ℕ) (hx : x < 2 ^ (W + 1)) : (natWord x).length ≤ 2 * (W + 1) + 1 := by
  rw [natWord_len]; have := natBitLength_le' x W hx; omega

theorem flatMap_len_le {α : Type} (f : α → List Bool) (B : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length ≤ B) → (l.flatMap f).length ≤ l.length * B
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := flatMap_len_le f B l (fun b hb => h b (by simp [hb]))
    nlinarith

theorem outW_length (a : ℕ → ℕ → ℤ) (D : ℤ) (m n W : ℕ) (hD : D.natAbs < 2 ^ (W + 1))
    (hy : ∀ j < n, (a (m + j) n).natAbs < 2 ^ (W + 1)) (hn : n < 2 ^ (W + 1)) :
    (outW a D m n).length ≤ 3 * (n + 1) * (2 * (W + 1) + 1) := by
  unfold outW
  split_ifs
  · rw [natWord_flag_len 0 (by omega)]; nlinarith
  · have he : ∀ j ∈ List.range n, (entW (a (m + j) n) D).length ≤ 3 + 2 * (2 * (W + 1) + 1) := by
      intro j hj
      have hj' := List.mem_range.mp hj
      unfold entW
      simp only [List.length_append]
      have hneg : negB (a (m + j) n) D ≤ 1 := by unfold negB; split_ifs <;> omega
      rw [natWord_flag_len _ hneg]
      have h1 := natWord_len_le ((a (m + j) n).natAbs / Nat.gcd D.natAbs (a (m + j) n).natAbs) W
        (lt_of_le_of_lt (Nat.div_le_self _ _) (hy j hj'))
      have h2 := natWord_len_le (D.natAbs / Nat.gcd D.natAbs (a (m + j) n).natAbs) W
        (lt_of_le_of_lt (Nat.div_le_self _ _) hD)
      omega
    have hf := flatMap_len_le _ _ _ he
    rw [List.length_range] at hf
    simp only [List.length_append]
    rw [natWord_flag_len 1 (by omega)]
    have := natWord_len_le n W hn
    nlinarith

end NearCubicGates.Close.Solve
