import Proof.Gates.CounterMachine.Interval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)

variable {ns nr : ℕ}

/-- The number of loop passes of `redP`. -/
def steps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | a, e + 1 => if a % 2 = 0 then steps (a / 2) e + 1 else 1

theorem steps_pos (a e : ℕ) : 1 ≤ steps a e := by
  cases e with
  | zero => simp [steps]
  | succ e => unfold steps; split_ifs <;> omega

theorem steps_le : ∀ (a e : ℕ), steps a e ≤ e + 1
  | _, 0 => by simp [steps]
  | a, e + 1 => by
    unfold steps
    split_ifs
    · have := steps_le (a / 2) e; omega
    · omega

theorem frame_bit_one (W a : ℕ) (hW : 1 ≤ W) : readTapeBit (frame (binary W a)) 1 = decide (a % 2 = 1) := by
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  simp only [binary, frame, readTapeBit]
  by_cases h : a % 2 = 1 <;> simp [h]

section Red
variable (X : Fin (ns + 1)) (E GO R : Fin nr)

/-- Halve while even and the exponent is positive (`GO` the loop flag). -/
def redP : WMX ns nr :=
  .seq (WMX.inc GO) (.whr GO (.ifr E (.seq (WMX.fwd X) (.ifs X (.seq (WMX.bwd X) (WMX.dec GO))
    (.seq (WMX.bwd X) (.seq (BinW.half X R) (WMX.dec E))))) (WMX.dec GO)))

def redCost (W a e : ℕ) : ℕ := 3 + 1 + (steps a e * (34 * W + 20 + 2) + 1)

theorem redP_spec (cap W : ℕ) (hEG : E ≠ GO) (hER : E ≠ R) (hGR : GO ≠ R) (σ : WState ns nr) (a e : ℕ) (hW : 1 ≤ W)
    (ha : a < 2 ^ W) (hX : NumOn σ X W a) (hE : σ.val E = e) (hG : σ.val GO = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + e + 2 ≤ cap) :
    WXExec cap (redP X E GO R) σ ((σ.sets X (frame (binary W (red a e).1))).setv E (red a e).2) (redCost W a e) := by
  let st : ℕ → ℕ → ℕ → WState ns nr := fun a' e' g => ((σ.sets X (frame (binary W a'))).setv E e').setv GO g
  have hgo : σ.setv GO (σ.val GO + 1) = st a e 1 := by
    apply WState.eq
    · simp [st, hX.2]
    · funext j; by_cases hj : j = X
      · subst hj; simp [st, hX.1]
      · simp [st, Function.update_of_ne hj]
    · funext r; by_cases h1 : r = GO
      · subst h1; simp [st, hG]
      · by_cases h2 : r = E
        · subst h2; simp [st, Function.update_of_ne h1, hE]
        · simp [st, Function.update_of_ne h1, Function.update_of_ne h2]
    · rfl
  have i1 := WXExec.inc cap GO σ (by rw [hG]; omega)
  rw [hgo] at i1
  -- the loop invariant: `k` passes left
  let Inv : ℕ → WState ns nr → Prop := fun k τ => ∃ a' e', a' < 2 ^ W ∧ e' ≤ e ∧ red a' e' = red a e ∧
    ((k = 0 ∧ τ = st a' e' 0 ∧ (a', e') = red a e) ∨ (k ≠ 0 ∧ τ = st a' e' 1 ∧ k = steps a' e'))
  have hbody : ∀ k τ, Inv (k + 1) τ → τ.val GO ≠ 0 ∧ Runs cap (.ifr E (.seq (WMX.fwd X) (.ifs X
      (.seq (WMX.bwd X) (WMX.dec GO)) (.seq (WMX.bwd X) (.seq (BinW.half X R) (WMX.dec E))))) (WMX.dec GO)) τ
      (34 * W + 20) (Inv k) := by
    rintro k τ ⟨a', e', ha', he', hred, ⟨hk, -⟩ | ⟨-, rfl, hk⟩⟩
    · omega
    have vG : (st a' e' 1).val GO = 1 := by simp [st]
    have vE : (st a' e' 1).val E = e' := by simp [st, Function.update_of_ne hEG]
    have vR : (st a' e' 1).val R = 0 := by simp [st, Function.update_of_ne hGR.symm, Function.update_of_ne hER.symm, hR]
    refine ⟨by rw [vG]; omega, ?_⟩
    cases e' with
    | zero =>
      -- exponent `0`: stop
      have d := WXExec.dec cap GO (st a' 0 1) (by rw [vG]; omega)
      rw [vG] at d
      refine (Runs.ifrF vE (Runs.of d ?_)).cost (by omega)
      have hk0 : k = 0 := by simp [steps] at hk; omega
      refine ⟨a', 0, ha', he', hred, Or.inl ⟨hk0, ?_, by rw [← hred]; rfl⟩⟩
      simp only [st, wsetv_setv]
    | succ e'' =>
      have hX1 : (st a' (e'' + 1) 1).st X = frame (binary W a') := by simp [st]
      have hXh : (st a' (e'' + 1) 1).sh X = σ.sh X := by simp [st]
      have f := WXExec.fwd cap X (st a' (e'' + 1) 1)
      rw [hXh, hX.2] at f
      set τ1 := (st a' (e'' + 1) 1).seth X (0 + 1) with hτ1
      have hbit : wbit τ1 X = decide (a' % 2 = 1) := by
        unfold wbit; simp only [hτ1, WState.seth_st, WState.seth_sh, Function.update_self, hX1]
        exact frame_bit_one W a' hW
      have b := WXExec.bwd cap X τ1
      have eb : τ1.seth X (τ1.sh X - 1) = st a' (e'' + 1) 1 := by
        apply WState.eq
        · funext j; by_cases hj : j = X
          · subst hj; simp [hτ1, st, hX.2]
          · simp [hτ1, Function.update_of_ne hj]
        · simp [hτ1]
        · simp [hτ1]
        · simp [hτ1]
      rw [eb] at b
      by_cases hodd : a' % 2 = 1
      · -- odd: stop
        have d := WXExec.dec cap GO (st a' (e'' + 1) 1) (by rw [vG]; omega)
        rw [vG] at d
        refine (Runs.ifrT (by rw [vE]; omega) (Runs.seqE f (Runs.ifsT (by rw [hbit]; simp [hodd])
          (Runs.seqE b (Runs.of d ?_))))).cost (by omega)
        have hk0 : k = 0 := by simp [steps, hodd] at hk; omega
        refine ⟨a', e'' + 1, ha', he', hred, Or.inl ⟨hk0, ?_, ?_⟩⟩
        · simp only [st, wsetv_setv]
        · rw [← hred]; simp [red, hodd]
      · -- even: halve
        have hev : a' % 2 = 0 := by omega
        have hh := BinW.half_spec (cap := cap) (A := X) (R := R) (W := W) (st a' (e'' + 1) 1) a'
          ⟨hX1, by rw [hXh, hX.2]⟩ vR ha' (by omega)
        set τ2 := (st a' (e'' + 1) 1).sets X (frame (binary W (a' / 2))) with hτ2
        have vE2 : τ2.val E = e'' + 1 := by simp [hτ2, st, Function.update_of_ne hEG]
        have d := WXExec.dec cap E τ2 (by rw [vE2]; omega)
        rw [vE2] at d
        refine (Runs.ifrT (by rw [vE]; omega) (Runs.seqE f (Runs.ifsF (by rw [hbit]; simp [hodd])
          (Runs.seqE b (Runs.seqE hh (Runs.of d ?_)))))).cost (by omega)
        have hk' : k = steps (a' / 2) e'' := by simp [steps, hev] at hk; omega
        have hred' : red (a' / 2) e'' = red a e := by rw [← hred]; simp [red, hev]
        refine ⟨a' / 2, e'', lt_of_le_of_lt (Nat.div_le_self _ _) ha', by omega, hred', ?_⟩
        have hτeq : τ2.setv E (e'' + 1 - 1) = st (a' / 2) e'' 1 := by
          apply WState.eq
          · simp [hτ2, st]
          · funext j; by_cases hj : j = X
            · subst hj; simp [hτ2, st]
            · simp [hτ2, st, Function.update_of_ne hj]
          · funext r; by_cases h1 : r = E
            · subst h1; simp [hτ2, st, Function.update_of_ne hEG]
            · by_cases h2 : r = GO
              · subst h2; simp [hτ2, st, Function.update_of_ne h1]
              · simp [hτ2, st, Function.update_of_ne h1, Function.update_of_ne h2]
          · simp [hτ2, st]
        rw [hτeq]
        by_cases hk0 : k = 0
        · exact absurd hk' (by have := steps_pos (a' / 2) e''; omega)
        · exact Or.inr ⟨hk0, rfl, hk'⟩
  have hexit : ∀ τ, Inv 0 τ → τ.val GO = 0 ∧
      τ = (σ.sets X (frame (binary W (red a e).1))).setv E (red a e).2 := by
    rintro τ ⟨a', e', -, -, -, ⟨-, rfl, hae⟩ | ⟨h0, -⟩⟩
    · refine ⟨by simp [st], ?_⟩
      have h1 : (red a e).1 = a' := by rw [← hae]
      have h2 : (red a e).2 = e' := by rw [← hae]
      rw [h1, h2]
      apply WState.eq
      · simp [st]
      · simp [st]
      · funext r; by_cases h : r = GO
        · subst h; simp [st, Function.update_of_ne hEG.symm, hG]
        · simp [st, Function.update_of_ne h]
      · simp [st]
    · exact absurd rfl h0
  have hl := Runs.whr (cap := cap) (r := GO) Inv (34 * W + 20)
    (fun τ => τ = (σ.sets X (frame (binary W (red a e).1))).setv E (red a e).2) hexit hbody (steps a e) (st a e 1)
    ⟨a, e, ha, le_rfl, rfl, Or.inr ⟨by have := steps_pos a e; omega, rfl, rfl⟩⟩
  obtain ⟨τ, el, rfl⟩ := hl
  exact WXExec.seq i1 el

end Red

/-! ## Emitting a constant word -/

def emitL (O : Fin (ns + 1)) : List Bool → WMX ns nr
  | [] => WMX.skip
  | b :: bs => .seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Out.P5.emit O b)) (emitL O bs)

theorem emitL_spec (cap : ℕ) (O : Fin (ns + 1)) : ∀ (bs : List Bool) (σ : WState ns nr),
    σ.sh O = (σ.st O).length →
    WXExec cap (emitL O bs) σ ((σ.sets O (σ.st O ++ bs)).seth O ((σ.st O).length + bs.length)) (4 * bs.length)
  | [], σ, h => by
    refine WXExec.cast cap (WXExec.skip cap σ) ?_ (by simp)
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp [h]
      · simp [Function.update_of_ne hj]
    · funext j; by_cases hj : j = O
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · simp
    · simp
  | b :: bs, σ, h => by
    have e1 := NearCubicWires.WireExponent3_5.FinalPass.Out.P5.emit_spec cap O b σ h
    set σ1 := (σ.sets O (σ.st O ++ [b])).seth O ((σ.st O).length + 1) with hσ1
    have e2 := emitL_spec cap O bs σ1 (by simp [hσ1])
    refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) e2) ?_ (by simp; omega)
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp [hσ1]; ring
      · simp [hσ1, Function.update_of_ne hj]
    · funext j; by_cases hj : j = O
      · subst hj; simp [hσ1]
      · simp [hσ1, Function.update_of_ne hj]
    · simp [hσ1]
    · simp [hσ1]

theorem natWord_zero : natWord 0 = [true, false, false] := by decide

end NearCubicGates.Close.CounterMachine
