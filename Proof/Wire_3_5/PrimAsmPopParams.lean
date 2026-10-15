import Proof.Wire_3_5.PrimAsmPopCap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopParams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW

variable {ns nr : ℕ} (cap : ℕ)

/-- The level block inside the params registers (`0 S`, `1 J`, `2 j`, `3 W`, `4 P`, scratch). -/
def yV : Fin 24 ↪ Fin 32 := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The sum of the windows below the top level. -/
def lbSum (S J : ℕ) : ℕ := ((List.range J).map fun j => 4 * winAt S J j).sum

section Loops
variable (Y : Fin 32 ↪ Fin nr)

/-- One level of the list bound (`27 = j`): `acc (24) += 4·W'_j`. -/
def lbBody : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Y 27) (Y 2) (Y 28))
  (.seq (levelVals (yV.trans Y))
  (.seq (ParseNat.addTo (Y 3) (Y 24) (Y 28))
  (.seq (ParseNat.addTo (Y 3) (Y 24) (Y 28))
  (.seq (ParseNat.addTo (Y 3) (Y 24) (Y 28))
  (.seq (ParseNat.addTo (Y 3) (Y 24) (Y 28))
  (.seq (WM.clear (Y 3))
  (.seq (WM.clear (Y 4))
  (WM.clear (Y 2)))))))))

/-- A bound on one level's cost. -/
def lvlBound (cap : ℕ) : ℕ := 6 * phBound cap + 200 * cap + 200

theorem lbBody_spec (τ : WState ns nr) (S J j a : ℕ) (h0 : τ.val (Y 0) = S) (h1 : τ.val (Y 1) = J)
    (h27 : τ.val (Y 27) = j) (hjJ : j ≤ J) (hz : ∀ i : Fin 32, 2 ≤ i.val → i.val ≤ 23 → τ.val (Y i) = 0)
    (h28 : τ.val (Y 28) = 0) (h24 : τ.val (Y 24) = a) (hcap : lvCap S J j ≤ cap)
    (hac : a + 4 * winAt S J j ≤ cap) (hjc : j ≤ cap) :
    ∃ n, WExec cap (lbBody Y) τ (τ.setv (Y 24) (a + 4 * winAt S J j)) n ∧ n ≤ lvlBound cap := by
  have hR : ∀ i k : Fin 32, Y i = Y k ↔ i = k := fun i k => Y.injective.eq_iff
  have hne : ∀ {i k : Fin 32}, i ≠ k → Y i ≠ Y k := fun h => Y.injective.ne h
  have hV : ∀ i : Fin 24, (yV.trans Y) i = Y ⟨i.val, by omega⟩ := fun i => rfl
  have hV3 : (yV.trans Y) 3 = Y 3 := rfl
  have hV4 : (yV.trans Y) 4 = Y 4 := rfl
  have h2z := hz 2 (by decide) (by decide)
  have h3z := hz 3 (by decide) (by decide)
  have h4z := hz 4 (by decide) (by decide)
  obtain ⟨w, hw⟩ : ∃ x, x = winAt S J j := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ x, x = 2 ^ Nat.clog 2 (2 * w + 1) := ⟨_, rfl⟩
  rw [← hw] at hac ⊢
  have hwl := winAt_le S J j
  have hcl := pow_clog_le (2 * w + 1) (by omega)
  unfold lvCap at hcap
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Y 27) (Y 2) (Y 28) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h2z h28 (by omega)
  rw [h27] at e1
  obtain ⟨n2, e2, b2⟩ := levelVals_spec cap (yV.trans Y) (τ.setv (Y 2) j) S J j
    (by rw [show (yV.trans Y) 0 = Y 0 from rfl]; simp [hR, h0])
    (by rw [show (yV.trans Y) 1 = Y 1 from rfl]; simp [hR, h1]) (by rw [show (yV.trans Y) 2 = Y 2 from rfl]; simp) hjJ
    (fun i hi => by
      have h2 : (⟨i.val, by omega⟩ : Fin 32) ≠ 2 := Fin.ne_of_val_ne (by show i.val ≠ 2; omega)
      rw [hV i, wsetv_val_ne _ _ (hne h2)]
      exact hz _ (by show 2 ≤ i.val; omega) (by show i.val ≤ 23; omega))
    (by unfold lvCap; exact hcap)
  rw [hV3, hV4, ← hw, ← hp] at e2
  set ρ := ((τ.setv (Y 2) j).setv (Y 3) w).setv (Y 4) p with hρ
  have hρ3 : ρ.val (Y 3) = w := by simp [hρ, hR]
  have hρ28 : ρ.val (Y 28) = 0 := by simp [hρ, hR, h28]
  have e3 := ParseNat.addTo_spec cap (Y 3) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide)) ρ hρ28
    (by rw [hρ3]; omega) (by rw [hρ3]; simp [hρ, hR, h24]; omega)
  rw [hρ3, show ρ.val (Y 24) = a by simp [hρ, hR, h24]] at e3
  have e4 := ParseNat.addTo_spec cap (Y 3) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (Y 24) (a + w)) (by simp [hR, hρ28]) (by simp [hR, hρ3]; omega) (by simp [hR, hρ3]; omega)
  rw [wsetv_setv, show (ρ.setv (Y 24) (a + w)).val (Y 24) + (ρ.setv (Y 24) (a + w)).val (Y 3) = a + 2 * w by
    simp [hR, hρ3]; omega, show (ρ.setv (Y 24) (a + w)).val (Y 3) = w by simp [hR, hρ3]] at e4
  have e5 := ParseNat.addTo_spec cap (Y 3) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (Y 24) (a + 2 * w)) (by simp [hR, hρ28]) (by simp [hR, hρ3]; omega) (by simp [hR, hρ3]; omega)
  rw [wsetv_setv, show (ρ.setv (Y 24) (a + 2 * w)).val (Y 24) + (ρ.setv (Y 24) (a + 2 * w)).val (Y 3) = a + 3 * w by
    simp [hR, hρ3]; omega, show (ρ.setv (Y 24) (a + 2 * w)).val (Y 3) = w by simp [hR, hρ3]] at e5
  have e6 := ParseNat.addTo_spec cap (Y 3) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (Y 24) (a + 3 * w)) (by simp [hR, hρ28]) (by simp [hR, hρ3]; omega) (by simp [hR, hρ3]; omega)
  rw [wsetv_setv, show (ρ.setv (Y 24) (a + 3 * w)).val (Y 24) + (ρ.setv (Y 24) (a + 3 * w)).val (Y 3) = a + 4 * w by
    simp [hR, hρ3]; omega, show (ρ.setv (Y 24) (a + 3 * w)).val (Y 3) = w by simp [hR, hρ3]] at e6
  have e7 := wclear_spec cap (Y 3) w (ρ.setv (Y 24) (a + 4 * w)) (by simp [hR, hρ3]) (by simp [hR, hρ3]; omega)
  have e8 := wclear_spec cap (Y 4) p ((ρ.setv (Y 24) (a + 4 * w)).setv (Y 3) 0) (by simp [hρ, hR])
    (by simp [hρ, hR]; omega)
  have e9 := wclear_spec cap (Y 2) j (((ρ.setv (Y 24) (a + 4 * w)).setv (Y 3) 0).setv (Y 4) 0) (by simp [hρ, hR])
    (by simp [hρ, hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [hρ, WState.setv_val, Function.update_apply]
      by_cases x2 : x = Y 2
      · subst x2; simp [hR, h2z]
      · by_cases x3 : x = Y 3
        · subst x3; simp [hR, h3z]
        · by_cases x4 : x = Y 4
          · subst x4; simp [hR, h4z]
          · by_cases x24 : x = Y 24
            · subst x24; simp [hR]
            · simp [x2, x3, x4, x24]
    · rfl
  · unfold lvlBound
    omega

end Loops

section Loops2
variable (Y : Fin 32 ↪ Fin nr)

/-- One level of the table word's length (`27 = j`): `acc (24) += W'_j + pow W'_j + L + 3` (`26 = L`). -/
def lwBody : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Y 27) (Y 2) (Y 28))
  (.seq (levelVals (yV.trans Y))
  (.seq (ParseNat.addTo (Y 3) (Y 24) (Y 28))
  (.seq (ParseNat.addTo (Y 4) (Y 24) (Y 28))
  (.seq (ParseNat.addTo (Y 26) (Y 24) (Y 28))
  (.seq (StarNums.incN (Y 24) 3)
  (.seq (WM.clear (Y 3))
  (.seq (WM.clear (Y 4))
  (WM.clear (Y 2)))))))))

theorem lwBody_spec (τ : WState ns nr) (S J j L a : ℕ) (h0 : τ.val (Y 0) = S) (h1 : τ.val (Y 1) = J)
    (h27 : τ.val (Y 27) = j) (hjJ : j ≤ J) (hz : ∀ i : Fin 32, 2 ≤ i.val → i.val ≤ 23 → τ.val (Y i) = 0)
    (h28 : τ.val (Y 28) = 0) (h24 : τ.val (Y 24) = a) (h26 : τ.val (Y 26) = L) (hcap : lvCap S J j ≤ cap)
    (hac : a + (winAt S J j + 2 ^ Nat.clog 2 (2 * winAt S J j + 1) + L + 3) ≤ cap) (hjc : j ≤ cap) :
    ∃ n, WExec cap (lwBody Y) τ
      (τ.setv (Y 24) (a + (winAt S J j + 2 ^ Nat.clog 2 (2 * winAt S J j + 1) + L + 3))) n ∧ n ≤ lvlBound cap := by
  have hR : ∀ i k : Fin 32, Y i = Y k ↔ i = k := fun i k => Y.injective.eq_iff
  have hne : ∀ {i k : Fin 32}, i ≠ k → Y i ≠ Y k := fun h => Y.injective.ne h
  have hV : ∀ i : Fin 24, (yV.trans Y) i = Y ⟨i.val, by omega⟩ := fun i => rfl
  have hV3 : (yV.trans Y) 3 = Y 3 := rfl
  have hV4 : (yV.trans Y) 4 = Y 4 := rfl
  have h2z := hz 2 (by decide) (by decide)
  have h3z := hz 3 (by decide) (by decide)
  have h4z := hz 4 (by decide) (by decide)
  obtain ⟨w, hw⟩ : ∃ x, x = winAt S J j := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ x, x = 2 ^ Nat.clog 2 (2 * w + 1) := ⟨_, rfl⟩
  rw [← hw, ← hp] at hac ⊢
  unfold lvCap at hcap
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Y 27) (Y 2) (Y 28) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h2z h28 (by omega)
  rw [h27] at e1
  obtain ⟨n2, e2, b2⟩ := levelVals_spec cap (yV.trans Y) (τ.setv (Y 2) j) S J j
    (by rw [show (yV.trans Y) 0 = Y 0 from rfl]; simp [hR, h0])
    (by rw [show (yV.trans Y) 1 = Y 1 from rfl]; simp [hR, h1]) (by rw [show (yV.trans Y) 2 = Y 2 from rfl]; simp) hjJ
    (fun i hi => by
      have h2 : (⟨i.val, by omega⟩ : Fin 32) ≠ 2 := Fin.ne_of_val_ne (by show i.val ≠ 2; omega)
      rw [hV i, wsetv_val_ne _ _ (hne h2)]
      exact hz _ (by show 2 ≤ i.val; omega) (by show i.val ≤ 23; omega))
    (by unfold lvCap; exact hcap)
  rw [hV3, hV4, ← hw, ← hp] at e2
  set ρ := ((τ.setv (Y 2) j).setv (Y 3) w).setv (Y 4) p with hρ
  have hρ28 : ρ.val (Y 28) = 0 := by simp [hρ, hR, h28]
  have e3 := ParseNat.addTo_spec cap (Y 3) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide)) ρ hρ28
    (by simp [hρ, hR]; omega) (by simp [hρ, hR, h24]; omega)
  rw [show ρ.val (Y 24) + ρ.val (Y 3) = a + w by simp [hρ, hR, h24], show ρ.val (Y 3) = w by simp [hρ, hR]] at e3
  have e4 := ParseNat.addTo_spec cap (Y 4) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (Y 24) (a + w)) (by simp [hR, hρ28]) (by simp [hρ, hR]; omega) (by simp [hρ, hR]; omega)
  rw [wsetv_setv, show (ρ.setv (Y 24) (a + w)).val (Y 24) + (ρ.setv (Y 24) (a + w)).val (Y 4) = a + w + p by
    simp [hρ, hR], show (ρ.setv (Y 24) (a + w)).val (Y 4) = p by simp [hρ, hR]] at e4
  have e5 := ParseNat.addTo_spec cap (Y 26) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (ρ.setv (Y 24) (a + w + p)) (by simp [hR, hρ28]) (by simp [hρ, hR, h26]; omega) (by simp [hρ, hR, h26]; omega)
  rw [wsetv_setv, show (ρ.setv (Y 24) (a + w + p)).val (Y 24) + (ρ.setv (Y 24) (a + w + p)).val (Y 26) = a + w + p + L
    by simp [hρ, hR, h26], show (ρ.setv (Y 24) (a + w + p)).val (Y 26) = L by simp [hρ, hR, h26]] at e5
  have e6 := StarNums.incN_spec cap (Y 24) 3 (ρ.setv (Y 24) (a + w + p + L)) (by simp; omega)
  rw [wsetv_setv, show (ρ.setv (Y 24) (a + w + p + L)).val (Y 24) + 3 = a + (w + p + L + 3) by simp; omega] at e6
  have e7 := wclear_spec cap (Y 3) w (ρ.setv (Y 24) (a + (w + p + L + 3))) (by simp [hρ, hR]) (by simp [hρ, hR]; omega)
  have e8 := wclear_spec cap (Y 4) p ((ρ.setv (Y 24) (a + (w + p + L + 3))).setv (Y 3) 0) (by simp [hρ, hR])
    (by simp [hρ, hR]; omega)
  have e9 := wclear_spec cap (Y 2) j (((ρ.setv (Y 24) (a + (w + p + L + 3))).setv (Y 3) 0).setv (Y 4) 0)
    (by simp [hρ, hR]) (by simp [hρ, hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [hρ, WState.setv_val, Function.update_apply]
      by_cases x2 : x = Y 2
      · subst x2; simp [hR, h2z]
      · by_cases x3 : x = Y 3
        · subst x3; simp [hR, h3z]
        · by_cases x4 : x = Y 4
          · subst x4; simp [hR, h4z]
          · by_cases x24 : x = Y 24
            · subst x24; simp [hR]
            · simp [x2, x3, x4, x24]
    · rfl
  · unfold lvlBound
    have hwl := winAt_le S J j
    have hcl := pow_clog_le (2 * w + 1) (by omega)
    omega

end Loops2

/-! ## The loops -/

/-- The list bound's sum. -/
def lbSumF (S J : ℕ) : ℕ := ∑ j ∈ Finset.range J, 4 * winAt S J j

/-- The table word's levels' sum at row length `L`. -/
def lwSumF (S J L : ℕ) : ℕ := ∑ j ∈ Finset.range (J + 1), (winAt S J j + 2 ^ Nat.clog 2 (2 * winAt S J j + 1) + L + 3)

section Loops3
variable (Y : Fin 32 ↪ Fin nr)

/-- **The list bound**: `acc += Σ_{j<J} 4·W'_j + 1` (`27` the level counter). -/
def lbW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Y 1) (Y 27) (Y 28))
  (.seq (.whr (Y 27) (.seq (.dec (Y 27)) (lbBody Y)))
  (.inc (Y 24)))

theorem lbW_spec (τ : WState ns nr) (S J a : ℕ) (h0 : τ.val (Y 0) = S) (h1 : τ.val (Y 1) = J)
    (hz : ∀ i : Fin 32, 2 ≤ i.val → i.val ≤ 23 → τ.val (Y i) = 0) (h27 : τ.val (Y 27) = 0)
    (h28 : τ.val (Y 28) = 0) (h24 : τ.val (Y 24) = a) (hcap : lvCap S J J ≤ cap)
    (hac : a + lbSumF S J + 1 ≤ cap) (hJc : J ≤ cap) :
    ∃ n, WExec cap (lbW Y) τ (τ.setv (Y 24) (a + lbSumF S J + 1)) n ∧
      n ≤ J * (lvlBound cap + 4) + 18 * J + 20 := by
  have hR : ∀ i k : Fin 32, Y i = Y k ↔ i = k := fun i k => Y.injective.eq_iff
  have hne : ∀ {i k : Fin 32}, i ≠ k → Y i ≠ Y k := fun h => Y.injective.ne h
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = 4 * winAt S J (J - 1 - i) := ⟨_, fun _ => rfl⟩
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Y 1) (Y 27) (Y 28) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h27 h28 (by omega)
  rw [h1] at e1
  let S' : ℕ → WState ns nr := fun k => (τ.setv (Y 27) (J - k)).setv (Y 24) (a + ∑ i ∈ Finset.range k, f i)
  have hS'0 : S' 0 = τ.setv (Y 27) J := by
    simp only [S', Finset.range_zero, Finset.sum_empty, Nat.add_zero, Nat.sub_zero]
    exact setv_eq_self (by rw [wsetv_val_ne _ _ (hne (by decide))]; exact h24)
  have hfull : ∑ i ∈ Finset.range J, f i = lbSumF S J := by
    unfold lbSumF
    rw [Finset.sum_congr rfl fun i _ => hf i]
    exact Finset.sum_range_reflect (fun j => 4 * winAt S J j) J
  have hloop := UnionMachine.Round.wloop cap (Y 27) (lbBody Y) (lvlBound cap) J S'
    (fun k _ => by simp [S', hR]) hJc
    (fun k hk => by
      have hin : (S' k).setv (Y 27) (J - k - 1) =
          (τ.setv (Y 27) (J - k - 1)).setv (Y 24) (a + ∑ i ∈ Finset.range k, f i) := by
        simp only [S']
        rw [wsetv_comm _ _ _ (hne (by decide) : Y 24 ≠ Y 27), wsetv_setv]
      rw [hin]
      have hpart : ∑ i ∈ Finset.range (k + 1), f i ≤ lbSumF S J := by
        rw [← hfull]; exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      rw [Finset.sum_range_succ, hf k] at hpart
      obtain ⟨m, em, bm⟩ := lbBody_spec cap Y ((τ.setv (Y 27) (J - k - 1)).setv (Y 24) (a + ∑ i ∈ Finset.range k, f i))
        S J (J - k - 1) (a + ∑ i ∈ Finset.range k, f i) (by simp [hR, h0]) (by simp [hR, h1]) (by simp [hR]) (by omega)
        (fun i h2 h23 => by
          rw [wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by show i.val ≠ 24; omega))),
            wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by show i.val ≠ 27; omega)))]
          exact hz i h2 h23)
        (by simp [hR, h28]) (by simp) (le_trans (LevelWordW.lvCap_mono S J _ (by omega)) hcap)
        (by rw [show J - k - 1 = J - 1 - k by omega]; omega) (by omega)
      refine WExec.mono (WExec.cast cap em ?_ le_rfl) bm
      simp only [S']
      rw [wsetv_setv, Finset.sum_range_succ, hf k, show J - k - 1 = J - (k + 1) by omega,
        show J - 1 - k = J - (k + 1) by omega, Nat.add_assoc])
  rw [hS'0] at hloop
  simp only [S', Nat.sub_self, hfull] at hloop
  have e3 := WExec.inc (cap := cap) (Y 24) ((τ.setv (Y 27) 0).setv (Y 24) (a + lbSumF S J)) (by simp; omega)
  rw [wsetv_setv, show ((τ.setv (Y 27) 0).setv (Y 24) (a + lbSumF S J)).val (Y 24) + 1 = a + lbSumF S J + 1 by simp]
    at e3
  have hτ0 : τ.setv (Y 27) 0 = τ := setv_eq_self h27
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq hloop e3)) (by rw [hτ0]) le_rfl, ?_⟩
  omega

/-- **The table word's length**: `acc += (M + 2) + Σ_{j≤J} (W'_j + pow W'_j + L + 3)` (`25 = M`, `26 = L`). -/
def lwW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Y 1) (Y 27) (Y 28))
  (.seq (.inc (Y 27))
  (.seq (.whr (Y 27) (.seq (.dec (Y 27)) (lwBody Y)))
  (.seq (ParseNat.addTo (Y 25) (Y 24) (Y 28))
  (StarNums.incN (Y 24) 2))))

theorem lwW_spec (τ : WState ns nr) (S J L M a : ℕ) (h0 : τ.val (Y 0) = S) (h1 : τ.val (Y 1) = J)
    (hz : ∀ i : Fin 32, 2 ≤ i.val → i.val ≤ 23 → τ.val (Y i) = 0) (h27 : τ.val (Y 27) = 0)
    (h28 : τ.val (Y 28) = 0) (h24 : τ.val (Y 24) = a) (h25 : τ.val (Y 25) = M) (h26 : τ.val (Y 26) = L)
    (hcap : lvCap S J J ≤ cap) (hac : a + lwSumF S J L + M + 2 ≤ cap) (hJc : J + 1 ≤ cap) :
    ∃ n, WExec cap (lwW Y) τ (τ.setv (Y 24) (a + lwSumF S J L + M + 2)) n ∧
      n ≤ (J + 1) * (lvlBound cap + 4) + 18 * J + 18 * M + 40 := by
  have hR : ∀ i k : Fin 32, Y i = Y k ↔ i = k := fun i k => Y.injective.eq_iff
  have hne : ∀ {i k : Fin 32}, i ≠ k → Y i ≠ Y k := fun h => Y.injective.ne h
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = winAt S J (J - i) + 2 ^ Nat.clog 2 (2 * winAt S J (J - i) + 1) + L + 3 :=
    ⟨_, fun _ => rfl⟩
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Y 1) (Y 27) (Y 28) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h27 h28 (by omega)
  rw [h1] at e1
  have e2 := WExec.inc (cap := cap) (Y 27) (τ.setv (Y 27) J) (by simp; omega)
  rw [wsetv_setv, show (τ.setv (Y 27) J).val (Y 27) + 1 = J + 1 by simp] at e2
  let S' : ℕ → WState ns nr := fun k => (τ.setv (Y 27) (J + 1 - k)).setv (Y 24) (a + ∑ i ∈ Finset.range k, f i)
  have hS'0 : S' 0 = τ.setv (Y 27) (J + 1) := by
    simp only [S', Finset.range_zero, Finset.sum_empty, Nat.add_zero, Nat.sub_zero]
    exact setv_eq_self (by rw [wsetv_val_ne _ _ (hne (by decide))]; exact h24)
  have hfull : ∑ i ∈ Finset.range (J + 1), f i = lwSumF S J L := by
    unfold lwSumF
    rw [Finset.sum_congr rfl fun i _ => hf i]
    have := Finset.sum_range_reflect (fun j => winAt S J j + 2 ^ Nat.clog 2 (2 * winAt S J j + 1) + L + 3) (J + 1)
    simp only [Nat.add_sub_cancel] at this
    exact this
  have hloop := UnionMachine.Round.wloop cap (Y 27) (lwBody Y) (lvlBound cap) (J + 1) S'
    (fun k _ => by simp [S', hR]) hJc
    (fun k hk => by
      have hin : (S' k).setv (Y 27) (J + 1 - k - 1) =
          (τ.setv (Y 27) (J + 1 - k - 1)).setv (Y 24) (a + ∑ i ∈ Finset.range k, f i) := by
        simp only [S']
        rw [wsetv_comm _ _ _ (hne (by decide) : Y 24 ≠ Y 27), wsetv_setv]
      rw [hin]
      have hpart : ∑ i ∈ Finset.range (k + 1), f i ≤ lwSumF S J L := by
        rw [← hfull]; exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      rw [Finset.sum_range_succ, hf k] at hpart
      obtain ⟨m, em, bm⟩ := lwBody_spec cap Y
        ((τ.setv (Y 27) (J + 1 - k - 1)).setv (Y 24) (a + ∑ i ∈ Finset.range k, f i))
        S J (J + 1 - k - 1) L (a + ∑ i ∈ Finset.range k, f i) (by simp [hR, h0]) (by simp [hR, h1]) (by simp [hR])
        (by omega)
        (fun i h2 h23 => by
          rw [wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by show i.val ≠ 24; omega))),
            wsetv_val_ne _ _ (hne (Fin.ne_of_val_ne (by show i.val ≠ 27; omega)))]
          exact hz i h2 h23)
        (by simp [hR, h28]) (by simp) (by simp [hR, h26]) (le_trans (LevelWordW.lvCap_mono S J _ (by omega)) hcap)
        (by rw [show J + 1 - k - 1 = J - k by omega]; omega) (by omega)
      refine WExec.mono (WExec.cast cap em ?_ le_rfl) bm
      simp only [S']
      rw [wsetv_setv, Finset.sum_range_succ, hf k, show J + 1 - k - 1 = J + 1 - (k + 1) by omega,
        show J + 1 - (k + 1) = J - k by omega, Nat.add_assoc])
  rw [hS'0] at hloop
  simp only [S', Nat.sub_self, hfull] at hloop
  have e4 := ParseNat.addTo_spec cap (Y 25) (Y 24) (Y 28) (hne (by decide)) (hne (by decide)) (hne (by decide))
    ((τ.setv (Y 27) 0).setv (Y 24) (a + lwSumF S J L)) (by simp [hR, h28]) (by simp [hR, h25]; omega)
    (by simp [hR, h25]; omega)
  rw [wsetv_setv, show ((τ.setv (Y 27) 0).setv (Y 24) (a + lwSumF S J L)).val (Y 24) +
      ((τ.setv (Y 27) 0).setv (Y 24) (a + lwSumF S J L)).val (Y 25) = a + lwSumF S J L + M by simp [hR, h25],
    show ((τ.setv (Y 27) 0).setv (Y 24) (a + lwSumF S J L)).val (Y 25) = M by simp [hR, h25]] at e4
  have e5 := StarNums.incN_spec cap (Y 24) 2 ((τ.setv (Y 27) 0).setv (Y 24) (a + lwSumF S J L + M)) (by simp; omega)
  rw [wsetv_setv, show ((τ.setv (Y 27) 0).setv (Y 24) (a + lwSumF S J L + M)).val (Y 24) + 2 =
    a + lwSumF S J L + M + 2 by simp] at e5
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq hloop (WExec.seq e4 e5))))
    (by rw [setv_eq_self h27]) le_rfl, ?_⟩
  omega

end Loops3

/-! ## The values are the list's -/

theorem list_sum_range (g : ℕ → ℕ) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range g n, Finset.sum_range_succ]; simp

/-- **The list bound of the base list** (`d = 3·listBound`): the program's sum plus one. -/
theorem lbP_eq (P : Lists.FlatListParams) :
    PopLink.lbP P = lbSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J + 1 := by
  unfold PopLink.lbP ListMachine.listBound lbSumF
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjJ : j < P.base.J := Finset.mem_range.mp hj
  rw [winAt_eq P.base j]
  unfold FinalPass.ListEval.topW
  rw [if_neg (by omega)]

/-- **The table word's length** for rows of length `L`: the program's sum plus `M + 2`. -/
theorem levelWord_length (P : Lists.BaseListParams) (L : ℕ) (row : ℕ → List Bool)
    (hrow : ∀ j ≤ P.J, (row j).length = L) :
    (FinalPass.ListEval.levelWord P.M P.J P.W row).length =
      lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B)) P.J L + P.M + 2 := by
  unfold FinalPass.ListEval.levelWord lwSumF
  simp only [List.length_append, List.length_flatMap, FinalPass.ListEval.unary, List.length_replicate,
    List.length_singleton]
  have hl : ((FinalPass.ListEval.levels P.J).map fun j =>
      (FinalPass.ListEval.record P.J P.W row j).length).sum =
      ∑ j ∈ Finset.range (P.J + 1), (winAt (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B)) P.J j +
        2 ^ Nat.clog 2 (2 * winAt (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B)) P.J j + 1) + L + 3) := by
    unfold FinalPass.ListEval.levels
    rw [List.map_reverse, List.sum_reverse, list_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjJ : j ≤ P.J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    unfold FinalPass.ListEval.record
    simp only [List.length_cons, List.length_append, FinalPass.ListEval.unary, List.length_replicate,
      List.length_singleton, hrow j hjJ]
    rw [powAt_eq P j, winAt_eq P j]
    unfold FinalPass.ListEval.pow
    simp only [List.length_nil]
    omega
  rw [hl]
  omega

/-- **The stage-5 register capacity of the base list** (`c = capP P L`). -/
theorem capP_eq (P : Lists.FlatListParams) (L : ℕ) :
    PopLink.capP P L =
      4 * (lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J L + P.base.M + 2 + L + 1) := by
  unfold PopLink.capP FinalPass.ListEval.capOf
  rw [levelWord_length P.base L _ (fun j _ => List.length_replicate)]

end NearCubicWires.WireExponent3_5.PrimAsm.PopParams
