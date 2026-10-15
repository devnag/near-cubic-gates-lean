import Proof.Gates.WordPrograms.Arr
import Proof.Gates.WordPrograms.OutX

/-! # Copy a range of records by index

**`copyN A Wk O …`**: append records `c₀, …, c₀ + K − 1` of the record stream on `A` (any tail) to the output
stream `O`, the cursor register `CUR` advancing from `c₀` to `c₀ + K` (`copyN_spec`). Built from `getAt` (read by
index) and `appendRec`. Cost `K · (copyStep L N + 8) + 7K + 3`, `N` the record count. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- `K` record copies `A[CUR] → O`, `CUR += 1` each (`K` in register `KC`). -/
def copyN (A Wk O : Fin (ns + 1)) (CA CW CUR K2 CS CO KC KC2 : Fin nr) : WMX ns nr :=
  repK KC KC2 (.seq (getAt A Wk CA CW CUR K2) (.seq (appendRecX Wk O CS CO) (WMX.inc CUR)))

/-- One copy's cost bound (any index below `N`). -/
def copyStep (L N : ℕ) : ℕ := (N + 1) * (40 * L + 40) + 10 * (N + 1) * (2 * L + 1) + 10 + 1 + (40 * L + 11) + 1 + 3

/-- The records `c₀, …, c₀ + k − 1`, framed. -/
def segRecs (L : ℕ) (xs : List ℕ) (c0 k : ℕ) : List Bool := ((xs.drop c0).take k).flatMap fun x => frame (binary L x)

theorem segRecs_succ (L : ℕ) (xs : List ℕ) (c0 k : ℕ) (h : c0 + k < xs.length) :
    segRecs L xs c0 (k + 1) = segRecs L xs c0 k ++ frame (binary L xs[c0 + k]) := by
  unfold segRecs
  rw [List.take_add_one, List.flatMap_append]
  congr 1
  rw [List.getElem?_drop, List.getElem?_eq_getElem h]
  simp

theorem segRecs_length (L : ℕ) (xs : List ℕ) (c0 k : ℕ) (h : c0 + k ≤ xs.length) :
    (segRecs L xs c0 k).length = k * (2 * L + 1) := by
  induction k with
  | zero => simp [segRecs]
  | succ k ih => rw [segRecs_succ L xs c0 k (by omega), List.length_append, ih (by omega)]; simp [frame_length]; ring

theorem copyStep_le (L N i : ℕ) (hi : i < N) :
    (i + 1) * (40 * L + 40) + 10 * (i + 1) * (2 * L + 1) + 10 + 1 + (40 * L + 11 + 1 + 3) ≤ copyStep L N := by
  have e1 := Nat.mul_le_mul_right (40 * L + 40) (show i + 1 ≤ N + 1 by omega)
  have e2 := Nat.mul_le_mul_right (2 * L + 1) (Nat.mul_le_mul_left 10 (show i + 1 ≤ N + 1 by omega))
  unfold copyStep; omega

theorem copyN_spec (cap : ℕ) {A Wk O : Fin (ns + 1)} {CA CW CUR K2 CS CO KC KC2 : Fin nr} (hS : [A, Wk, O].Nodup)
    (hR : [CA, CW, CUR, K2, CS, CO, KC, KC2].Nodup) (L : ℕ) (hL : 1 ≤ L) (xs : List ℕ) (c0 K : ℕ)
    (hK : c0 + K ≤ xs.length) (σ : WState ns nr) (junk out L0 : List Bool)
    (hA : σ.st A = recStream (xs.map (binary L)) ++ junk) (hAh : σ.sh A = 0) (hCA : σ.val CA = 0)
    (hCW : σ.val CW = 0) (hK2 : σ.val K2 = 0) (hCS : σ.val CS = 0) (hWh : σ.sh Wk = 0)
    (hWl : (σ.st Wk).length ≤ 2 * L + 1) (hCUR : σ.val CUR = c0) (hKC : σ.val KC = K) (hKC2 : σ.val KC2 = 0)
    (hO : OutOn σ O CO out L0) (hcap : (xs.length + 1) * (2 * L + 1) + 2 * xs.length ≤ cap)
    (hcapO : out.length + K * (2 * L + 1) + 1 ≤ cap) :
    Runs cap (copyN A Wk O CA CW CUR K2 CS CO KC KC2) σ (K * (copyStep L xs.length + 8) + 7 * K + 3) (fun τ =>
      OutOn τ O CO (out ++ segRecs L xs c0 K) L0 ∧ τ.val CUR = c0 + K ∧ τ.sh Wk = 0 ∧
        (τ.st Wk).length ≤ 2 * L + 1 ∧ τ.val KC = K ∧ τ.val KC2 = 0 ∧ SameExcept σ τ [Wk, O] [CUR, CO]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hS hR
  obtain ⟨⟨hAW, hAO⟩, hWO⟩ := hS
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩, ⟨h12, h13, h14, h15, h16, h17⟩, ⟨h23, h24, h25, h26, h27⟩,
    ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67⟩ := hR
  let Inv : ℕ → WState ns nr → Prop := fun k τ =>
    OutOn τ O CO (out ++ segRecs L xs c0 k) L0 ∧ τ.val CUR = c0 + k ∧ τ.sh Wk = 0 ∧ (τ.st Wk).length ≤ 2 * L + 1 ∧
      SameExcept σ τ [Wk, O] [CUR, CO, KC, KC2]
  have hInv : ∀ k τ (r : Fin nr), r = KC ∨ r = KC2 → ∀ v, Inv k τ → Inv k (τ.setv r v) := by
    rintro k τ r hr v ⟨h1, h2, h3, h4, h5⟩
    have hrCO : CO ≠ r := by rcases hr with rfl | rfl <;> assumption
    have hrCUR : CUR ≠ r := by rcases hr with rfl | rfl <;> assumption
    exact ⟨⟨by simpa using h1.1, by simpa using h1.2.1, by
      rw [WState.setv_val, Function.update_of_ne hrCO]; exact h1.2.2⟩,
      by rw [WState.setv_val, Function.update_of_ne hrCUR]; exact h2, by simpa using h3, by simpa using h4,
      h5.trans (sameExcept_setv τ (by rcases hr with rfl | rfl <;> simp) v)⟩
  have h := Runs.rep (cap := cap) (K := KC) (K2 := KC2)
    (body := .seq (getAt A Wk CA CW CUR K2) (.seq (appendRecX Wk O CS CO) (WMX.inc CUR))) h67
    (copyStep L xs.length) K Inv (by omega) (fun k τ v hI => hInv k τ KC (Or.inl rfl) v hI)
    (fun k τ v hI => hInv k τ KC2 (Or.inr rfl) v hI) ?_ σ
    ⟨by simpa [segRecs] using hO, hCUR, hWh, hWl, SameExcept.refl _ _ _⟩ hKC hKC2
  · refine h.post fun τ hτ => ⟨hτ.1.1, hτ.1.2.1, hτ.1.2.2.1, hτ.1.2.2.2.1, hτ.2.1, hτ.2.2, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hτ.1.2.2.2.2
    refine ⟨h1, fun r hr => ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases hr1 : r = KC
    · subst hr1; rw [hτ.2.1, hKC]
    · by_cases hr2 : r = KC2
      · subst hr2; rw [hτ.2.2, hKC2]
      · exact h2 r (by simp [hr.1, hr.2, hr1, hr2])
  · intro k hk τ hI
    obtain ⟨hOτ, hCURτ, hWhτ, hWlτ, hfr⟩ := hI
    have hfrv : ∀ r, r ≠ CUR → r ≠ CO → r ≠ KC → r ≠ KC2 → τ.val r = σ.val r :=
      fun r a b c d => hfr.val (by simp [a, b, c, d])
    have hn : c0 + k < xs.length := by omega
    have hg := getAt_spec cap (CA := CA) (CW := CW) (N := CUR) (K2 := K2) hAW (by simp [h01, h02, h03, h12, h13, h23])
      L hL xs (c0 + k) hn τ junk
      (by rw [hfr.st (by simp [hAW, hAO]), hA]) (by rw [hfr.sh (by simp [hAW, hAO]), hAh])
      (by rw [hfrv CA h02 h05 h06 h07, hCA]) hWhτ hWlτ (by rw [hfrv CW h12 h15 h16 h17, hCW]) hCURτ
      (by rw [hfrv K2 (Ne.symm h23) h35 h36 h37, hK2]) (by omega)
    set τ1 := τ.sets Wk (frame (binary L xs[c0 + k])) with hτ1
    have hO1 : OutOn τ1 O CO (out ++ segRecs L xs c0 k) L0 :=
      ⟨by simp [hτ1, Function.update_of_ne (Ne.symm hWO), hOτ.1], by simp [hτ1, Function.update_of_ne (Ne.symm hWO), hOτ.2.1],
        by simp [hτ1, hOτ.2.2]⟩
    have hlen := segRecs_length L xs c0 k (by omega)
    have ha := appendRec_spec cap hWO h45 τ1 (binary L xs[c0 + k]) [] (out ++ segRecs L xs c0 k) L0
      (by simp [hτ1, BinW.frame_frameP]) (by simp [hτ1, hWhτ])
      (by simp [hτ1]; rw [hfrv CS (Ne.symm h24) h45 h46 h47, hCS]) hO1
      (by
        rw [List.length_append, hlen, binary_length]
        have : (k + 1) * (2 * L + 1) ≤ K * (2 * L + 1) := Nat.mul_le_mul_right _ (by omega)
        nlinarith)
    set τ2 := ((τ1.sets O (overlay (out ++ segRecs L xs c0 k ++ frame (binary L xs[c0 + k])) L0)).seth O
      (out ++ segRecs L xs c0 k ++ frame (binary L xs[c0 + k])).length).setv CO
      (out ++ segRecs L xs c0 k ++ frame (binary L xs[c0 + k])).length with hτ2
    have hcur : τ2.val CUR < cap := by
      have : τ2.val CUR = c0 + k := by simp only [hτ2, WState.setv_val, Function.update_of_ne h25]; simp [hτ1, hCURτ]
      rw [this]; clear_value τ1 τ2; omega
    have hi := WXExec.inc cap CUR τ2 hcur
    rw [binary_length] at ha
    have hex : WXExec cap (.seq (getAt A Wk CA CW CUR K2) (.seq (appendRecX Wk O CS CO) (WMX.inc CUR))) τ
        (τ2.setv CUR (τ2.val CUR + 1)) (copyStep L xs.length) :=
      (WXExec.seq hg (WXExec.seq (WXExec.wm ha) hi)).mono (copyStep_le L xs.length (c0 + k) hn)
    refine ⟨_, hex, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [hτ2, Function.update_of_ne (Ne.symm hWO), segRecs_succ L xs c0 k hn, List.append_assoc]
    · simp [hτ2, segRecs_succ L xs c0 k hn, List.append_assoc]
    · simp [hτ2, Function.update_apply, Ne.symm h25, segRecs_succ L xs c0 k hn, List.append_assoc]
    · simp [hτ2, hτ1, hCURτ, Function.update_apply, h25]; omega
    · simp [hτ2, hτ1, Function.update_of_ne hWO, hWhτ]
    · simp [hτ2, hτ1, Function.update_of_ne hWO, frame_length]
    · refine hfr.trans ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ2, hτ1]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [hτ2, hτ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hτ2, hτ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]
    · simp [hτ2, hτ1, Function.update_of_ne (Ne.symm h26), Function.update_of_ne (Ne.symm h56)]
    · simp [hτ2, hτ1, Function.update_of_ne (Ne.symm h27), Function.update_of_ne (Ne.symm h57)]

end NearCubicGates.Close.WordPrograms
