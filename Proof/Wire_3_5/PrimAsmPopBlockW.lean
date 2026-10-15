import Proof.Wire_3_5.PrimAsmLevelWordW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.PrimAsm.PopRec
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW

variable {ns nr : ℕ} (cap : ℕ)

/-- The POP writer's registers: `0` output counter; `1`–`19` the FILTER bank's; `20`–`43` the level block (`20 S`,
`21 J`); `44 M`, `45 L`, `46`–`48` the table word's counters; `49 s'`, `50` sign flag, `51 c+1`, `52 walkLen`, `53 θ`,
`54 R`, `55 Lg`, `56 cap`, `57` a visit's rows' length, `58` the table's length, `59`, `60` loop counters, `61`, `62`
scratch, `63 s`. -/
abbrev PReg (nr : ℕ) := Fin 64 ↪ Fin nr

/-- The FILTER bank's registers inside the POP writer's. -/
def pF : Fin 20 ↪ Fin 64 := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The table word's registers inside the POP writer's (its output counter is `0`). -/
def pW : Fin 30 ↪ Fin 64 :=
  ⟨![20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 0, 44, 45, 46,
    47, 48], by decide⟩

theorem pW_scratch : ∀ i : Fin 30, 2 ≤ i.val → i.val ≤ 23 → 22 ≤ (pW i).val ∧ (pW i).val ≤ 43 := by decide

/-! ## The zero fields -/

section Zeros
variable (O : Fin (ns + 1)) (X : PReg nr)

/-- One field `0^{c+1}` (from `51`) at level 2 with its end. -/
def zf : WM ns nr := .seq (repRegW O (X 0) (X 51) (X 61) (X 62) (m2 false)) (emitW O (X 0) [true, false])

/-- `n` runs of a program. -/
def repP (P : WM ns nr) : ℕ → WM ns nr
  | 0 => .skip
  | n + 1 => .seq (repP P n) P

theorem zf_spec (σ : WState ns nr) (x : ℕ) (hx : σ.val (X 51) = x) (h61 : σ.val (X 61) = 0)
    (h62 : σ.val (X 62) = 0) (ho : σ.sh O = (σ.st O).length) (hxc : x ≤ cap)
    (hc : σ.val (X 0) + (4 * x + 2) ≤ cap) :
    WExec cap (zf O X) σ (appendO σ O (X 0) (reps x (m2 false) ++ [true, false])) (54 * x + 22) := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have e1 := repRegW_spec cap O (X 0) (X 51) (X 61) (X 62) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (m2 false) σ h61 h62 ho (by omega) (by rw [hx]; simp [m2]; omega)
  rw [hx] at e1
  have e2 := emitW_spec cap O (X 0) [true, false] (appendO σ O (X 0) (reps x (m2 false))) (by simp [ho])
    (by simp [FiltRecW.reps_length, m2]; omega)
  rw [appendO_append] at e2
  exact WExec.cast cap (WExec.seq e1 e2) rfl (by simp [m2]; omega)

theorem zerosN_spec (x : ℕ) : ∀ (n : ℕ) (σ : WState ns nr), σ.val (X 51) = x → σ.val (X 61) = 0 →
    σ.val (X 62) = 0 → σ.sh O = (σ.st O).length → x ≤ cap → σ.val (X 0) + n * (4 * x + 2) ≤ cap →
    WExec cap (repP (zf O X) n) σ (appendO σ O (X 0) (reps n (reps x (m2 false) ++ [true, false])))
      (n * (54 * x + 23))
  | 0, σ, _, _, _, _, _, _ => by
    rw [reps_zero, appendO_nil, Nat.zero_mul]
    exact WExec.skip σ
  | n + 1, σ, hx, h61, h62, ho, hxc, hc => by
    have hR : ∀ i k : Fin 64, X i = X k ↔ i = k := fun i k => X.injective.eq_iff
    have hc' : σ.val (X 0) + n * (4 * x + 2) + (4 * x + 2) ≤ cap := by
      have : (n + 1) * (4 * x + 2) = n * (4 * x + 2) + (4 * x + 2) := by ring
      omega
    have ih := zerosN_spec x n σ hx h61 h62 ho hxc (by omega)
    have hl : (reps n (reps x (m2 false) ++ [true, false])).length = n * (4 * x + 2) := by
      rw [FiltRecW.reps_length]
      simp only [List.length_append, FiltRecW.reps_length, m2, List.length_cons, List.length_nil]
      ring
    have e := zf_spec cap O X (appendO σ O (X 0) (reps n (reps x (m2 false) ++ [true, false]))) x
      (by simp [hR, hx]) (by simp [hR, h61]) (by simp [hR, h62]) (by simp [ho]) hxc
      (by rw [appendO_val, Function.update_self, hl]; omega)
    rw [appendO_append, ← reps_succ] at e
    refine WExec.cast cap (WExec.seq ih e) rfl ?_
    show n * (54 * x + 23) + 1 + (54 * x + 22) ≤ (n + 1) * (54 * x + 23)
    have : (n + 1) * (54 * x + 23) = n * (54 * x + 23) + (54 * x + 23) := by ring
    omega

end Zeros

theorem fSt_zero_s {O S : Fin (ns + 1)} {F : FReg nr} (hOS : O ≠ S) (σ : WState ns nr) (u : List Bool) :
    fSt O S F σ u 0 = appendO σ O (F 0) u := by
  have hR : ∀ i j : Fin 20, F i = F j ↔ i = j := fun i j => F.injective.eq_iff
  unfold fSt
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp [Function.update_apply, Ne.symm hOS]
    · simp [Function.update_apply, hj]
  · rfl
  · funext j; by_cases hj : j = F 18
    · subst hj; simp [hR]
    · simp [Function.update_apply, hj]
  · rfl

section LStX
variable {O S : Fin (ns + 1)} {OP : Fin nr}

theorem lSt_val_ne {r : Fin nr} (h : r ≠ OP) (τ : WState ns nr) (u : List Bool) (hh : ℕ) :
    (lSt O S OP τ u hh).val r = τ.val r := by
  rw [lSt_val, Function.update_of_ne h]

theorem lSt_val_self (τ : WState ns nr) (u : List Bool) (hh : ℕ) :
    (lSt O S OP τ u hh).val OP = τ.val OP + u.length := by
  rw [lSt_val, Function.update_self]

theorem lSt_ho (hOS : O ≠ S) (τ : WState ns nr) (ho : τ.sh O = (τ.st O).length) (u : List Bool) (hh : ℕ) :
    (lSt O S OP τ u hh).sh O = ((lSt O S OP τ u hh).st O).length := by
  rw [lSt_shO hOS, lSt_stO, ho, List.length_append]

end LStX

/-! ## The stage-3∘5 data -/

section Data
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **The stage-3∘5 data fields** of a block and its flag: the table word, `unary s'` (`49`), the scratch (`51 = c+1`),
the sign (`50`), 15 registers, `neg`. -/
def dataW (neg : Bool) : WM ns nr :=
  .seq (lvWordW O S (pW.trans X))
  (.seq (emitW O (X 0) [true, false])
  (.seq (repRegW O (X 0) (X 49) (X 61) (X 62) (m2 true))
  (.seq (emitW O (X 0) (m2 false ++ [true, false]))
  (.seq (zf O X)
  (.seq (.ifr (X 50) (emitW O (X 0) (m2 true ++ [true, false])) (emitW O (X 0) (m2 false ++ [true, false])))
  (.seq (repP (zf O X) 15)
  (emitW O (X 0) (m2 neg ++ [true, false]))))))))

/-- A bound on the data fields' cost. -/
def dataBound (cap J M s c : ℕ) : ℕ := lvWordBound cap J M + 54 * s + 16 * (54 * (c + 1) + 23) + 700

theorem pieceP_length (lvE : List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) (neg : Bool) :
    (pieceP lvE s sgn c neg).length =
      lvE.length + 2 + (4 * s + 6) + (4 * (c + 1) + 2) + 6 + 15 * (4 * (c + 1) + 2) + 6 := by
  unfold pieceP
  simp only [List.length_append, FiltRecW.reps_length, m2, List.length_cons, List.length_nil]
  ring

theorem dataW_spec (hOS : O ≠ S) (neg : Bool) (τ : WState ns nr) (M Sv J L s' c : ℕ) (sgn : Bool)
    (rowF : ℕ → List Bool) (hrows : ∀ j ≤ J, (rowF j).length = L)
    (h20 : τ.val (X 20) = Sv) (h21 : τ.val (X 21) = J) (h44 : τ.val (X 44) = M) (h45 : τ.val (X 45) = L)
    (hz : ∀ i : Fin 64, 22 ≤ i.val → i.val ≤ 43 → τ.val (X i) = 0) (h46 : τ.val (X 46) = 0)
    (h47 : τ.val (X 47) = 0) (h48 : τ.val (X 48) = 0) (h49 : τ.val (X 49) = s')
    (h50 : τ.val (X 50) = if sgn then 1 else 0) (h51 : τ.val (X 51) = c + 1) (h61 : τ.val (X 61) = 0)
    (h62 : τ.val (X 62) = 0) (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).length,
      readTapeBit (τ.st S) (τ.sh S + i) = ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hc : τ.val (X 0) + (pieceP (levelE M Sv J rowF) s' sgn c neg).length ≤ cap)
    (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap) (hsc : s' ≤ cap) (hcc : c + 1 ≤ cap) :
    ∃ n, WExec cap (dataW O S X neg) τ
      (lSt O S (X 0) τ (pieceP (levelE M Sv J rowF) s' sgn c neg) (τ.sh S + (J + 1) * (2 * L + 1))) n ∧
      n ≤ dataBound cap J M s' c := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have n0 : ∀ i : Fin 64, i ≠ 0 → X i ≠ X 0 := fun i h => hne h
  have hpl := pieceP_length (levelE M Sv J rowF) s' sgn c neg
  have hW24 : (pW.trans X) 24 = X 0 := rfl
  obtain ⟨n1, e1, b1⟩ := lvWordW_spec cap O S (pW.trans X) hOS τ M Sv J L rowF hrows h20 h21 h44 h45
    (fun i h2 h23 => hz (pW i) (pW_scratch i h2 h23).1 (pW_scratch i h2 h23).2) h46 h47 h48 ho hS hcap
    (by rw [hW24]; omega) hJc hLc hMc
  rw [hW24] at e1
  obtain ⟨h', hh'⟩ : ∃ x, x = τ.sh S + (J + 1) * (2 * L + 1) := ⟨_, rfl⟩
  rw [← hh'] at e1
  obtain ⟨u1, hu1⟩ : ∃ x, x = levelE M Sv J rowF := ⟨_, rfl⟩
  rw [← hu1] at e1 hpl hc
  have e2 := emitW_spec cap O (X 0) [true, false] (lSt O S (X 0) τ u1 h') (lSt_ho hOS τ ho _ _)
    (by rw [lSt_val_self]; simp only [List.length_cons, List.length_nil]; omega)
  rw [lSt_append hOS] at e2
  obtain ⟨u2, hu2⟩ : ∃ x, x = u1 ++ [true, false] := ⟨_, rfl⟩
  have hl2 : u2.length = u1.length + 2 := by rw [hu2, List.length_append]; rfl
  rw [← hu2] at e2
  have e3 := repRegW_spec cap O (X 0) (X 49) (X 61) (X 62) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (m2 true) (lSt O S (X 0) τ u2 h') (by rw [lSt_val_ne (n0 61 (by decide)), h61])
    (by rw [lSt_val_ne (n0 62 (by decide)), h62]) (lSt_ho hOS τ ho _ _)
    (by rw [lSt_val_ne (n0 49 (by decide)), h49]; omega)
    (by rw [lSt_val_ne (n0 49 (by decide)), h49, lSt_val_self, hl2]
        simp only [m2, List.length_cons, List.length_nil]; omega)
  rw [lSt_val_ne (n0 49 (by decide)), h49, lSt_append hOS] at e3
  obtain ⟨u3, hu3⟩ : ∃ x, x = u2 ++ reps s' (m2 true) := ⟨_, rfl⟩
  have hl3 : u3.length = u1.length + 2 + 4 * s' := by
    rw [hu3, List.length_append, hl2, FiltRecW.reps_length]; simp [m2]; ring
  rw [← hu3] at e3
  have e4 := emitW_spec cap O (X 0) (m2 false ++ [true, false]) (lSt O S (X 0) τ u3 h') (lSt_ho hOS τ ho _ _)
    (by rw [lSt_val_self, hl3]; simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [lSt_append hOS] at e4
  obtain ⟨u4, hu4⟩ : ∃ x, x = u3 ++ (m2 false ++ [true, false]) := ⟨_, rfl⟩
  have hl4 : u4.length = u1.length + 2 + (4 * s' + 6) := by
    rw [hu4, List.length_append, hl3]; simp [m2]; ring
  rw [← hu4] at e4
  have e5 := zf_spec cap O X (lSt O S (X 0) τ u4 h') (c + 1) (by rw [lSt_val_ne (n0 51 (by decide)), h51])
    (by rw [lSt_val_ne (n0 61 (by decide)), h61]) (by rw [lSt_val_ne (n0 62 (by decide)), h62])
    (lSt_ho hOS τ ho _ _) hcc (by rw [lSt_val_self, hl4]; omega)
  rw [lSt_append hOS] at e5
  obtain ⟨u5, hu5⟩ : ∃ x, x = u4 ++ (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl5 : u5.length = u1.length + 2 + (4 * s' + 6) + (4 * (c + 1) + 2) := by
    rw [hu5, List.length_append, hl4, List.length_append, FiltRecW.reps_length]; simp [m2]; ring
  rw [← hu5] at e5
  have e6 : WExec cap (.ifr (X 50) (emitW O (X 0) (m2 true ++ [true, false])) (emitW O (X 0) (m2 false ++ [true, false])))
      (lSt O S (X 0) τ u5 h') (lSt O S (X 0) τ (u5 ++ (m2 sgn ++ [true, false])) h') (8 * 6 + 1) := by
    have hcap6 : (lSt O S (X 0) τ u5 h').val (X 0) + (m2 sgn ++ [true, false]).length ≤ cap := by
      rw [lSt_val_self, hl5]; simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega
    cases sgn
    · have e := emitW_spec cap O (X 0) (m2 false ++ [true, false]) (lSt O S (X 0) τ u5 h') (lSt_ho hOS τ ho _ _) hcap6
      rw [lSt_append hOS] at e
      exact WExec.ifrF (by rw [lSt_val_ne (n0 50 (by decide)), h50]; rfl) e
    · have e := emitW_spec cap O (X 0) (m2 true ++ [true, false]) (lSt O S (X 0) τ u5 h') (lSt_ho hOS τ ho _ _) hcap6
      rw [lSt_append hOS] at e
      exact WExec.ifrT (by rw [lSt_val_ne (n0 50 (by decide)), h50]; decide) e
  obtain ⟨u6, hu6⟩ : ∃ x, x = u5 ++ (m2 sgn ++ [true, false]) := ⟨_, rfl⟩
  have hl6 : u6.length = u1.length + 2 + (4 * s' + 6) + (4 * (c + 1) + 2) + 6 := by
    rw [hu6, List.length_append, hl5]; simp [m2]
  rw [← hu6] at e6
  have e7 := zerosN_spec cap O X (c + 1) 15 (lSt O S (X 0) τ u6 h') (by rw [lSt_val_ne (n0 51 (by decide)), h51])
    (by rw [lSt_val_ne (n0 61 (by decide)), h61]) (by rw [lSt_val_ne (n0 62 (by decide)), h62])
    (lSt_ho hOS τ ho _ _) hcc (by rw [lSt_val_self, hl6]; omega)
  rw [lSt_append hOS] at e7
  obtain ⟨u7, hu7⟩ : ∃ x, x = u6 ++ reps 15 (reps (c + 1) (m2 false) ++ [true, false]) := ⟨_, rfl⟩
  have hl7 : u7.length = u1.length + 2 + (4 * s' + 6) + (4 * (c + 1) + 2) + 6 + 15 * (4 * (c + 1) + 2) := by
    rw [hu7, List.length_append, hl6, FiltRecW.reps_length]
    simp only [List.length_append, FiltRecW.reps_length, m2, List.length_cons, List.length_nil]; ring
  rw [← hu7] at e7
  have e8 := emitW_spec cap O (X 0) (m2 neg ++ [true, false]) (lSt O S (X 0) τ u7 h') (lSt_ho hOS τ ho _ _)
    (by rw [lSt_val_self, hl7]; simp only [m2, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [lSt_append hOS] at e8
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ le_rfl, ?_⟩
  · rw [hu7, hu6, hu5, hu4, hu3, hu2, hu1, hh']
    unfold pieceP
    simp only [List.append_assoc]
  · unfold dataBound
    have c3 : s' * (8 * (m2 true).length + 4) = 36 * s' := by simp [m2]; ring
    simp only [m2, List.length_cons, List.length_nil, List.length_append] at c3 ⊢
    omega

end Data

/-! ## The block's registers -/

/-- The registers a block reads: the FILTER bank's numbers (`1`–`4` the labels, `13 = 4L`, `14 = d`), the list's
(`20 S`, `21 J`, `44 M`, `45 L`), the state `s'` (`49`), the sign (`50`), `c+1` (`51`), a visit's rows' length (`57`);
the scratch at `0`. -/
structure BlockRegs (X : PReg nr) (τ : WState ns nr) (Lp d r4 G off Lg Sv J M L s' c VW : ℕ) (sgn : Bool) :
    Prop where
  h1 : τ.val (X 1) = r4
  h2 : τ.val (X 2) = G
  h3 : τ.val (X 3) = off
  h4 : τ.val (X 4) = Lg
  hz1 : ∀ i : Fin 64, 5 ≤ i.val → i.val ≤ 12 → τ.val (X i) = 0
  h13 : τ.val (X 13) = Lp
  h14 : τ.val (X 14) = d
  h19 : τ.val (X 19) = 0
  h20 : τ.val (X 20) = Sv
  h21 : τ.val (X 21) = J
  hz2 : ∀ i : Fin 64, 22 ≤ i.val → i.val ≤ 43 → τ.val (X i) = 0
  h44 : τ.val (X 44) = M
  h45 : τ.val (X 45) = L
  h46 : τ.val (X 46) = 0
  h47 : τ.val (X 47) = 0
  h48 : τ.val (X 48) = 0
  h49 : τ.val (X 49) = s'
  h50 : τ.val (X 50) = if sgn then 1 else 0
  h51 : τ.val (X 51) = c + 1
  h57 : τ.val (X 57) = VW
  h61 : τ.val (X 61) = 0
  h62 : τ.val (X 62) = 0

theorem BlockRegs.of_val {X : PReg nr} {τ τ' : WState ns nr} {Lp d r4 G off Lg Sv J M L s' c VW : ℕ} {sgn : Bool}
    (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c VW sgn)
    (hv : ∀ i : Fin 64, 1 ≤ i.val → i.val ≤ 57 ∨ 61 ≤ i.val ∧ i.val ≤ 62 → τ'.val (X i) = τ.val (X i)) :
    BlockRegs X τ' Lp d r4 G off Lg Sv J M L s' c VW sgn where
  h1 := by rw [hv 1 (by decide) (by decide)]; exact hB.h1
  h2 := by rw [hv 2 (by decide) (by decide)]; exact hB.h2
  h3 := by rw [hv 3 (by decide) (by decide)]; exact hB.h3
  h4 := by rw [hv 4 (by decide) (by decide)]; exact hB.h4
  hz1 := fun i h5 h12 => by rw [hv i (by omega) (by omega)]; exact hB.hz1 i h5 h12
  h13 := by rw [hv 13 (by decide) (by decide)]; exact hB.h13
  h14 := by rw [hv 14 (by decide) (by decide)]; exact hB.h14
  h19 := by rw [hv 19 (by decide) (by decide)]; exact hB.h19
  h20 := by rw [hv 20 (by decide) (by decide)]; exact hB.h20
  h21 := by rw [hv 21 (by decide) (by decide)]; exact hB.h21
  hz2 := fun i h5 h12 => by rw [hv i (by omega) (by omega)]; exact hB.hz2 i h5 h12
  h44 := by rw [hv 44 (by decide) (by decide)]; exact hB.h44
  h45 := by rw [hv 45 (by decide) (by decide)]; exact hB.h45
  h46 := by rw [hv 46 (by decide) (by decide)]; exact hB.h46
  h47 := by rw [hv 47 (by decide) (by decide)]; exact hB.h47
  h48 := by rw [hv 48 (by decide) (by decide)]; exact hB.h48
  h49 := by rw [hv 49 (by decide) (by decide)]; exact hB.h49
  h50 := by rw [hv 50 (by decide) (by decide)]; exact hB.h50
  h51 := by rw [hv 51 (by decide) (by decide)]; exact hB.h51
  h57 := by rw [hv 57 (by decide) (by decide)]; exact hB.h57
  h61 := by rw [hv 61 (by decide) (by decide)]; exact hB.h61
  h62 := by rw [hv 62 (by decide) (by decide)]; exact hB.h62

theorem BlockRegs.lSt {X : PReg nr} {O S : Fin (ns + 1)} {τ : WState ns nr} {Lp d r4 G off Lg Sv J M L s' c VW : ℕ}
    {sgn : Bool} (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c VW sgn) (u : List Bool) (h : ℕ) :
    BlockRegs X (lSt O S (X 0) τ u h) Lp d r4 G off Lg Sv J M L s' c VW sgn :=
  hB.of_val fun i h1 _ => lSt_val_ne (X.injective.ne (Fin.ne_of_val_ne (by show i.val ≠ 0; omega))) τ u h

/-! ## A block -/

/-- The FILTER bank's first fields' register capacity (`FiltRecW.phaseA_spec`). -/
def labCapA (Lp d : ℕ) : ℕ := 4 * (8 * Lp + 6) + 30 + 4 * d + 6 + Lp + d + 10

/-- The label fields' register capacity (`FiltRecW.phaseB_spec`, labels below `Mlab`). -/
def labCapB (r4 G off Lg Mlab : ℕ) : ℕ :=
  ((sliceLabs r4 G off Lg).flatMap labE).length + 4 * labSum (sliceLabs r4 G off Lg) + 10 +
    Lg * (4 * (4 * Mlab + 4)) + Lg * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) + 4 * (2 * Mlab + 10) + 7 * Mlab +
    r4 + G + off + Lg + labSum (sliceLabs r4 G off Lg) + 40

section Block
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **A factor block**: its marker, the FILTER bank's first fields, the stage-3∘5 data. -/
def blockW (neg : Bool) : WM ns nr :=
  .seq (emitW O (X 0) [true, true]) (.seq (phaseA O (pF.trans X)) (.seq (phaseB O (pF.trans X)) (dataW O S X neg)))

/-- A bound on a block's cost. -/
def blockBound (cap J M s c Lp d r4 G off Lg : ℕ) : ℕ :=
  dataBound cap J M s c + 400 * (Lp + d + 10) + 100 * (labSum (sliceLabs r4 G off Lg) + 10) + labsCost r4 G off Lg + 50

theorem blockE_length (Lp d cap1 : ℕ) (labs : List ℕ) (lvE : List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) (neg : Bool) :
    (blockE Lp d cap1 labs lvE s sgn c neg).length =
      2 + ((pieceA Lp d).length + ((pieceB labs cap1).length + (pieceP lvE s sgn c neg).length)) := by
  unfold blockE; simp only [List.length_append, List.length_cons, List.length_nil]

theorem blockE_length_neg (Lp d cap1 : ℕ) (labs : List ℕ) (lvE : List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) :
    (blockE Lp d cap1 labs lvE s sgn c true).length = (blockE Lp d cap1 labs lvE s sgn c false).length := by
  rw [blockE_length, blockE_length, pieceP_length, pieceP_length]

theorem blockW_spec (hOS : O ≠ S) (neg : Bool) (τ : WState ns nr) (Lp d r4 G off Lg Sv J M L s' c VW : ℕ)
    (sgn : Bool) (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c VW sgn) (Mlab : ℕ)
    (hM : off + Lg + (r4 + 4) * G ≤ Mlab) (rowF : ℕ → List Bool) (hrows : ∀ j ≤ J, (rowF j).length = L)
    (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).length,
      readTapeBit (τ.st S) (τ.sh S + i) = ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap) (hsc : s' ≤ cap)
    (hcc : c + 1 ≤ cap) (cA : τ.val (X 0) + 2 + labCapA Lp d ≤ cap)
    (cB : τ.val (X 0) + 2 + (pieceA Lp d).length + labCapB r4 G off Lg Mlab ≤ cap)
    (hc : τ.val (X 0) + (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
      sgn c neg).length ≤ cap) :
    ∃ n, WExec cap (blockW O S X neg) τ
      (lSt O S (X 0) τ (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
        sgn c neg) (τ.sh S + (J + 1) * (2 * L + 1))) n ∧
      n ≤ blockBound cap J M s' c Lp d r4 G off Lg := by
  have hF0 : (pF.trans X) 0 = X 0 := rfl
  rw [blockE_length] at hc
  have e1 := emitW_spec cap O (X 0) [true, true] τ ho (by simp only [List.length_cons, List.length_nil]; omega)
  rw [← lSt_self (S := S) hOS] at e1
  have hB1 := hB.lSt (O := O) (S := S) [true, true] (τ.sh S)
  obtain ⟨nA, eA, bA⟩ := phaseA_spec cap O S (pF.trans X) hOS (lSt O S (X 0) τ [true, true] (τ.sh S)) []
    hB1.h19 (hB1.hz1 9 (by decide) (by decide)) (lSt_ho hOS τ ho _ _) Lp d hB1.h13 hB1.h14
    (by rw [hF0, lSt_val_self]; unfold labCapA at cA; simp only [List.length_cons, List.length_nil]; omega)
  rw [fSt_zero, fSt_zero_s hOS, hF0, lSt_append hOS, List.nil_append] at eA
  have hB2 := hB.lSt (O := O) (S := S) ([true, true] ++ pieceA Lp d) (τ.sh S)
  obtain ⟨nB, eB, bB⟩ := phaseB_spec cap O S (pF.trans X) hOS (lSt O S (X 0) τ ([true, true] ++ pieceA Lp d) (τ.sh S))
    [] (hB2.hz1 9 (by decide) (by decide)) (lSt_ho hOS τ ho _ _) r4 G off Lg hB2.h1 hB2.h2 hB2.h3 hB2.h4
    (hB2.hz1 5 (by decide) (by decide)) (hB2.hz1 6 (by decide) (by decide)) (hB2.hz1 7 (by decide) (by decide))
    (hB2.hz1 8 (by decide) (by decide)) (hB2.hz1 10 (by decide) (by decide)) (hB2.hz1 11 (by decide) (by decide))
    (hB2.hz1 12 (by decide) (by decide)) Mlab hM _ _ rfl rfl
    (by
      rw [hF0, lSt_val_self]
      refine le_trans (le_of_eq ?_) cB
      unfold labCapB
      simp only [List.length_append, List.length_cons, List.length_nil]
      ring)
  rw [fSt_zero, fSt_zero_s hOS, hF0, lSt_append hOS, List.nil_append] at eB
  obtain ⟨u2, hu2⟩ : ∃ x, x = [true, true] ++ pieceA Lp d ++ pieceB (sliceLabs r4 G off Lg)
      (labSum (sliceLabs r4 G off Lg)) := ⟨_, rfl⟩
  have hl2 : u2.length = 2 + (pieceA Lp d).length +
      (pieceB (sliceLabs r4 G off Lg) (labSum (sliceLabs r4 G off Lg))).length := by
    rw [hu2]; simp only [List.length_append, List.length_cons, List.length_nil]
  rw [← hu2] at eB
  have hB3 := hB.lSt (O := O) (S := S) u2 (τ.sh S)
  obtain ⟨nD, eD, bD⟩ := dataW_spec cap O S X hOS neg (lSt O S (X 0) τ u2 (τ.sh S)) M Sv J L s' c sgn rowF hrows
    hB3.h20 hB3.h21 hB3.h44 hB3.h45 hB3.hz2 hB3.h46 hB3.h47 hB3.h48 hB3.h49 hB3.h50 hB3.h51 hB3.h61 hB3.h62
    (lSt_ho hOS τ ho _ _) (by rw [lSt_stS hOS, lSt_shS]; exact hS) hcap
    (by rw [lSt_val_self, hl2]; omega) hJc hLc hMc hsc hcc
  rw [lSt_lSt hOS, lSt_shS] at eD
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq eA (WExec.seq eB eD))) ?_ le_rfl, ?_⟩
  · rw [hu2]; unfold blockE; simp only [List.append_assoc]
  · unfold blockBound
    generalize dataBound cap J M s' c = DB at bD ⊢
    generalize labSum (sliceLabs r4 G off Lg) = CAP at bB ⊢
    generalize labsCost r4 G off Lg = LC at bB ⊢
    clear * - bA bB bD
    simp only [List.length_cons, List.length_nil]
    omega

end Block

/-! ## A visit -/

section Visit
variable (O S : Fin (ns + 1)) (X : PReg nr)

/-- **A visit's two blocks**: past the visit's marker, the block with `neg = true`, the table stream rewound by the
visit's rows' length (`57`), the block with `neg = false`. -/
def visitW : WM ns nr :=
  .seq (.fwd S)
  (.seq (blockW O S X true)
  (.seq (FinalPass.Hash4.wcopyR (X 57) (X 61) (X 62))
  (.seq (WM.rewind S (X 61))
  (blockW O S X false))))

theorem visitW_spec (hOS : O ≠ S) (τ : WState ns nr) (Lp d r4 G off Lg Sv J M L s' c : ℕ)
    (sgn : Bool) (hB : BlockRegs X τ Lp d r4 G off Lg Sv J M L s' c ((J + 1) * (2 * L + 1)) sgn) (Mlab : ℕ)
    (hM : off + Lg + (r4 + 4) * G ≤ Mlab) (rowF : ℕ → List Bool) (hrows : ∀ j ≤ J, (rowF j).length = L)
    (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).length,
      readTapeBit (τ.st S) (τ.sh S + 1 + i) =
        ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hJc : J + 1 ≤ cap) (hLc : L ≤ cap) (hMc : M ≤ cap) (hsc : s' ≤ cap)
    (hcc : c + 1 ≤ cap) (hVc : (J + 1) * (2 * L + 1) ≤ cap)
    (cA : τ.val (X 0) + (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
      sgn c true).length + 2 + labCapA Lp d ≤ cap)
    (cB : τ.val (X 0) + (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
      sgn c true).length + 2 + (pieceA Lp d).length + labCapB r4 G off Lg Mlab ≤ cap)
    (hc : τ.val (X 0) + (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
      sgn c true ++ blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
      sgn c false).length ≤ cap) :
    ∃ n, WExec cap (visitW O S X) τ
      (lSt O S (X 0) τ (blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
        sgn c true ++ blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF) s'
        sgn c false) (τ.sh S + 1 + (J + 1) * (2 * L + 1))) n ∧
      n ≤ 2 * blockBound cap J M s' c Lp d r4 G off Lg + 30 * cap + 20 := by
  have hne : ∀ {i k : Fin 64}, i ≠ k → X i ≠ X k := fun h => X.injective.ne h
  have n0 : ∀ i : Fin 64, i ≠ 0 → X i ≠ X 0 := fun i h => hne h
  have hlTF := blockE_length_neg Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg) (levelE M Sv J rowF)
    s' sgn c
  obtain ⟨bT, hbT⟩ : ∃ x, x = blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg)
      (levelE M Sv J rowF) s' sgn c true := ⟨_, rfl⟩
  obtain ⟨bF, hbF⟩ : ∃ x, x = blockE Lp d (labSum (sliceLabs r4 G off Lg)) (sliceLabs r4 G off Lg)
      (levelE M Sv J rowF) s' sgn c false := ⟨_, rfl⟩
  rw [← hbT, ← hbF] at hlTF
  rw [← hbT] at cA cB
  rw [← hbT, ← hbF, List.length_append] at hc
  rw [← hbT, ← hbF]
  obtain ⟨VW, hVW⟩ : ∃ x, x = (J + 1) * (2 * L + 1) := ⟨_, rfl⟩
  rw [← hVW] at hB hVc ⊢
  have e1 := WExec.fwd (cap := cap) S τ
  rw [show τ.seth S (τ.sh S + 1) = lSt O S (X 0) τ [] (τ.sh S + 1) by unfold lSt; rw [appendO_nil]] at e1
  obtain ⟨n2, e2, b2⟩ := blockW_spec cap O S X hOS true (lSt O S (X 0) τ [] (τ.sh S + 1)) Lp d r4 G off Lg Sv J M L
    s' c VW sgn (hB.lSt [] _) Mlab hM rowF hrows (lSt_ho hOS τ ho _ _)
    (by rw [lSt_stS hOS, lSt_shS]; exact hS) hcap hJc hLc hMc hsc hcc
    (by rw [lSt_val_self]; simp only [List.length_nil]; omega)
    (by rw [lSt_val_self]; simp only [List.length_nil]; omega)
    (by rw [lSt_val_self, ← hbT]; simp only [List.length_nil]; omega)
  rw [lSt_lSt hOS, lSt_shS, List.nil_append, ← hbT, ← hVW] at e2
  have e3 := FinalPass.Hash4.wcopyR_spec cap (X 57) (X 61) (X 62) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (lSt O S (X 0) τ bT (τ.sh S + 1 + VW)) (by rw [lSt_val_ne (n0 61 (by decide))]; exact hB.h61)
    (by rw [lSt_val_ne (n0 62 (by decide))]; exact hB.h62) (by rw [lSt_val_ne (n0 57 (by decide)), hB.h57]; exact hVc)
  rw [lSt_val_ne (n0 57 (by decide)), hB.h57, lSt_setv _ _ _ _ (n0 61 (by decide))] at e3
  have e4 := wrewind_spec cap S (X 61) VW (lSt O S (X 0) (τ.setv (X 61) VW) bT (τ.sh S + 1 + VW))
    (by rw [lSt_val_ne (n0 61 (by decide))]; simp) (by rw [lSt_val_ne (n0 61 (by decide))]; simp; exact hVc)
  rw [lSt_setv _ _ _ _ (n0 61 (by decide)), lSt_seth, lSt_shS, wsetv_setv, setv_eq_self hB.h61,
    show τ.sh S + 1 + VW - VW = τ.sh S + 1 by omega] at e4
  obtain ⟨n5, e5, b5⟩ := blockW_spec cap O S X hOS false (lSt O S (X 0) τ bT (τ.sh S + 1)) Lp d r4 G off Lg Sv J M L
    s' c VW sgn (hB.lSt bT _) Mlab hM rowF hrows (lSt_ho hOS τ ho _ _)
    (by rw [lSt_stS hOS, lSt_shS]; exact hS) hcap hJc hLc hMc hsc hcc
    (by rw [lSt_val_self]; omega) (by rw [lSt_val_self]; omega) (by rw [lSt_val_self, ← hbF]; omega)
  rw [lSt_lSt hOS, lSt_shS, ← hbF, ← hVW] at e5
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) rfl le_rfl, ?_⟩
  generalize blockBound cap J M s' c Lp d r4 G off Lg = BB at b2 b5 ⊢
  clear * - b2 b5 hVc
  omega

end Visit

end NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW
