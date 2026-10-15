import Proof.Wire_3_5.PrimAsmLevelW
import Proof.Wire_3_5.PrimAsmPopRec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Copying a framed row -/

def rowLoop (O S : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.fwd S) (.seq (.ifs S (emitW O OP (m2 true)) (emitW O OP (m2 false))) (.fwd S))))

theorem rowLoop_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP K : Fin nr) (hKO : K ≠ OP) (row : List Bool)
    (σ : WState ns nr) (hKn : σ.val K = row.length)
    (hr : ∀ i < row.length, readTapeBit (σ.st S) (σ.sh S + 2 * i + 1) = row.getD i false)
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 * row.length ≤ cap) (hn : row.length ≤ cap) :
    WExec cap (rowLoop O S OP K) σ
      (((appendO σ O OP (row.flatMap m2)).seth S (σ.sh S + 2 * row.length)).setv K 0)
      (row.length * (37 + 4) + 1) := by
  let S' : ℕ → WState ns nr := fun k =>
    ((appendO σ O OP ((row.take k).flatMap m2)).seth S (σ.sh S + 2 * k)).setv K (row.length - k)
  have hS0 : S' 0 = σ := by
    simp only [S', List.take_zero, List.flatMap_nil, appendO_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, ← hKn]
    apply WState.eq <;> simp [Function.update_eq_self]
  have hloop := UnionMachine.Round.wloop cap K
    (.seq (.fwd S) (.seq (.ifs S (emitW O OP (m2 true)) (emitW O OP (m2 false))) (.fwd S))) 37 row.length S'
    (fun k _ => by simp [S'])
    hn
    (fun k hk => by
      set τ := ((appendO σ O OP ((row.take k).flatMap m2)).seth S (σ.sh S + 2 * k)).setv K
        (row.length - k - 1) with hτ
      have hτS : (S' k).setv K (row.length - k - 1) = τ := by simp only [S', hτ, wsetv_setv]
      rw [hτS]
      have hlen : ((row.take k).flatMap m2).length = 4 * k := by
        rw [List.length_flatMap]
        simp only [m2, List.length_cons, List.length_nil]
        rw [List.map_const', List.sum_replicate, List.length_take, min_eq_left (by omega)]
        ring
      have h1 := WExec.fwd (cap := cap) S τ
      set τ1 := τ.seth S (τ.sh S + 1) with hτ1
      have hbit : wbit τ1 S = row.getD k false := by
        have := hr k hk
        simp only [hτ1, hτ, wbit]
        simp [hOS.symm, Function.update_apply]
        exact this
      have hoτ : τ1.sh O = (τ1.st O).length := by simp [hτ1, hτ, hOS, ho]
      have hcτ : τ1.val OP + (m2 (row.getD k false)).length ≤ cap := by
        simp only [hτ1, hτ]
        simp [Function.update_apply, Ne.symm hKO, hlen, m2]
        omega
      have hE : WExec cap (.ifs S (emitW O OP (m2 true)) (emitW O OP (m2 false))) τ1
          (appendO τ1 O OP (m2 (row.getD k false))) (8 * 4 + 1) := by
        cases hb : row.getD k false
        · rw [hb] at hbit hcτ
          exact WExec.ifsF hbit (emitW_spec cap O OP (m2 false) τ1 hoτ hcτ)
        · rw [hb] at hbit hcτ
          exact WExec.ifsT hbit (emitW_spec cap O OP (m2 true) τ1 hoτ hcτ)
      have h3 := WExec.fwd (cap := cap) S (appendO τ1 O OP (m2 (row.getD k false)))
      refine WExec.cast cap (WExec.seq h1 (WExec.seq hE h3)) ?_ (by omega)
      have htake : (row.take (k + 1)).flatMap m2 = (row.take k).flatMap m2 ++ m2 (row.getD k false) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append,
          List.getD_eq_getElem _ _ hk]
        simp
      simp only [S', hτ1, hτ, htake]
      apply WState.eq
      · funext j
        by_cases hjS : j = S
        · subst hjS; simp [Function.update_apply, Ne.symm hOS]; omega
        · by_cases hj : j = O
          · subst hj; simp [Function.update_apply, hjS]; try omega
          · simp [Function.update_apply, hj, hjS]
      · funext j; by_cases hj : j = O
        · subst hj; simp [hOS]
        · simp [Function.update_apply, hj]
      · funext j; by_cases hj : j = K
        · subst hj; simp [Function.update_apply, hKO]; omega
        · by_cases hjO : j = OP
          · subst hjO; simp [Function.update_apply, hj]; omega
          · simp [Function.update_apply, hj, hjO]
      · simp)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp only [S', List.take_length, Nat.sub_self]

/-! ## The table word at level 2 -/

/-- Level `j`'s record at level 2: its marker, `pow W'_j`, `W'_j` (from `S = natCeilSqrt(64²B)`), its row. -/
def levelRecE (Sv J j : ℕ) (row : List Bool) : List Bool :=
  m2 true ++ (reps (2 ^ Nat.clog 2 (2 * winAt Sv J j + 1)) (m2 true) ++ m2 false) ++
    (reps (winAt Sv J j) (m2 true) ++ m2 false) ++ row.flatMap m2

/-- **The table word at level 2**: `M`, the records of levels `J, …, 0`, the end. -/
def levelE (M Sv J : ℕ) (rowF : ℕ → List Bool) : List Bool :=
  (reps M (m2 true) ++ m2 false) ++ (FinalPass.ListEval.levels J).flatMap (fun j => levelRecE Sv J j (rowF j)) ++
    m2 false

theorem unary_m2 (n : ℕ) : (FinalPass.ListEval.unary n).flatMap m2 = reps n (m2 true) ++ m2 false := by
  rw [unary_eq, List.flatMap_append, flatMap_replicate]; rfl

theorem levelE_eq (P : Lists.BaseListParams) (rowF : ℕ → List Bool) :
    (FinalPass.ListEval.levelWord P.M P.J P.W rowF).flatMap m2 =
      levelE P.M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B)) P.J rowF := by
  unfold FinalPass.ListEval.levelWord levelE
  rw [List.flatMap_append, List.flatMap_append, unary_m2, List.flatMap_assoc]
  congr 2
  refine List.flatMap_congr fun j _ => ?_
  unfold FinalPass.ListEval.record levelRecE
  rw [List.flatMap_cons, List.flatMap_append, List.flatMap_append, unary_m2, unary_m2, ← winAt_eq]
  rfl

theorem levelRecE_length (Sv J j : ℕ) (row : List Bool) :
    (levelRecE Sv J j row).length = 4 + (4 * 2 ^ Nat.clog 2 (2 * winAt Sv J j + 1) + 4) +
      (4 * winAt Sv J j + 4) + 4 * row.length := by
  unfold levelRecE
  simp only [List.length_append, FiltRecW.reps_length, m2, List.length_cons, List.length_nil, List.length_flatMap]
  rw [List.map_const', List.sum_replicate]
  simp; ring

/-! ## The writer's state -/

section LSt
variable (O S : Fin (ns + 1)) (OP : Fin nr)

/-- The output extended by `u`, the row stream's head at `h`. -/
def lSt (τ : WState ns nr) (u : List Bool) (h : ℕ) : WState ns nr := (appendO τ O OP u).seth S h

variable {O S OP}

theorem lSt_val (τ : WState ns nr) (u : List Bool) (h : ℕ) :
    (lSt O S OP τ u h).val = Function.update τ.val OP (τ.val OP + u.length) := by
  simp [lSt]

theorem lSt_shO (hOS : O ≠ S) (τ : WState ns nr) (u : List Bool) (h : ℕ) :
    (lSt O S OP τ u h).sh O = τ.sh O + u.length := by
  simp [lSt, Function.update_apply, hOS]

theorem lSt_shS (τ : WState ns nr) (u : List Bool) (h : ℕ) : (lSt O S OP τ u h).sh S = h := by
  simp [lSt]

theorem lSt_stO (τ : WState ns nr) (u : List Bool) (h : ℕ) : (lSt O S OP τ u h).st O = τ.st O ++ u := by
  simp [lSt]

theorem lSt_stS (hOS : O ≠ S) (τ : WState ns nr) (u : List Bool) (h : ℕ) : (lSt O S OP τ u h).st S = τ.st S := by
  simp [lSt, Function.update_apply, Ne.symm hOS]

theorem lSt_append (hOS : O ≠ S) (τ : WState ns nr) (u v : List Bool) (h : ℕ) :
    appendO (lSt O S OP τ u h) O OP v = lSt O S OP τ (u ++ v) h := by
  unfold lSt appendO
  apply WState.eq
  · funext j
    by_cases hjO : j = O
    · subst hjO; simp [Function.update_apply, hOS]; omega
    · by_cases hjS : j = S
      · subst hjS; simp [Function.update_apply, hjO]
      · simp [Function.update_apply, hjO, hjS]
  · funext j
    by_cases hjO : j = O
    · subst hjO; simp [Function.update_apply]
    · simp [Function.update_apply, hjO]
  · funext j
    by_cases hj : j = OP
    · subst hj; simp [Function.update_apply]; omega
    · simp [Function.update_apply, hj]
  · simp

theorem lSt_setv (τ : WState ns nr) (u : List Bool) (h : ℕ) (r : Fin nr) (hr : r ≠ OP) (x : ℕ) :
    (lSt O S OP τ u h).setv r x = lSt O S OP (τ.setv r x) u h := by
  unfold lSt
  rw [appendO_setv _ O OP r hr]
  rfl

theorem lSt_seth (τ : WState ns nr) (u : List Bool) (h h' : ℕ) :
    (lSt O S OP τ u h).seth S h' = lSt O S OP τ u h' := by
  unfold lSt
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · rfl
  · rfl

theorem lSt_nil (τ : WState ns nr) : lSt O S OP τ [] (τ.sh S) = τ := by
  unfold lSt
  rw [appendO_nil]
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · rfl
  · rfl

theorem lSt_lSt (hOS : O ≠ S) (τ : WState ns nr) (u v : List Bool) (h h' : ℕ) :
    lSt O S OP (lSt O S OP τ u h) v h' = lSt O S OP τ (u ++ v) h' := by
  unfold lSt
  rw [show appendO ((appendO τ O OP u).seth S h) O OP v = lSt O S OP τ (u ++ v) h from lSt_append hOS τ u v h]
  exact lSt_seth τ (u ++ v) h h'

end LSt

section LSt2
variable {O S : Fin (ns + 1)} {OP : Fin nr}

theorem lSt_self (hOS : O ≠ S) (τ : WState ns nr) (v : List Bool) : lSt O S OP τ v (τ.sh S) = appendO τ O OP v := by
  unfold lSt
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp [Function.update_apply, Ne.symm hOS]
    · simp [Function.update_apply, hj]
  · rfl
  · rfl
  · rfl

end LSt2

/-! ## One level -/

/-- The level registers inside the writer's: `W 0`–`W 23` are `LevelW`'s (`0 S`, `1 J`, `2 j`, `3 W`, `4 P`, scratch). -/
def lwV : Fin 24 ↪ Fin 30 := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩

section Body
variable (O S : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr)

/-- **One level** (the writer's registers: `0`–`23` the level block, `24` output counter, `25 M`, `26 L`, `27` the
loop counter `= j`, `28` the row counter, `29` scratch): compute `W'_j`, `pow W'_j`; write the record at level 2;
copy the row from stream `S`. -/
def lvBody : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (W 27) (W 2) (W 29))
  (.seq (levelVals (lwV.trans W))
  (.seq (emitW O (W 24) (m2 true))
  (.seq (repW O (W 24) (W 4) (m2 true))
  (.seq (emitW O (W 24) (m2 false))
  (.seq (repW O (W 24) (W 3) (m2 true))
  (.seq (emitW O (W 24) (m2 false))
  (.seq (FinalPass.Hash4.wcopyR (W 26) (W 28) (W 29))
  (.seq (rowLoop O S (W 24) (W 28))
  (.seq (.fwd S)
  (WM.clear (W 2)))))))))))

/-- A bound on one level's cost. -/
def lvBodyBound (cap : ℕ) : ℕ := 4 * phBound cap + 200 * (cap + 10)

theorem lvBody_spec (hOS : O ≠ S) (τ : WState ns nr) (Sv J j : ℕ) (row : List Bool)
    (h0 : τ.val (W 0) = Sv) (h1 : τ.val (W 1) = J) (h27 : τ.val (W 27) = j) (hjJ : j ≤ J)
    (hz : ∀ i : Fin 30, 2 ≤ i.val → i.val ≤ 23 → τ.val (W i) = 0) (h28 : τ.val (W 28) = 0)
    (h29 : τ.val (W 29) = 0) (h26 : τ.val (W 26) = row.length) (ho : τ.sh O = (τ.st O).length)
    (hrow : ∀ i < row.length, readTapeBit (τ.st S) (τ.sh S + 2 * i + 1) = row.getD i false)
    (hcap : lvCap Sv J j ≤ cap) (hc : τ.val (W 24) + (levelRecE Sv J j row).length ≤ cap)
    (hjc : j ≤ cap) (hLc : row.length ≤ cap) :
    ∃ n, WExec cap (lvBody O S W) τ (lSt O S (W 24) τ (levelRecE Sv J j row) (τ.sh S + (2 * row.length + 1))) n ∧
      n ≤ lvBodyBound cap := by
  have hR : ∀ i k : Fin 30, W i = W k ↔ i = k := fun i k => W.injective.eq_iff
  have hne : ∀ {i k : Fin 30}, i ≠ k → W i ≠ W k := fun h => W.injective.ne h
  have hlen := levelRecE_length Sv J j row
  generalize hw : winAt Sv J j = w at hlen
  generalize hp : 2 ^ Nat.clog 2 (2 * w + 1) = p at hlen
  have hV : ∀ i : Fin 24, (lwV.trans W) i = W ⟨i.val, by omega⟩ := fun i => rfl
  have hV0 : (lwV.trans W) 0 = W 0 := rfl
  have hV1 : (lwV.trans W) 1 = W 1 := rfl
  have hV2 : (lwV.trans W) 2 = W 2 := rfl
  have hV3 : (lwV.trans W) 3 = W 3 := rfl
  have hV4 : (lwV.trans W) 4 = W 4 := rfl
  have h2z := hz 2 (by decide) (by decide)
  have h3z := hz 3 (by decide) (by decide)
  have h4z := hz 4 (by decide) (by decide)
  -- the level's numbers
  have e1 := FinalPass.Hash4.wcopyR_spec cap (W 27) (W 2) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h2z h29 (by omega)
  rw [h27] at e1
  obtain ⟨n2, e2, b2⟩ := levelVals_spec cap (lwV.trans W) (τ.setv (W 2) j) Sv J j
    (by rw [hV0]; simp [hR, h0]) (by rw [hV1]; simp [hR, h1]) (by rw [hV2]; simp) hjJ
    (fun i hi => by
      have h2 : (⟨i.val, by omega⟩ : Fin 30) ≠ 2 := Fin.ne_of_val_ne (by show i.val ≠ 2; omega)
      rw [hV i, wsetv_val_ne _ _ (hne h2)]
      exact hz _ (by show 2 ≤ i.val; omega) (by show i.val ≤ 23; omega))
    hcap
  rw [hV3, hV4, hw, hp] at e2
  -- the record
  set ρ2 := ((τ.setv (W 2) j).setv (W 3) w).setv (W 4) p with hρ2
  have hsh2 : ρ2.sh = τ.sh := rfl
  have hst2 : ρ2.st = τ.st := rfl
  have hv2 : ρ2.val (W 24) = τ.val (W 24) := by simp [hρ2, hR]
  have e3 := emitW_spec cap O (W 24) (m2 true) ρ2 (by rw [hsh2, hst2]; exact ho)
    (by rw [hv2]; simp only [m2, List.length_cons, List.length_nil]; omega)
  rw [← lSt_self (S := S) hOS, hsh2] at e3
  have e4 := repW_spec cap O (W 24) (W 4) (hne (by decide)) (m2 true) p (lSt O S (W 24) ρ2 (m2 true) (τ.sh S))
    (by rw [lSt_val]; simp [hρ2, hR]) (by rw [lSt_shO hOS, lSt_stO, hsh2, hst2, ho]; simp)
    (by rw [lSt_val]; simp [hR, hv2, m2]; omega) (by omega)
  rw [lSt_append hOS, lSt_setv _ _ _ _ (hne (by decide))] at e4
  set ρ4 := ρ2.setv (W 4) 0 with hρ4
  have e5 := emitW_spec cap O (W 24) (m2 false) (lSt O S (W 24) ρ4 (m2 true ++ reps p (m2 true)) (τ.sh S))
    (by rw [lSt_shO hOS, lSt_stO]; simp [hρ4, hsh2, hst2, ho])
    (by rw [lSt_val]; simp [hρ4, hR, hv2, m2, FiltRecW.reps_length]; omega)
  rw [lSt_append hOS] at e5
  have e6 := repW_spec cap O (W 24) (W 3) (hne (by decide)) (m2 true) w
    (lSt O S (W 24) ρ4 (m2 true ++ reps p (m2 true) ++ m2 false) (τ.sh S))
    (by rw [lSt_val]; simp [hρ4, hρ2, hR]) (by rw [lSt_shO hOS, lSt_stO]; simp [hρ4, hsh2, hst2, ho])
    (by rw [lSt_val]; simp [hρ4, hR, hv2, m2, FiltRecW.reps_length]; omega) (by omega)
  rw [lSt_append hOS, lSt_setv _ _ _ _ (hne (by decide))] at e6
  set ρ6 := ρ4.setv (W 3) 0 with hρ6
  have e7 := emitW_spec cap O (W 24) (m2 false)
    (lSt O S (W 24) ρ6 (m2 true ++ reps p (m2 true) ++ m2 false ++ reps w (m2 true)) (τ.sh S))
    (by rw [lSt_shO hOS, lSt_stO]; simp [hρ6, hρ4, hsh2, hst2, ho])
    (by rw [lSt_val]; simp [hρ6, hρ4, hR, hv2, m2, FiltRecW.reps_length]; omega)
  rw [lSt_append hOS] at e7
  -- the row
  set u7 := m2 true ++ reps p (m2 true) ++ m2 false ++ reps w (m2 true) ++ m2 false with hu7
  have hu7l : u7.length = 4 * p + 4 * w + 12 := by
    simp [hu7, m2, FiltRecW.reps_length]; omega
  have e8 := FinalPass.Hash4.wcopyR_spec cap (W 26) (W 28) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (lSt O S (W 24) ρ6 u7 (τ.sh S)) (by rw [lSt_val]; simp [hρ6, hρ4, hρ2, hR, h28])
    (by rw [lSt_val]; simp [hρ6, hρ4, hρ2, hR, h29]) (by rw [lSt_val]; simp [hρ6, hρ4, hρ2, hR, h26]; omega)
  rw [show (lSt O S (W 24) ρ6 u7 (τ.sh S)).val (W 26) = row.length by
    rw [lSt_val]; simp [hρ6, hρ4, hρ2, hR, h26], lSt_setv _ _ _ _ (hne (by decide))] at e8
  set ρ8 := ρ6.setv (W 28) row.length with hρ8
  have e9 := rowLoop_spec cap O S hOS (W 24) (W 28) (hne (by decide)) row (lSt O S (W 24) ρ8 u7 (τ.sh S))
    (by rw [lSt_val]; simp [hρ8, hR])
    (fun i hi => by rw [lSt_stS hOS, lSt_shS]; simp only [hρ8, hρ6, hρ4, hρ2, WState.setv]; exact hrow i hi)
    (by rw [lSt_shO hOS, lSt_stO]; simp [hρ8, hρ6, hρ4, hsh2, hst2, ho])
    (by rw [lSt_val]; simp [hρ8, hρ6, hρ4, hR, hv2]; omega) hLc
  rw [lSt_append hOS, lSt_shS, lSt_seth, lSt_setv _ _ _ _ (hne (by decide))] at e9
  set ρ9 := ρ8.setv (W 28) 0 with hρ9
  have e10 := WExec.fwd (cap := cap) S (lSt O S (W 24) ρ9 (u7 ++ row.flatMap m2) (τ.sh S + 2 * row.length))
  rw [lSt_shS, lSt_seth] at e10
  have e11 := wclear_spec cap (W 2) j (lSt O S (W 24) ρ9 (u7 ++ row.flatMap m2) (τ.sh S + 2 * row.length + 1))
    (by rw [lSt_val]; simp [hρ9, hρ8, hρ6, hρ4, hρ2, hR]) (by rw [lSt_val]; simp [hρ9, hρ8, hρ6, hρ4, hρ2, hR]; omega)
  rw [lSt_setv _ _ _ _ (hne (by decide))] at e11
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11)))))))))) ?_ le_rfl, ?_⟩
  · have hρ : ρ9.setv (W 2) 0 = τ := by
      apply WState.eq
      · rfl
      · rfl
      · funext x
        simp only [hρ9, hρ8, hρ6, hρ4, hρ2, WState.setv_val, Function.update_apply]
        by_cases x2 : x = W 2
        · subst x2; simp [hR, h2z]
        · by_cases x28 : x = W 28
          · subst x28; simp [hR, h28]
          · by_cases x3 : x = W 3
            · subst x3; simp [hR, h3z]
            · by_cases x4 : x = W 4
              · subst x4; simp [hR, h4z]
              · simp [x2, x28, x3, x4]
      · rfl
    rw [hρ]
    have hu : u7 ++ row.flatMap m2 = levelRecE Sv J j row := by
      rw [hu7]; unfold levelRecE; rw [hw, hp]; simp only [List.append_assoc]
    rw [hu, show τ.sh S + 2 * row.length + 1 = τ.sh S + (2 * row.length + 1) by omega]
  · unfold lvBodyBound
    have hF : cap + 2 ≤ phBound cap := by
      unfold phBound
      have : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_self _
      have hE : 2000 * (cap + 2) * (cap + 2) = 2000 * ((cap + 2) * (cap + 2)) := by ring
      omega
    have hpc : p ≤ cap := by omega
    have hwc : w ≤ cap := by omega
    have hA : p * (8 * (m2 true).length + 4) = 36 * p := by simp [m2]; ring
    have hB : w * (8 * (m2 true).length + 4) = 36 * w := by simp [m2]; ring
    simp only [m2, List.length_cons, List.length_nil] at hA hB ⊢
    omega

end Body

/-! ## The whole table word -/

theorem getD_flatMap_block {α : Type} (f : α → List Bool) (m : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = m) → ∀ (k : ℕ) (hk : k < l.length) (i : ℕ), i < m →
      (l.flatMap f).getD (k * m + i) false = (f l[k]).getD i false
  | [], _, k, hk, _, _ => absurd hk (by simp)
  | a :: l, hl, k, hk, i, hi => by
    rw [List.flatMap_cons]
    have ha := hl a List.mem_cons_self
    cases k with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by rw [ha]; exact hi)]
    | succ k =>
      rw [List.getD_append_right _ _ _ _ (by rw [ha, Nat.succ_mul]; omega)]
      rw [ha, show (k + 1) * m + i - m = k * m + i by rw [Nat.succ_mul]; omega, List.getElem_cons_succ]
      exact getD_flatMap_block f m l (fun b hb => hl b (List.mem_cons_of_mem a hb)) k
        (by simp only [List.length_cons] at hk; omega) i hi

theorem frame_getD_odd (r : List Bool) (i : ℕ) (hi : i < r.length) :
    (frame r).getD (2 * i + 1) false = r.getD i false := by
  rw [frame_eq, marks_eq, List.getD_append _ _ _ _ (by rw [List.length_flatMap]; simp; omega)]
  have h := getD_flatMap_block (fun b : Bool => [true, b]) 2 r (fun _ _ => rfl) i hi 1 (by omega)
  rw [show i * 2 + 1 = 2 * i + 1 by ring] at h
  rw [h, List.getD_eq_getElem _ _ hi]
  rfl

theorem levels_length (J : ℕ) : (FinalPass.ListEval.levels J).length = J + 1 := by
  simp [FinalPass.ListEval.levels]

theorem levels_getElem (J k : ℕ) (hk : k < (FinalPass.ListEval.levels J).length) :
    (FinalPass.ListEval.levels J)[k] = J - k := by
  unfold FinalPass.ListEval.levels
  rw [List.getElem_reverse, List.getElem_range]
  simp only [List.length_range]
  omega

theorem lvCap_mono (Sv J j : ℕ) (hj : j ≤ J) : lvCap Sv J j ≤ lvCap Sv J J := by
  unfold lvCap
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.div_le_div_right (c := 3) hj)
  omega

theorem flatMap_take_length_le {α : Type} (l : List α) (f : α → List Bool) (m : ℕ) :
    ((l.take m).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop m l]
  rw [List.flatMap_append, List.length_append]
  omega

section Word
variable (O S : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr)

/-- **The table word, written**: `M`, the levels `J, …, 0` (loop counter `27`), the end. -/
def lvWordW : WM ns nr :=
  .seq (repRegW O (W 24) (W 25) (W 28) (W 29) (m2 true))
  (.seq (emitW O (W 24) (m2 false))
  (.seq (FinalPass.Hash4.wcopyR (W 1) (W 27) (W 29))
  (.seq (.inc (W 27))
  (.seq (.whr (W 27) (.seq (.dec (W 27)) (lvBody O S W)))
  (emitW O (W 24) (m2 false))))))

/-- A bound on the table word's cost. -/
def lvWordBound (cap J M : ℕ) : ℕ := 54 * M + 18 * J + 100 + (J + 1) * (lvBodyBound cap + 4)

/-- **The visited list's table word at level 2, written** from its rows on stream `S` (the visit's word after its
marker: `frame (row j)` for `j = J, …, 0`), `S = natCeilSqrt(64²B)` in `W 0`, `J` in `W 1`, `M` in `W 25`, `L` in
`W 26`. -/
theorem lvWordW_spec (hOS : O ≠ S) (τ : WState ns nr) (M Sv J L : ℕ) (rowF : ℕ → List Bool)
    (hrows : ∀ j ≤ J, (rowF j).length = L)
    (h0 : τ.val (W 0) = Sv) (h1 : τ.val (W 1) = J) (h25 : τ.val (W 25) = M) (h26 : τ.val (W 26) = L)
    (hz : ∀ i : Fin 30, 2 ≤ i.val → i.val ≤ 23 → τ.val (W i) = 0) (h27 : τ.val (W 27) = 0)
    (h28 : τ.val (W 28) = 0) (h29 : τ.val (W 29) = 0) (ho : τ.sh O = (τ.st O).length)
    (hS : ∀ i < ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).length,
      readTapeBit (τ.st S) (τ.sh S + i) = ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).getD i false)
    (hcap : lvCap Sv J J ≤ cap) (hc : τ.val (W 24) + (levelE M Sv J rowF).length ≤ cap) (hJc : J + 1 ≤ cap)
    (hLc : L ≤ cap) (hMc : M ≤ cap) :
    ∃ n, WExec cap (lvWordW O S W) τ (lSt O S (W 24) τ (levelE M Sv J rowF) (τ.sh S + (J + 1) * (2 * L + 1))) n ∧
      n ≤ lvWordBound cap J M := by
  have hR : ∀ i k : Fin 30, W i = W k ↔ i = k := fun i k => W.injective.eq_iff
  have hne : ∀ {i k : Fin 30}, i ≠ k → W i ≠ W k := fun h => W.injective.ne h
  set f : ℕ → List Bool := fun j => levelRecE Sv J j (rowF j) with hf
  set pre := reps M (m2 true) ++ m2 false with hpre
  have hlE : levelE M Sv J rowF = pre ++ (FinalPass.ListEval.levels J).flatMap f ++ m2 false := rfl
  have hpl : pre.length = 4 * M + 4 := by simp [hpre, m2, FiltRecW.reps_length]; ring
  have hEl : (levelE M Sv J rowF).length = pre.length + ((FinalPass.ListEval.levels J).flatMap f).length + 4 := by
    rw [hlE]; simp [m2]; omega
  -- the preamble
  have e1 := repRegW_spec cap O (W 24) (W 25) (W 28) (W 29) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (m2 true) τ h28 h29 ho (by omega) (by rw [h25]; simp [m2]; omega)
  rw [h25] at e1
  have e2 := emitW_spec cap O (W 24) (m2 false) (appendO τ O (W 24) (reps M (m2 true))) (by simp [hOS, ho])
    (by simp [m2, FiltRecW.reps_length]; omega)
  rw [appendO_append, ← hpre] at e2
  have e3 := FinalPass.Hash4.wcopyR_spec cap (W 1) (W 27) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (appendO τ O (W 24) pre) (by simp [hR, h27]) (by simp [hR, h29]) (by simp [hR, h1]; omega)
  rw [show (appendO τ O (W 24) pre).val (W 1) = J by simp [hR, h1]] at e3
  have e4 := WExec.inc (cap := cap) (W 27) ((appendO τ O (W 24) pre).setv (W 27) J) (by simp; omega)
  rw [wsetv_setv, show ((appendO τ O (W 24) pre).setv (W 27) J).val (W 27) + 1 = J + 1 by simp] at e4
  -- the loop
  let S' : ℕ → WState ns nr := fun k =>
    lSt O S (W 24) (τ.setv (W 27) (J + 1 - k)) (pre ++ ((FinalPass.ListEval.levels J).take k).flatMap f)
      (τ.sh S + k * (2 * L + 1))
  have hS'0 : S' 0 = (appendO τ O (W 24) pre).setv (W 27) (J + 1) := by
    simp only [S', List.take_zero, List.flatMap_nil, List.append_nil, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    rw [← lSt_setv _ _ _ _ (hne (by decide)), lSt_self hOS]
  have hloop := UnionMachine.Round.wloop cap (W 27) (lvBody O S W) (lvBodyBound cap) (J + 1) S'
    (fun k _ => by simp only [S']; rw [lSt_val]; simp [hR])
    hJc
    (fun k hk => by
      have hkl : k < (FinalPass.ListEval.levels J).length := by rw [levels_length]; exact hk
      have hlk := levels_getElem J k hkl
      set τ' := lSt O S (W 24) (τ.setv (W 27) (J + 1 - k - 1)) (pre ++ ((FinalPass.ListEval.levels J).take k).flatMap f)
        (τ.sh S + k * (2 * L + 1)) with hτ'
      have hτS : (S' k).setv (W 27) (J + 1 - k - 1) = τ' := by
        simp only [S', hτ']
        rw [lSt_setv _ _ _ _ (hne (by decide)), wsetv_setv]
      rw [hτS]
      have htake : ((FinalPass.ListEval.levels J).take (k + 1)).flatMap f =
          ((FinalPass.ListEval.levels J).take k).flatMap f ++ f (J - k) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkl, Option.toList_some, List.flatMap_append, hlk]
        simp
      have hrl : (rowF (J - k)).length = L := hrows (J - k) (by omega)
      have hpref : pre.length + (((FinalPass.ListEval.levels J).take k).flatMap f).length + (f (J - k)).length ≤
          (levelE M Sv J rowF).length := by
        have := flatMap_take_length_le (FinalPass.ListEval.levels J) f (k + 1)
        rw [htake, List.length_append] at this
        omega
      have hblk : ∀ a ∈ FinalPass.ListEval.levels J, (frame (rowF a)).length = 2 * L + 1 := by
        intro a ha
        have haJ : a ≤ J := by
          unfold FinalPass.ListEval.levels at ha
          simp only [List.mem_reverse, List.mem_range] at ha
          omega
        rw [frame_length, hrows a haJ]
      have hwl : ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).length = (J + 1) * (2 * L + 1) := by
        rw [List.length_flatMap, List.map_congr_left (fun a ha => hblk a ha), List.map_const', List.sum_replicate,
          levels_length]
        simp
      have hcb : τ.val (W 24) + (pre ++ ((FinalPass.ListEval.levels J).take k).flatMap f).length +
          (levelRecE Sv J (J - k) (rowF (J - k))).length ≤ cap := by
        have : (f (J - k)).length = (levelRecE Sv J (J - k) (rowF (J - k))).length := rfl
        rw [List.length_append]
        omega
      obtain ⟨nb, eb, bb⟩ := lvBody_spec cap O S W hOS τ' Sv J (J - k) (rowF (J - k))
        (by rw [hτ', lSt_val]; simp [hR, h0]) (by rw [hτ', lSt_val]; simp [hR, h1])
        (by rw [hτ', lSt_val]; simp [hR]; omega) (by omega)
        (fun i h2 h23 => by
          have hi24 : W i ≠ W 24 := hne (Fin.ne_of_val_ne (by show i.val ≠ 24; omega))
          have hi27 : W i ≠ W 27 := hne (Fin.ne_of_val_ne (by show i.val ≠ 27; omega))
          rw [hτ', lSt_val, Function.update_of_ne hi24, wsetv_val_ne _ _ hi27]
          exact hz i h2 h23)
        (by rw [hτ', lSt_val]; simp [hR, h28]) (by rw [hτ', lSt_val]; simp [hR, h29])
        (by rw [hτ', lSt_val]; simp [hR, h26, hrl])
        (by rw [hτ', lSt_shO hOS, lSt_stO]; simp [ho])
        (fun i hi => by
          rw [hτ', lSt_stS hOS, lSt_shS]
          have hidx : k * (2 * L + 1) + (2 * i + 1) < ((FinalPass.ListEval.levels J).flatMap fun j => frame (rowF j)).length := by
            rw [hwl]
            have : k * (2 * L + 1) + (2 * L + 1) ≤ (J + 1) * (2 * L + 1) := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
            omega
          have h1' := hS _ hidx
          rw [getD_flatMap_block (fun j => frame (rowF j)) (2 * L + 1) _ hblk k hkl (2 * i + 1) (by omega), hlk,
            frame_getD_odd _ _ hi] at h1'
          simp only [WState.setv]
          rw [← h1']
          congr 1
          omega)
        (le_trans (lvCap_mono Sv J (J - k) (by omega)) hcap)
        (by rw [hτ', lSt_val, Function.update_self, wsetv_val_ne _ _ (hne (show (24 : Fin 30) ≠ 27 by decide))]
            exact hcb) (by omega) (by omega)
      refine WExec.mono (WExec.cast cap eb ?_ le_rfl) bb
      rw [hτ', lSt_lSt hOS, lSt_shS]
      simp only [S']
      rw [htake, List.append_assoc, hrl, show J + 1 - k - 1 = J + 1 - (k + 1) by omega,
        show τ.sh S + k * (2 * L + 1) + (2 * L + 1) = τ.sh S + (k + 1) * (2 * L + 1) by ring])
  rw [hS'0] at hloop
  have hall : ((FinalPass.ListEval.levels J).take (J + 1)).flatMap f = (FinalPass.ListEval.levels J).flatMap f := by
    rw [List.take_of_length_le (by rw [levels_length])]
  simp only [S', Nat.sub_self, hall] at hloop
  have e6 := emitW_spec cap O (W 24) (m2 false)
    (lSt O S (W 24) (τ.setv (W 27) 0) (pre ++ (FinalPass.ListEval.levels J).flatMap f) (τ.sh S + (J + 1) * (2 * L + 1)))
    (by rw [lSt_shO hOS, lSt_stO]; simp [ho])
    (by rw [lSt_val, Function.update_self, wsetv_val_ne _ _ (hne (show (24 : Fin 30) ≠ 27 by decide)),
          List.length_append]
        simp only [m2, List.length_cons, List.length_nil]
        omega)
  rw [lSt_append hOS] at e6
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq hloop e6))))) ?_
    le_rfl, ?_⟩
  · rw [setv_eq_self h27, ← hlE]
  · unfold lvWordBound
    simp only [m2, List.length_cons, List.length_nil]
    omega

end Word

end NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW
