import Proof.Gates.TabMachine.ExactVal
import Proof.Gates.WordPrograms.SInt
import Proof.Gates.WordPrograms.BinWDiv
import Proof.Gates.WordPrograms.Arr
import Proof.Gates.WordPrograms.OutX

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn split join split_spec join_spec encS_sval natAbs_sval)
open StablePartition.Workspace (overlay)

theorem emb_ne {α : Type} {k : ℕ} (S : Fin k ↪ α) {i j : Fin k} (h : i ≠ j) : S i ≠ S j :=
  fun e => h (S.injective e)

theorem emb_eq_iff {α : Type} {k : ℕ} (S : Fin k ↪ α) (i j : Fin k) : S i = S j ↔ i = j := S.injective.eq_iff

variable {ns nr : ℕ}

/-! ## The child's fields -/

/-- The signed field of index `j` of the child at `(bit, i)`. -/
def fieldJ (ws : List ℤ) (bit i j : ℕ) : ℤ := if ws.getD j 0 < 0 then -(litW ws bit i j : ℤ) else (litW ws bit i j : ℤ)

/-- The negative literal coefficients of the first `j` indices. -/
def negSum (ws : List ℤ) (bit i j : ℕ) : ℕ :=
  ((List.range j).map fun j' => if ws.getD j' 0 < 0 then litW ws bit i j' else 0).sum

/-- The record bits of a list of signed fields. -/
def recBits (W : ℕ) (zs : List ℤ) : List Bool := zs.flatMap fun z => binary (W + 1) (encS z)

theorem childL_eq (ws : List ℤ) (sh bit i : ℕ) :
    childL ws sh bit i = (List.range ws.length).map (fieldJ ws bit i) ++
      [2 * 2 ^ bit * ((sh / 2 ^ bit + 1 : ℕ) : ℤ) + 1 - (negSum ws bit i ws.length : ℤ)] := by
  unfold childL negSum fieldJ
  rw [Nat.cast_list_sum, List.map_map]
  congr 3
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  split <;> simp

/-! ## The child body: one index `j` -/

section Body
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- One index of a child: `X := ±(2·clr |w_j| b + [j = i])`, appended to `KD`; the negative ones summed in `NO`.
Streams: `3` the weight record, `4` M, `6` X, `12` `2^bit`, `13` `2^{bit+1}`, `15` NO, `16 17 18` divmod, `20` zero,
`2` the output. Registers: `11` DJ (`i − j`), `12` PASS (`[i < j]`), `4` sign, `2 3` BinW, `16 17` divmod,
`14 15` the output and field counters. -/
def cBody : WMX ns nr :=
  .seq (split (S 3) (S 4) (R 4) (R 2) (R 3))
  (.seq (.ifr (R 11) (BinW.divmod (S 4) (S 13) (S 16) (S 17) (S 18) (R 2) (R 3) (R 16) (R 17))
                     (BinW.divmod (S 4) (S 12) (S 16) (S 17) (S 18) (R 2) (R 3) (R 16) (R 17)))
  (.seq (BinW.sub (S 4) (S 17) (R 2) (R 3))
  (.seq (BinW.shl (S 4) (S 20) (R 2) (R 3))
  (.seq (.ifr (R 11) WMX.skip (.ifr (R 12) WMX.skip (.seq (BinW.inc (S 4) (S 20) (R 2) (R 3)) (WMX.inc (R 12)))))
  (.seq (.ifr (R 4) (BinW.add (S 15) (S 4) (R 2) (R 3)) WMX.skip)
  (.seq (join (S 4) (S 6) (R 4) (R 2) (R 3))
  (.seq (fieldO (S 6) (S 2) (R 15) (R 14))
  (.ifr (R 11) (WMX.dec (R 11)) WMX.skip))))))))

/-- What the body needs and keeps: the scratch words, the constants, the zero registers. -/
structure BodyPre (cap W : ℕ) (σ : WState ns nr) (pw : ℕ) : Prop where
  m : ∃ v, NumOn σ (S 4) (W + 1) v
  x : ∃ v, NumOn σ (S 6) (W + 1) v
  q : ∃ v, NumOn σ (S 16) (W + 1) v
  rm : ∃ v, NumOn σ (S 17) (W + 1) v
  dx : ∃ v, NumOn σ (S 18) (W + 1) v
  hpw : NumOn σ (S 12) (W + 1) pw
  hpw2 : NumOn σ (S 13) (W + 1) (2 * pw)
  zr : NumOn σ (S 20) (W + 1) 0
  sg : σ.val (R 4) = 0
  f : σ.val (R 2) = 0
  r : σ.val (R 3) = 0
  dk : σ.val (R 16) = 0
  dt : σ.val (R 17) = 0
  cs : σ.val (R 15) = 0
  cap : 2 * (W + 1) + 1 ≤ cap

theorem bodyPre_frame {cap W : ℕ} {σ τ : WState ns nr} {pw : ℕ} (h : BodyPre S R cap W σ pw)
    (hfr : SameExcept σ τ [S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] [R 11, R 12, R 14])
    (hm : ∃ v, NumOn τ (S 4) (W + 1) v) (hx : ∃ v, NumOn τ (S 6) (W + 1) v) (hq : ∃ v, NumOn τ (S 16) (W + 1) v)
    (hrm : ∃ v, NumOn τ (S 17) (W + 1) v) (hdx : ∃ v, NumOn τ (S 18) (W + 1) v) : BodyPre S R cap W τ pw where
  m := hm
  x := hx
  q := hq
  rm := hrm
  dx := hdx
  hpw := hfr.numOn (by simp [emb_eq_iff]) h.hpw
  hpw2 := hfr.numOn (by simp [emb_eq_iff]) h.hpw2
  zr := hfr.numOn (by simp [emb_eq_iff]) h.zr
  sg := by rw [hfr.val (by simp [emb_eq_iff])]; exact h.sg
  f := by rw [hfr.val (by simp [emb_eq_iff])]; exact h.f
  r := by rw [hfr.val (by simp [emb_eq_iff])]; exact h.r
  dk := by rw [hfr.val (by simp [emb_eq_iff])]; exact h.dk
  dt := by rw [hfr.val (by simp [emb_eq_iff])]; exact h.dt
  cs := by rw [hfr.val (by simp [emb_eq_iff])]; exact h.cs
  cap := h.cap

theorem litW_eq (ws : List ℤ) (bit i j : ℕ) :
    litW ws bit i j = 2 * ((ws.getD j 0).natAbs - (ws.getD j 0).natAbs % (if i ≤ j then 2 ^ bit else 2 ^ (bit + 1))) +
      if j = i then 1 else 0 := by
  unfold litW clr; split <;> rfl

theorem litW_le (ws : List ℤ) (bit i j : ℕ) : litW ws bit i j ≤ 2 * (ws.getD j 0).natAbs + 1 := by
  rw [litW_eq]; split <;> split <;> omega

/-- The cost bound of the body. -/
def bodyCost (W : ℕ) : ℕ := BinW.divCost (W + 1) + 500 * W + 600

/-- **The child body.** -/
theorem cBody_spec (cap W : ℕ) (σ : WState ns nr) (ws : List ℤ) (bit i j : ℕ) (out L0 : List Bool) (no : ℕ)
    (hpre : BodyPre S R cap W σ (2 ^ bit)) (hWk : NumOn σ (S 3) (W + 1) (encS (ws.getD j 0)))
    (hwj : 2 * (ws.getD j 0).natAbs + 2 ≤ 2 ^ W) (hbit : 2 ^ (bit + 2) ≤ 2 ^ (W + 1))
    (hNO : NumOn σ (S 15) (W + 1) no) (hno : no + 2 * (ws.getD j 0).natAbs + 1 < 2 ^ (W + 1))
    (hDJ : σ.val (R 11) = i - j) (hPASS : σ.val (R 12) = (decide (i < j)).toNat)
    (hKD : OutOn σ (S 2) (R 14) out L0) (hcapO : out.length + 2 * (W + 1) + 1 ≤ cap) (hcapI : i ≤ cap) :
    Runs cap (cBody S R) σ (bodyCost W) (fun τ =>
      OutOn τ (S 2) (R 14) (out ++ frameP (binary (W + 1) (encS (fieldJ ws bit i j)))) L0 ∧
      NumOn τ (S 15) (W + 1) (no + if ws.getD j 0 < 0 then litW ws bit i j else 0) ∧
      τ.val (R 11) = i - (j + 1) ∧ τ.val (R 12) = (decide (i < j + 1)).toNat ∧ BodyPre S R cap W τ (2 ^ bit) ∧
      NumOn τ (S 3) (W + 1) (encS (ws.getD j 0)) ∧
      SameExcept σ τ [S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] [R 11, R 12, R 14]) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  set x := ws.getD j 0 with hx
  set a := x.natAbs with ha
  have hpw2 : 2 ^ (bit + 1) = 2 * 2 ^ bit := by ring
  have hW1 : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
  -- (1) split
  obtain ⟨m0, hm0⟩ := hpre.m
  have h1 := split_spec (S := R 4) cap W (hne (by decide)) (hner (by decide)) σ x m0 ⟨hWk, by omega⟩ hm0 hpre.sg hpre.f
    hpre.r hpre.cap
  set σ1 := (σ.sets (S 4) (frame (binary (W + 1) a))).setv (R 4) (decide (x < 0)).toNat with hσ1
  -- (2) divmod by `P`
  set P := if i ≤ j then 2 ^ bit else 2 ^ (bit + 1) with hP
  obtain ⟨q0, hq0⟩ := hpre.q
  obtain ⟨r0, hr0⟩ := hpre.rm
  obtain ⟨d0, hd0⟩ := hpre.dx
  have hσ1num : ∀ (k : Fin 24) (v : ℕ), k ≠ 4 → NumOn σ (S k) (W + 1) v → NumOn σ1 (S k) (W + 1) v := by
    intro k v hk h
    exact BinW.numOn_setv (BinW.numOn_sets_ne h (hne hk) _) _ _
  have hM1 : NumOn σ1 (S 4) (W + 1) a := BinW.numOn_setv (BinW.numOn_sets_self σ _ _ _ hm0.2) _ _
  have hσ1v : ∀ (k : Fin 24), k ≠ 4 → σ1.val (R k) = σ.val (R k) := by
    intro k hk; simp [hσ1, Function.update_of_ne (hner hk)]
  have h2 : WXExec cap (.ifr (R 11) (BinW.divmod (S 4) (S 13) (S 16) (S 17) (S 18) (R 2) (R 3) (R 16) (R 17))
      (BinW.divmod (S 4) (S 12) (S 16) (S 17) (S 18) (R 2) (R 3) (R 16) (R 17))) σ1
      (((σ1.sets (S 16) (frame (binary (W + 1) (a / P)))).sets (S 17) (frame (binary (W + 1) (a % P)))).sets (S 18)
        (frame (binary (W + 1) 0))) (BinW.divCost (W + 1) + 1) := by
    have ha1 : a < 2 ^ (W + 1) := by omega
    have hdm := fun (B : Fin 24) (b : ℕ) (hB4 : B ≠ 4) (hB16 : B ≠ 16) (hB17 : B ≠ 17) (hB18 : B ≠ 18)
        (hb : NumOn σ1 (S B) (W + 1) b) (hb0 : 0 < b) (h2b : 2 * b ≤ 2 ^ (W + 1)) =>
      BinW.divmod_spec (A := S 4) (B := S B) (Q := S 16) (M := S 17) (X := S 18) (F := R 2) (R := R 3) (K := R 16)
        (T := R 17) cap (W + 1) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne hB16) (hne hB17)
        (hne hB18) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hner (by decide)) (hner (by decide))
        (hner (by decide)) (hner (by decide)) σ1 a b q0 r0 d0 hM1 hb (hσ1num _ _ (by decide) hq0)
        (hσ1num _ _ (by decide) hr0) (hσ1num _ _ (by decide) hd0) (by rw [hσ1v 2 (by decide)]; exact hpre.f)
        (by rw [hσ1v 3 (by decide)]; exact hpre.r) (by rw [hσ1v 16 (by decide)]; exact hpre.dk)
        (by rw [hσ1v 17 (by decide)]; exact hpre.dt) ha1 hb0 h2b (by have := hpre.cap; omega)
    by_cases hij : i ≤ j
    · have hP' : P = 2 ^ bit := by rw [hP, if_pos hij]
      have hv : σ1.val (R 11) = 0 := by rw [hσ1v 11 (by decide), hDJ]; omega
      rw [hP']
      exact WXExec.ifrF hv (hdm 12 _ (by decide) (by decide) (by decide) (by decide)
        (hσ1num _ _ (by decide) hpre.hpw) (Nat.pow_pos (by norm_num)) (by rw [pow_succ] at hbit; omega))
    · have hP' : P = 2 ^ (bit + 1) := by rw [hP, if_neg hij]
      have hv : σ1.val (R 11) ≠ 0 := by rw [hσ1v 11 (by decide), hDJ]; omega
      rw [hP', hpw2]
      exact WXExec.ifrT hv (hdm 13 _ (by decide) (by decide) (by decide) (by decide)
        (hσ1num _ _ (by decide) hpre.hpw2) (by positivity) (by rw [pow_succ] at hbit; omega))
  set σ2 := ((σ1.sets (S 16) (frame (binary (W + 1) (a / P)))).sets (S 17) (frame (binary (W + 1) (a % P)))).sets
    (S 18) (frame (binary (W + 1) 0)) with hσ2
  have hσ2num : ∀ (k : Fin 24) (v : ℕ), k ≠ 4 → k ≠ 16 → k ≠ 17 → k ≠ 18 → NumOn σ (S k) (W + 1) v →
      NumOn σ2 (S k) (W + 1) v := by
    intro k v h4 h16 h17 h18 h
    exact BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (hσ1num k v h4 h) (hne h16) _) (hne h17) _)
      (hne h18) _
  have hσ2v : ∀ (k : Fin 24), k ≠ 4 → σ2.val (R k) = σ.val (R k) := fun k hk => by simp [hσ2, hσ1v k hk]
  have hM2 : NumOn σ2 (S 4) (W + 1) a :=
    BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hM1 (hne (by decide)) _) (hne (by decide)) _)
      (hne (by decide)) _
  have hRM2 : NumOn σ2 (S 17) (W + 1) (a % P) :=
    BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by simp [hσ1, hr0.2])) (hne (by decide)) _
  -- (3) `M := a − a % P`
  have h3 := BinW.sub_spec (A := S 4) (B := S 17) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ2 a (a % P) hM2 hRM2 (by rw [hσ2v 2 (by decide)]; exact hpre.f)
    (by rw [hσ2v 3 (by decide)]; exact hpre.r) (Nat.mod_le _ _) (by omega) (by have := hpre.cap; omega)
  set c := a - a % P with hc
  set σ3 := σ2.sets (S 4) (frame (binary (W + 1) c)) with hσ3
  -- (4) `M := 2c`
  have hZR3 : NumOn σ3 (S 20) (W + 1) 0 :=
    BinW.numOn_sets_ne (hσ2num _ _ (by decide) (by decide) (by decide) (by decide) hpre.zr) (hne (by decide)) _
  have h4 := BinW.shl_spec (A := S 4) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ3 c 0 (BinW.numOn_sets_self _ _ _ _ (by simp [hσ2, hσ1, hm0.2])) hZR3
    (by simp [hσ3, hσ2v 2 (by decide), hpre.f]) (by simp [hσ3, hσ2v 3 (by decide), hpre.r])
    (by have := hpre.cap; omega)
  set σ4 := σ3.sets (S 4) (frame (binary (W + 1) (2 * c))) with hσ4
  -- (5) `+1` at `j = i`
  set e := if j = i then 1 else 0 with he
  set pass := (decide (i < j)).toNat with hpass
  have hσ4v : ∀ (k : Fin 24), k ≠ 4 → σ4.val (R k) = σ.val (R k) := fun k hk => by
    simp [hσ4, hσ3, hσ2v k hk]
  have hsame : ∀ v p, σ4.st (S 4) = frame (binary (W + 1) v) → σ4.val (R 12) = p →
      (σ4.sets (S 4) (frame (binary (W + 1) v))).setv (R 12) p = σ4 := by
    intro v p h1 h2
    rw [BinW.sets_same h1, BinW.setv_same h2]
  have h5 : WXExec cap (.ifr (R 11) WMX.skip (.ifr (R 12) WMX.skip
      (.seq (BinW.inc (S 4) (S 20) (R 2) (R 3)) (WMX.inc (R 12)))))
      σ4 ((σ4.sets (S 4) (frame (binary (W + 1) (2 * c + e)))).setv (R 12) (pass + e)) (41 * W + 60) := by
    have hcl : c ≤ a := Nat.sub_le _ _
    have hM4 : σ4.st (S 4) = frame (binary (W + 1) (2 * c)) := by simp [hσ4]
    by_cases hji : j < i
    · have hv : σ4.val (R 11) ≠ 0 := by rw [hσ4v 11 (by decide), hDJ]; omega
      have he0 : e = 0 := by rw [he]; simp; omega
      have hp0 : pass = 0 := by rw [hpass]; simp; omega
      refine (WXExec.ifrT hv (WXExec.skip cap σ4)).cast cap (hsame _ _ (by rw [he0]; exact hM4) ?_).symm (by omega)
      rw [hσ4v 12 (by decide), hPASS, he0]; exact (Nat.add_zero _).symm
    · have hv : σ4.val (R 11) = 0 := by rw [hσ4v 11 (by decide), hDJ]; omega
      by_cases hij : i < j
      · have he0 : e = 0 := by rw [he]; simp; omega
        have hv2 : σ4.val (R 12) ≠ 0 := by rw [hσ4v 12 (by decide), hPASS, hpass]; simp [hij]
        refine (WXExec.ifrF hv (WXExec.ifrT hv2 (WXExec.skip cap σ4))).cast cap
          (hsame _ _ (by rw [he0]; exact hM4) ?_).symm (by omega)
        rw [hσ4v 12 (by decide), hPASS, he0]; exact (Nat.add_zero _).symm
      · have hji' : j = i := by omega
        have he1 : e = 1 := by rw [he]; simp [hji']
        have hp0 : pass = 0 := by rw [hpass]; simp; omega
        have hv2 : σ4.val (R 12) = 0 := by rw [hσ4v 12 (by decide), hPASS, hp0]
        have hi1 := BinW.inc_spec (A := S 4) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
          (hner (by decide)) σ4 (2 * c) 0 (BinW.numOn_sets_self _ _ _ _ (by simp [hσ3, hσ2, hσ1, hm0.2]))
          (BinW.numOn_sets_ne hZR3 (hne (by decide)) _) (by rw [hσ4v 2 (by decide)]; exact hpre.f)
          (by rw [hσ4v 3 (by decide)]; exact hpre.r) (by omega) (by have := hpre.cap; omega)
        have hcapP : (σ4.sets (S 4) (frame (binary (W + 1) (2 * c + 1)))).val (R 12) < cap := by
          rw [WState.sets_val, hv2]; have := hpre.cap; omega
        have hi2 := WXExec.inc cap (R 12) (σ4.sets (S 4) (frame (binary (W + 1) (2 * c + 1)))) hcapP
        refine (WXExec.ifrF hv (WXExec.ifrF hv2 (WXExec.seq hi1 hi2))).cast cap ?_ (by omega)
        rw [he1, hp0, WState.sets_val, hv2]
  set lw := 2 * c + e with hlw
  have hlwv : lw = litW ws bit i j := by
    rw [hlw, hc, he, litW_eq]
  have hlwb : lw ≤ 2 * a + 1 := by
    have := litW_le ws bit i j; rw [← hx, ← ha] at this; rw [hlwv]; exact this
  set σ5 := (σ4.sets (S 4) (frame (binary (W + 1) lw))).setv (R 12) (pass + e) with hσ5
  -- (6) `NO += lw` if negative
  have hσ5v : ∀ (k : Fin 24), k ≠ 4 → k ≠ 12 → σ5.val (R k) = σ.val (R k) := fun k h4 h12 => by
    simp [hσ5, Function.update_of_ne (hner h12), hσ4v k h4]
  set nw := no + if x < 0 then lw else 0 with hnw
  have h6 : WXExec cap (.ifr (R 4) (BinW.add (S 15) (S 4) (R 2) (R 3)) WMX.skip) σ5
      (σ5.sets (S 15) (frame (binary (W + 1) nw))) (41 * W + 45) := by
    have hNO5 : NumOn σ5 (S 15) (W + 1) no :=
      BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne
        (hσ2num _ _ (by decide) (by decide) (by decide) (by decide) hNO) (hne (by decide)) _) (hne (by decide)) _)
        (hne (by decide)) _) _ _
    have hsg5 : σ5.val (R 4) = (decide (x < 0)).toNat := by
      simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (hner (show (4 : Fin 24) ≠ 12 by decide))]
    by_cases hneg : x < 0
    · have hv : σ5.val (R 4) ≠ 0 := by rw [hsg5]; simp [hneg]
      have hadd := BinW.add_spec (A := S 15) (B := S 4) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
        (hner (by decide)) σ5 no lw hNO5 (BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _
          (by simp [hσ4, hσ3, hσ2, hσ1, hm0.2])) _ _) (by rw [hσ5v 2 (by decide) (by decide)]; exact hpre.f)
        (by rw [hσ5v 3 (by decide) (by decide)]; exact hpre.r) (by omega) (by have := hpre.cap; omega)
      refine (WXExec.ifrT hv hadd).cast cap ?_ (by omega)
      rw [hnw, if_pos hneg]
    · have hv : σ5.val (R 4) = 0 := by rw [hsg5]; simp [hneg]
      refine (WXExec.ifrF hv (WXExec.skip cap σ5)).cast cap (BinW.sets_same ?_).symm (by omega)
      rw [hnw, if_neg hneg, hNO5.1]; simp
  set σ6 := σ5.sets (S 15) (frame (binary (W + 1) nw)) with hσ6
  -- (7) `X := ±lw`
  obtain ⟨x0, hx0⟩ := hpre.x
  have hsg6 : σ6.val (R 4) = (decide (x < 0)).toNat := by
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (hner (show (4 : Fin 24) ≠ 12 by decide))]
  have h7 := join_spec (X := S 6) (M := S 4) (S := R 4) (F := R 2) (R := R 3) cap W
    (hne (show (6 : Fin 24) ≠ 4 by decide)) (hner (by decide)) (hner (by decide))
    (hner (by decide)) σ6 lw x0 (decide (x < 0))
    (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ (by simp [hσ4, hσ3, hσ2, hσ1, hm0.2])) _ _)
      (hne (by decide)) _) (by omega)
    (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (hσ2num _ _ (by decide) (by decide) (by decide) (by decide) hx0) (hne (by decide)) _) (hne (by decide)) _)
      (hne (by decide)) _) _ _) (hne (by decide)) _) hsg6
    (by simp [hσ6, hσ5v 2 (by decide) (by decide), hpre.f]) (by simp [hσ6, hσ5v 3 (by decide) (by decide), hpre.r])
    hpre.cap
  set z := sval lw (decide (x < 0)) with hz
  have hzv : z = fieldJ ws bit i j := by
    rw [hz, fieldJ, ← hx, ← hlwv]; unfold sval; by_cases hneg : x < 0 <;> simp [hneg]
  set σ7 := (σ6.sets (S 6) (frame (binary (W + 1) (encS z)))).setv (R 4) 0 with hσ7
  -- (8) the field
  have hKD7 : OutOn σ7 (S 2) (R 14) out L0 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hKD.1]
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hKD.2.1]
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, Function.update_apply, hKD.2.2]
  have h8 := fieldO_spec cap (hne (show (6 : Fin 24) ≠ 2 by decide)) (hner (show (15 : Fin 24) ≠ 14 by decide)) σ7
    (binary (W + 1) (encS z)) [] out L0 (by simp [hσ7, BinW.frame_frameP]) (by simp [hσ7, hσ6, hσ5, hσ4, hσ3,
      hσ2, hσ1, emb_eq_iff, hx0.2])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, Function.update_apply, hpre.cs]) hKD7
    (by rw [binary_length]; exact hcapO)
  set σ8 := outSt σ7 (S 2) (R 14) (out ++ frameP (binary (W + 1) (encS z))) L0 with hσ8
  -- (9) `DJ := DJ − 1`
  have hDJ8 : σ8.val (R 11) = i - j := by
    simp [hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, Function.update_apply, hDJ]
  have h9 : WXExec cap (.ifr (R 11) (WMX.dec (R 11)) WMX.skip) σ8 (σ8.setv (R 11) (i - (j + 1))) 2 := by
    by_cases hji : j < i
    · have hv : σ8.val (R 11) ≠ 0 := by rw [hDJ8]; omega
      refine (WXExec.ifrT hv (WXExec.dec cap (R 11) σ8 (by rw [hDJ8]; omega))).cast cap ?_ (by omega)
      rw [hDJ8, Nat.sub_sub]
    · have hv : σ8.val (R 11) = 0 := by rw [hDJ8]; omega
      exact (WXExec.ifrF hv (WXExec.skip cap σ8)).cast cap (BinW.setv_same (by rw [hDJ8]; omega)).symm (by omega)
  -- the composition and the post
  simp only [binary_length] at h8
  refine ⟨_, WXExec.mono (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 (WXExec.seq h6
    (WXExec.seq h7 (WXExec.seq h8 h9)))))))) (by unfold bodyCost; omega), ?_⟩
  rw [← hzv]
  set τ := σ8.setv (R 11) (i - (j + 1)) with hτ
  -- what `τ` keeps
  have hst : ∀ k : Fin 24, k ≠ 2 → k ≠ 4 → k ≠ 6 → k ≠ 15 → k ≠ 16 → k ≠ 17 → k ≠ 18 →
      τ.st (S k) = σ.st (S k) := by
    intro k h2 h4 h6 h15 h16 h17 h18
    simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, h2, h4, h6, h15, h16, h17, h18]
  have hsh : ∀ k : Fin 24, k ≠ 2 → τ.sh (S k) = σ.sh (S k) := by
    intro k h2
    simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, h2]
  have hval : ∀ r : Fin nr, r ≠ R 4 → r ≠ R 11 → r ≠ R 12 → r ≠ R 14 → τ.val r = σ.val r := by
    intro r h4 h11 h12 h14
    simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, h4, h11, h12, h14]
  have hfin : SameExcept σ τ [S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] [R 11, R 12, R 14] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, by simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      by_cases hyS : ∃ k, S k = y
      · obtain ⟨k, rfl⟩ := hyS
        simp only [emb_eq_iff] at hy
        exact ⟨hst k hy.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1 hy.2.2.2.2.2.1 hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2,
          hsh k hy.1⟩
      · have hyS' : ∀ k, S k ≠ y := fun k h => hyS ⟨k, h⟩
        constructor <;> simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply,
          Ne.symm (hyS' _)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases hr4 : r = R 4
      · rw [hr4]; simp [hτ, hσ8, outSt, hσ7, hpre.sg, emb_eq_iff]
      · exact hval r hr4 hr.1 hr.2.1 hr.2.2
  have hpe : pass + e = (decide (i < j + 1)).toNat := by
    rw [hpass, he]
    by_cases h1 : i < j
    · have h2 : j ≠ i := by omega
      have h3 : i < j + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : j = i
      · simp [h1, h2]
      · have h3 : ¬ i < j + 1 := by omega
        simp [h1, h2, h3]
  have hhead : ∀ k : Fin 24, k ≠ 2 → σ.sh (S k) = 0 → τ.sh (S k) = 0 := fun k h2 h0 => by rw [hsh k h2, h0]
  refine ⟨?_, ?_, ?_, ?_, bodyPre_frame S R hpre hfin ?_ ?_ ?_ ?_ ?_, ?_, hfin⟩
  · exact ⟨by simp [hτ, hσ8, outSt], by simp [hτ, hσ8, outSt], by simp [hτ, hσ8, outSt, emb_eq_iff]⟩
  · rw [← hlwv]
    exact ⟨by simp [hτ, hσ8, outSt, hσ7, hσ6, emb_eq_iff, hnw], hhead 15 (by decide) hNO.2⟩
  · simp [hτ]
  · simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, emb_eq_iff, hpe]
  · exact ⟨lw, by simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, emb_eq_iff], hhead 4 (by decide) hm0.2⟩
  · exact ⟨encS z, by simp [hτ, hσ8, outSt, hσ7, emb_eq_iff], hhead 6 (by decide) hx0.2⟩
  · exact ⟨a / P, by simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, emb_eq_iff], hhead 16 (by decide) hq0.2⟩
  · exact ⟨a % P, by simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, emb_eq_iff], hhead 17 (by decide) hr0.2⟩
  · exact ⟨0, by simp [hτ, hσ8, outSt, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, emb_eq_iff], hhead 18 (by decide) hd0.2⟩
  · exact ⟨by rw [hst 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hWk.1],
      hhead 3 (by decide) hWk.2⟩

/-- **One child**: the weight scan, then the target `TL − NO` and the record's end; `DJ` starts at `IX = i`. -/
def emitChild : WMX ns nr :=
  .seq (BinW.zero (S 15) (S 20) (R 2) (R 3))
  (.seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup (R 10) (R 11) (R 22)))
  (.seq (.wm (WM.move (R 22) (R 10)))
  (.seq (recLoop (S 0) (S 3) (R 0) (R 1) (cBody S R))
  (.seq (BinW.copy (S 6) (S 14) (R 2) (R 3))
  (.seq (BinW.shl (S 6) (S 20) (R 2) (R 3))
  (.seq (BinW.copy (S 7) (S 15) (R 2) (R 3))
  (.seq (BinW.shl (S 7) (S 20) (R 2) (R 3))
  (.seq (SInt.ssub (S 6) (S 7) (S 4) (S 5) (R 4) (R 5) (R 2) (R 3))
  (.seq (fieldO (S 6) (S 2) (R 15) (R 14))
  (.seq (emitO (S 2) (R 14) false)
  (.wm (WM.clear (R 12)))))))))))))

/-- The marked fields of the first `j` indices of the child. -/
def prefixFields (W : ℕ) (ws : List ℤ) (bit i j : ℕ) : List Bool :=
  ((List.range j).map (fieldJ ws bit i)).flatMap fun z => frameP (binary (W + 1) (encS z))

theorem prefixFields_succ (W : ℕ) (ws : List ℤ) (bit i j : ℕ) :
    prefixFields W ws bit i (j + 1) = prefixFields W ws bit i j ++ frameP (binary (W + 1) (encS (fieldJ ws bit i j))) := by
  simp [prefixFields, List.range_succ]

theorem negSum_succ (ws : List ℤ) (bit i j : ℕ) :
    negSum ws bit i (j + 1) = negSum ws bit i j + if ws.getD j 0 < 0 then litW ws bit i j else 0 := by
  simp [negSum, List.range_succ]

theorem frame_recBits (W : ℕ) (zs : List ℤ) :
    frame (recBits W zs) = (zs.flatMap fun z => frameP (binary (W + 1) (encS z))) ++ [false] := by
  rw [frame_eq_frameP]
  unfold recBits
  congr 1
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [List.flatMap_cons, frameP, List.flatMap_append] at ih ⊢; exact ih

theorem bodyPre_atRec {cap W : ℕ} {σ : WState ns nr} {pw : ℕ} (h : BodyPre S R cap W σ pw) (w : List Bool) (p : ℕ) :
    BodyPre S R cap W (atRec (S 0) (S 3) (R 0) σ w p) pw := by
  have hfr : SameExcept σ (atRec (S 0) (S 3) (R 0) σ w p) [S 0, S 3] [R 0] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [atRec, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [atRec, Function.update_of_ne hr]
  exact ⟨hfr.numOn (by simp [emb_eq_iff]) h.m.choose_spec |> fun x => ⟨_, x⟩,
    hfr.numOn (by simp [emb_eq_iff]) h.x.choose_spec |> fun x => ⟨_, x⟩,
    hfr.numOn (by simp [emb_eq_iff]) h.q.choose_spec |> fun x => ⟨_, x⟩,
    hfr.numOn (by simp [emb_eq_iff]) h.rm.choose_spec |> fun x => ⟨_, x⟩,
    hfr.numOn (by simp [emb_eq_iff]) h.dx.choose_spec |> fun x => ⟨_, x⟩,
    hfr.numOn (by simp [emb_eq_iff]) h.hpw, hfr.numOn (by simp [emb_eq_iff]) h.hpw2,
    hfr.numOn (by simp [emb_eq_iff]) h.zr,
    by rw [hfr.val (by simp [emb_eq_iff])]; exact h.sg, by rw [hfr.val (by simp [emb_eq_iff])]; exact h.f,
    by rw [hfr.val (by simp [emb_eq_iff])]; exact h.r, by rw [hfr.val (by simp [emb_eq_iff])]; exact h.dk,
    by rw [hfr.val (by simp [emb_eq_iff])]; exact h.dt, by rw [hfr.val (by simp [emb_eq_iff])]; exact h.cs, h.cap⟩

/-- The loop invariant of the child's scan. -/
def ChildInv (cap W : ℕ) (σ0 : WState ns nr) (ws : List ℤ) (bit i : ℕ) (out L0 : List Bool) (j : ℕ)
    (τ : WState ns nr) : Prop :=
  OutOn τ (S 2) (R 14) (out ++ prefixFields W ws bit i j) L0 ∧ NumOn τ (S 15) (W + 1) (negSum ws bit i j) ∧
    τ.val (R 11) = i - j ∧ τ.val (R 12) = (decide (i < j)).toNat ∧ BodyPre S R cap W τ (2 ^ bit) ∧
    τ.sh (S 3) = 0 ∧ (τ.st (S 3)).length ≤ 2 * (W + 1) + 1 ∧
    SameExcept σ0 τ [S 0, S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] [R 0, R 1, R 11, R 12, R 14]

theorem negSum_le (ws : List ℤ) (bit i : ℕ) : ∀ j, negSum ws bit i j ≤
    ((List.range j).map fun j' => 2 * (ws.getD j' 0).natAbs + 1).sum
  | 0 => by simp [negSum]
  | j + 1 => by
    rw [negSum_succ, List.range_succ, List.map_append, List.sum_append]
    have := negSum_le ws bit i j
    have h2 := litW_le ws bit i j
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split <;> omega

theorem sum_range_mono (f : ℕ → ℕ) {j m : ℕ} (h : j ≤ m) :
    ((List.range j).map f).sum ≤ ((List.range m).map f).sum := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_or_ge j (m + 1) with h1 | h1
    · rw [List.range_succ, List.map_append, List.sum_append]
      have := ih (by omega); omega
    · rw [show j = m + 1 by omega]

theorem sumRange_le (ws : List ℤ) (j : ℕ) (hj : j ≤ ws.length) :
    ((List.range j).map fun j' => 2 * (ws.getD j' 0).natAbs + 1).sum ≤ (ws.map fun z => 2 * z.natAbs + 1).sum := by
  have e : (ws.map fun z => 2 * z.natAbs + 1) = (List.range ws.length).map fun j' => 2 * (ws.getD j' 0).natAbs + 1 := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2; simp [List.getElem?_eq_getElem (by simpa using h1 : k < ws.length)]
  rw [e]
  exact sum_range_mono _ hj

theorem encS_natCast (m : ℕ) : encS (m : ℤ) = 2 * m := by unfold encS; simp

theorem frameP_len (w : List Bool) : (frameP w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [frameP, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
                   omega

theorem prefixFields_length (W : ℕ) (ws : List ℤ) (bit i : ℕ) :
    ∀ k, (prefixFields W ws bit i k).length = k * (2 * (W + 1))
  | 0 => by simp [prefixFields]
  | k + 1 => by rw [prefixFields_succ, List.length_append, prefixFields_length W ws bit i k, frameP_len,
      binary_length]; ring

/-- The cost bound of one child. -/
def childCost (W n i : ℕ) : ℕ := n * (bodyCost W + 50 * (W + 1) + 30) + 3 + 20 * i + 1000 * W + 2000

/-- The scan's body meets the loop's per-record hypothesis. -/
theorem childScan_body (cap W : ℕ) (σ0 : WState ns nr) (ws : List ℤ) (junk : List Bool) (bit i : ℕ)
    (out L0 : List Bool) (hw : ∀ z ∈ ws, 2 * z.natAbs + 2 ≤ 2 ^ W) (hbit : 2 ^ (bit + 2) ≤ 2 ^ (W + 1))
    (hsum : (ws.map fun z => 2 * z.natAbs + 1).sum < 2 ^ W)
    (hcapO : out.length + ws.length * (2 * (W + 1) + 1) ≤ cap) (hcapI : i ≤ cap) :
    BodySpecJ cap (W + 1) (I := S 0) (Wk := S 3) (CI := R 0) (CW := R 1) (cBody S R)
      (ws.map fun z => binary (W + 1) (encS z)) (ChildInv S R cap W σ0 ws bit i out L0) (fun _ => bodyCost W) junk := by
  intro k hk τ hInv hst hsh hci hcw hwh hwl
  simp only [List.length_map] at hk
  obtain ⟨hKD, hNO, hDJ, hPASS, hpre, -, -, hfr⟩ := hInv
  have hwk : (ws.map fun z => binary (W + 1) (encS z))[k] = binary (W + 1) (encS (ws.getD k 0)) := by
    rw [List.getElem_map, List.getD_eq_getElem _ _ hk]
  rw [hwk]
  set τ1 := atRec (S 0) (S 3) (R 0) τ (binary (W + 1) (encS (ws.getD k 0))) ((k + 1) * (2 * (W + 1) + 1)) with hτ1
  have hmem : ws.getD k 0 ∈ ws := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hb := cBody_spec S R cap W τ1 ws bit i k (out ++ prefixFields W ws bit i k) L0 (negSum ws bit i k)
    (bodyPre_atRec S R hpre _ _) ⟨by simp [hτ1, atRec], by simp [hτ1, atRec, emb_eq_iff, hwh]⟩
    (hw _ hmem) hbit
    ⟨by simp [hτ1, atRec, emb_eq_iff, hNO.1], by simp [hτ1, atRec, emb_eq_iff, hNO.2]⟩
    (by
      have h1 := negSum_le ws bit i k
      have h2 := sumRange_le ws (k + 1) (by omega)
      rw [List.range_succ, List.map_append, List.sum_append] at h2
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h2
      have : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
    (by simp [hτ1, atRec, emb_eq_iff, hDJ]) (by simp [hτ1, atRec, emb_eq_iff, hPASS])
    (⟨by simp [hτ1, atRec, emb_eq_iff, hKD.1], by simp [hτ1, atRec, emb_eq_iff, hKD.2.1],
      by simp [hτ1, atRec, emb_eq_iff, Function.update_apply, hKD.2.2]⟩)
    (by rw [List.length_append, prefixFields_length]; nlinarith) hcapI
  obtain ⟨τ2, e2, hKD2, hNO2, hDJ2, hPASS2, hpre2, hWk2, hfr2⟩ := hb
  refine ⟨τ2, e2, ⟨?_, ?_, hDJ2, hPASS2, hpre2, hWk2.2, by rw [hWk2.1, frame_length, binary_length], ?_⟩, ?_⟩
  · rw [prefixFields_succ, ← List.append_assoc]; exact hKD2
  · rw [negSum_succ]; exact hNO2
  · have hfr1 : SameExcept τ τ1 [S 0, S 2, S 3, S 4, S 6, S 15, S 16, S 17, S 18] [R 0, R 1, R 11, R 12, R 14] := by
      refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [hτ1, atRec, Function.update_of_ne hy.1, Function.update_of_ne hy.2.2.1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hτ1, atRec, Function.update_of_ne hr.1]
    exact (hfr.trans hfr1).trans (hfr2.weaken (by simp) (by simp))
  · refine ⟨?_, ?_, ?_, ?_, hWk2.2, ?_⟩
    · rw [hfr2.st (by simp [emb_eq_iff])]
    · rw [hfr2.sh (by simp [emb_eq_iff])]
    · rw [hfr2.val (by simp [emb_eq_iff])]
    · rw [hfr2.val (by simp [emb_eq_iff])]
    · rw [hWk2.1, frame_length, binary_length]

end Body

end NearCubicGates.Close.TabMachine
