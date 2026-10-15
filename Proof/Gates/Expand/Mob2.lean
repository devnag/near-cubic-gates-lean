import Proof.Gates.Expand.Mob

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Prog
variable (MB : Fin 18 ↪ Fin (ns + 1)) (MS : Fin 3 ↪ Fin (ns + 1)) (MR : Fin 9 ↪ Fin nr)

def mobLoopIn : WMX ns nr := recLoop (MS 1) (MB 1) (MR 5) (MR 6) (mobInner MB (MR 0) (MR 1))

def mobEmit : WMX ns nr :=
  .seq (BinW.mul (MB 0) (MB 13) (MB 9) (MB 6) (MR 0) (MR 1) (MR 2)) (.seq (BinW.add (MB 9) (MB 4) (MR 0) (MR 1))
    (.seq (appendRecX (MB 9) (MS 2) (MR 7) (MR 8)) (BinW.inc (MB 17) (MB 14) (MR 0) (MR 1))))

/-- `SH := (WK ∧ MASKV)·M`, `PSM := (WK ∧ T)·M`, `ACC := 0`. -/
def mobSet : WMX ns nr :=
  .seq (BinW.copy (MB 5) (MB 0) (MR 0) (MR 1)) (.seq (andX (MB 5) (MB 15) (MR 0) (MR 1))
    (.seq (BinW.mul (MB 5) (MB 13) (MB 2) (MB 6) (MR 0) (MR 1) (MR 2))
      (.seq (BinW.copy (MB 5) (MB 0) (MR 0) (MR 1)) (.seq (andX (MB 5) (MB 16) (MR 0) (MR 1))
        (.seq (BinW.mul (MB 5) (MB 13) (MB 3) (MB 6) (MR 0) (MR 1) (MR 2)) (BinW.zero (MB 4) (MB 14) (MR 0) (MR 1)))))))

/-- After the inner loop: if `ACC ≠ 0`, emit. -/
def mobTest : WMX ns nr :=
  .seq (BinW.lt (MB 4) (MB 14) (MR 0) (MR 1)) (.ifr (MR 0) (WMX.dec (MR 0)) (mobEmit MB MS MR))

def mobOuter : WMX ns nr := .seq (mobSet MB MR) (.seq (mobLoopIn MB MS MR) (mobTest MB MS MR))

/-- The Möbius phase. -/
def mobPhase : WMX ns nr := .seq (recLoop (MS 0) (MB 0) (MR 3) (MR 4) (mobOuter MB MS MR)) (closeOutX (MS 2) (MR 8))

end Prog

section Inner
variable {MB : Fin 18 ↪ Fin (ns + 1)} {MS : Fin 3 ↪ Fin (ns + 1)} {MR : Fin 9 ↪ Fin nr}

theorem mrN {i j : Fin 9} (h : i ≠ j) : MR i ≠ MR j := fun e => h (MR.injective e)
theorem msN {i j : Fin 3} (h : i ≠ j) : MS i ≠ MS j := fun e => h (MS.injective e)

/-- The inner loop's invariant: the accumulator after `i` value records. -/
def IInv (MB : Fin 18 ↪ Fin (ns + 1)) (MS : Fin 3 ↪ Fin (ns + 1)) (MR : Fin 9 ↪ Fin nr) (Wb : ℕ)
    (v0 : Fin 18 → ℕ) (vals : List ℕ) (σ0 : WState ns nr) (i : ℕ) (τ : WState ns nr) : Prop :=
  ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧
    w 4 = (vals.take i).foldl (mobStep (v0 12) (v0 10) (v0 11) (v0 2) (v0 3)) (v0 4) ∧
    (∀ j : Fin 18, j ≠ 1 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 → w j = v0 j) ∧
    τ.val (MR 0) = 0 ∧ τ.val (MR 1) = 0 ∧
    SameExcept σ0 τ [MB 1, MB 4, MB 5, MB 6, MB 7, MB 8, MS 1] [MR 0, MR 5]

def mobLoopInCost (Wb n : ℕ) : ℕ := n * (mobInnerCost Wb + (50 * Wb + 30)) + 3

theorem mobLoopIn_spec (cap Wb : ℕ) (hMS : ∀ i j, MB i ≠ MS j) (vals : List ℕ) (hvals : ∀ x ∈ vals, x < 2 ^ Wb)
    (junk : List Bool) (σ : WState ns nr) (v0 : Fin 18 → ℕ) (h : MV MB Wb v0 σ) (hok : MOK Wb v0)
    (hF : σ.val (MR 0) = 0) (hR : σ.val (MR 1) = 0) (hI : σ.st (MS 1) = recStream (vals.map (binary Wb)) ++ junk)
    (hIh : σ.sh (MS 1) = 0) (hCI : σ.val (MR 5) = 0) (hCW : σ.val (MR 6) = 0) (hWh : σ.sh (MB 1) = 0)
    (hW1 : 1 ≤ Wb) (hcap : 2 * Wb + 1 ≤ cap) (hcapV : vals.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (mobLoopIn MB MS MR) σ (mobLoopInCost Wb vals.length)
      (fun τ => ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧
        w 4 = vals.foldl (mobStep (v0 12) (v0 10) (v0 11) (v0 2) (v0 3)) (v0 4) ∧
        (∀ j : Fin 18, j ≠ 1 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 → w j = v0 j) ∧
        τ.val (MR 0) = 0 ∧ τ.val (MR 1) = 0 ∧ τ.val (MR 5) = 0 ∧ τ.val (MR 6) = 0 ∧ τ.sh (MS 1) = 0 ∧
        τ.st (MS 1) = σ.st (MS 1) ∧
        SameExcept σ τ [MB 1, MB 4, MB 5, MB 6, MB 7, MB 8, MS 1] [MR 0, MR 5]) := by
  have hw : ∀ w ∈ vals.map (binary Wb), w.length = Wb := by
    intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp
  have hb : BodySpecJ cap Wb (I := MS 1) (Wk := MB 1) (CI := MR 5) (CW := MR 6) (mobInner MB (MR 0) (MR 1))
      (vals.map (binary Wb)) (IInv MB MS MR Wb v0 vals σ) (fun _ => mobInnerCost Wb) junk := by
    intro i hi τ ⟨w, hw', okw, hw4, hwo, hF', hR', fr⟩ _ _ _ _ hwh _
    have hil : i < vals.length := by simpa using hi
    set τa := atRec (MS 1) (MB 1) (MR 5) τ (vals.map (binary Wb))[i] ((i + 1) * (2 * Wb + 1)) with hτa
    have fa : SameExcept τ τa [MS 1, MB 1] [MR 5] := by
      rw [hτa]; unfold atRec
      exact SameExcept.trans (SameExcept.trans (sameExcept_sets τ (by simp) _) (sameExcept_seth _ (by simp) _))
        (sameExcept_setv _ (by simp) _)
    have hMVa : MV MB Wb (Function.update w 1 vals[i]) τa := by
      intro j
      by_cases e : j = 1
      · subst e
        simp only [Function.update_self]
        exact ⟨by simp [hτa, atRec, Function.update_of_ne (hMS 1 1)], by
          simp [hτa, atRec, Function.update_of_ne (hMS 1 1), hwh]⟩
      · rw [Function.update_of_ne e]
        exact fa.numOn (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hMS j 1, fun h' => e (MB.injective h')⟩) (hw' j)
    have okA : MOK Wb (Function.update w 1 vals[i]) := okw.upd 1 (by decide) _ (hvals _ (List.getElem_mem hil))
    have hFa : τa.val (MR 0) = 0 := by rw [fa.val (by simp [mrN])]; exact hF'
    have hRa : τa.val (MR 1) = 0 := by rw [fa.val (by simp [mrN])]; exact hR'
    obtain ⟨τ', hrun, w', hw'', okw', hw4', hwo', hF'', hR'', f'⟩ :=
      mobInner_spec cap Wb τa _ hMVa okA (mrN (by decide)) hFa hRa hcap
    refine ⟨τ', hrun, ⟨w', hw'', okw', ?_, ?_, hF'', hR'', ?_⟩, ?_⟩
    · rw [hw4']
      simp only [Function.update_self, Function.update_of_ne (by decide : (12 : Fin 18) ≠ 1),
        Function.update_of_ne (by decide : (10 : Fin 18) ≠ 1), Function.update_of_ne (by decide : (11 : Fin 18) ≠ 1),
        Function.update_of_ne (by decide : (2 : Fin 18) ≠ 1), Function.update_of_ne (by decide : (3 : Fin 18) ≠ 1),
        Function.update_of_ne (by decide : (4 : Fin 18) ≠ 1)]
      rw [hw4, hwo 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hwo 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hwo 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hwo 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hwo 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        List.take_succ_eq_append_getElem hil, List.foldl_append]
      rfl
    · intro j j1 j4 j5 j6 j7 j8
      rw [hwo' j j4 j5 j6 j7 j8, Function.update_of_ne j1, hwo j j1 j4 j5 j6 j7 j8]
    · exact SameExcept.trans (SameExcept.trans fr (se_sub fa (by simp [List.cons_subset]) (by simp [List.cons_subset])))
        (se_sub f' (by simp [List.cons_subset]) (by simp [List.cons_subset]))
    · have nI : MS 1 ∉ [MB 4, MB 5, MB 6, MB 7, MB 8] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(hMS 4 1).symm, (hMS 5 1).symm, (hMS 6 1).symm, (hMS 7 1).symm, (hMS 8 1).symm⟩
      have nW : MB 1 ∉ [MB 4, MB 5, MB 6, MB 7, MB 8] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨MB.injective.ne (by decide), MB.injective.ne (by decide), MB.injective.ne (by decide),
          MB.injective.ne (by decide), MB.injective.ne (by decide)⟩
      refine ⟨f'.st nI, f'.sh nI, f'.val (by simp [mrN]), f'.val (by simp [mrN]), ?_, ?_⟩
      · rw [f'.sh nW]; simp [hτa, atRec, Function.update_of_ne (hMS 1 1), hwh]
      · rw [f'.st nW]; simp [hτa, atRec, frame_length]
  have hInv0 : IInv MB MS MR Wb v0 vals σ 0 σ :=
    ⟨v0, h, hok, by simp, fun _ _ _ _ _ _ _ => rfl, hF, hR, SameExcept.refl _ _ _⟩
  have hlen : (vals.map (binary Wb)).length = vals.length := by simp
  obtain ⟨τ, ⟨w, hw', okw, hw4, hwo, hF', hR', fr⟩, hst, hcw, hloop⟩ := recLoopJ_spec (cap := cap) (L := Wb)
    (hMS 1 1).symm (mrN (by decide)) hw hW1 (by rw [hlen]; omega) hb σ hInv0 hI hIh hCI hCW hWh
    (by rw [h 1 |>.1]; simp [frame_length])
  rw [hlen] at hloop hw4
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  rw [List.take_length] at hw4
  refine ⟨_, hloop, w, ?_, okw, hw4, hwo, ?_, ?_, by simp, ?_, by simp, ?_, ?_⟩
  · intro j; exact (hw' j) |> fun hn => ⟨by simpa using hn.1, by
      simp only [WState.seth_sh, WState.setv_sh]
      rw [Function.update_of_ne (hMS j 1)]; exact hn.2⟩
  · simp [Function.update_of_ne (mrN (by decide : (0 : Fin 9) ≠ 5)), hF']
  · simp [Function.update_of_ne (mrN (by decide : (1 : Fin 9) ≠ 5)), hR']
  · simp [Function.update_of_ne (mrN (by decide : (6 : Fin 9) ≠ 5)), hcw]
  · simp only [WState.seth_st, WState.setv_st]; rw [hst, hI]
  · exact SameExcept.trans fr (SameExcept.trans (sameExcept_setv _ (by simp) _) (sameExcept_seth _ (by simp) _))

end Inner

section Outer
variable {MB : Fin 18 ↪ Fin (ns + 1)} {MS : Fin 3 ↪ Fin (ns + 1)} {MR : Fin 9 ↪ Fin nr}

theorem MV.frame' {k : ℕ} {S : Fin k ↪ Fin (ns + 1)} {W : ℕ} {v : Fin k → ℕ} {σ τ : WState ns nr}
    {L : List (Fin (ns + 1))} {Rg : List (Fin nr)} (h : MV S W v σ) (f : SameExcept σ τ L Rg) (hL : ∀ i, S i ∉ L) :
    MV S W v τ := fun i => f.numOn (hL i) (h i)

theorem MV.ex {k : ℕ} {S : Fin k ↪ Fin (ns + 1)} {W : ℕ} {v : Fin k → ℕ} {σ : WState ns nr} {a : Fin k} {x : ℕ}
    (h : MV S W (Function.update v a x) σ) : ∃ w, MV S W w σ ∧ w a = x ∧ ∀ j, j ≠ a → w j = v j :=
  ⟨_, h, by simp, fun j hj => by simp [hj]⟩

theorem MV.ex2 {k : ℕ} {S : Fin k ↪ Fin (ns + 1)} {W : ℕ} {v : Fin k → ℕ} {σ : WState ns nr} {a b : Fin k} {x y : ℕ}
    (h : MV S W (Function.update (Function.update v a x) b y) σ) (hab : a ≠ b) :
    ∃ w, MV S W w σ ∧ w a = x ∧ w b = y ∧ ∀ j, j ≠ a → j ≠ b → w j = v j :=
  ⟨_, h, by simp [hab], by simp, fun j hj hj' => by simp [hj, hj']⟩

theorem MOK.ext {Wb : ℕ} {v : Fin 18 → ℕ} (h : MOK Wb v) (w : Fin 18 → ℕ) (a : Fin 18) (ha : a ≠ 4 ∧ a ≠ 12 ∧ a ≠ 14)
    (hw : ∀ j, j ≠ a → w j = v j) (hx : w a < 2 ^ Wb) : MOK Wb w := by
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · by_cases e : j = a
    · subst e; exact hx
    · rw [hw j e]; exact h.lt j
  · rw [hw 12 (Ne.symm ha.2.1)]; exact h.mw
  · rw [hw 4 (Ne.symm ha.1), hw 12 (Ne.symm ha.2.1)]; exact h.acc
  · rw [hw 14 (Ne.symm ha.2.2)]; exact h.one

theorem MOK.upd4 {Wb : ℕ} {v : Fin 18 → ℕ} (h : MOK Wb v) (x : ℕ) (hx : x ≤ v 12) : MOK Wb (Function.update v 4 x) :=
  ⟨fun j => by
    by_cases e : j = 4
    · subst e; simp only [Function.update_self]; exact lt_of_le_of_lt hx (h.lt 12)
    · rw [Function.update_of_ne e]; exact h.lt j,
    by rw [Function.update_of_ne (by decide)]; exact h.mw,
    by simp only [Function.update_self, Function.update_of_ne (by decide : (12 : Fin 18) ≠ 4)]; exact hx,
    by rw [Function.update_of_ne (by decide)]; exact h.one⟩

/-- The accumulator of the set with record `rec` against the value records `vals`. -/
def mobAcc (Mw MH TMv MASKV T rec : ℕ) (vals : List ℕ) : ℕ :=
  vals.foldl (mobStep Mw MH TMv ((rec &&& MASKV) * (Mw + 1)) ((rec &&& T) * (Mw + 1))) 0

def mobEmitCost (Wb : ℕ) : ℕ := mulCost Wb + 1 + ((41 * Wb + 3) + 1 + ((40 * Wb + 11) + 1 + (41 * Wb + 7)))

/-- The constants of the Möbius block. -/
structure MConst (Wb V W : ℕ) (v : Fin 18 → ℕ) : Prop where
  mh : v 10 = (2 ^ V - 1) * 2 ^ W
  tm : v 11 = 2 ^ V * 2 ^ W
  mw : v 12 = 2 ^ W - 1
  m : v 13 = 2 ^ W
  one : v 14 = 1
  mv : v 15 = 2 ^ V - 1
  t : v 16 = 2 ^ V

def mobSetCost (Wb : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (mulCost Wb + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 +
    (mulCost Wb + 1 + (41 * Wb + 3))))))

theorem mobSet_spec (cap Wb V W : ℕ) (σ : WState ns nr) (v : Fin 18 → ℕ) (h : MV MB Wb v σ) (hok : MOK Wb v)
    (hc : MConst Wb V W v) (rec : ℕ) (hrec : v 0 = rec)
    (hF : σ.val (MR 0) = 0) (hR : σ.val (MR 1) = 0) (hG : σ.val (MR 2) = 0)
    (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (mobSet MB MR) σ (mobSetCost Wb) (fun τ => ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧
      w 2 = (rec &&& (2 ^ V - 1)) * 2 ^ W ∧ w 3 = (rec &&& 2 ^ V) * 2 ^ W ∧ w 4 = 0 ∧
      (∀ j : Fin 18, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → w j = v j) ∧
      τ.val (MR 0) = 0 ∧ τ.val (MR 1) = 0 ∧ τ.val (MR 2) = 0 ∧ SameExcept σ τ [MB 2, MB 3, MB 4, MB 5, MB 6] []) := by
  have hc' := hcap
  have hpowV : 0 < 2 ^ V := Nat.two_pow_pos V
  have hpowW : 0 < 2 ^ W := Nat.two_pow_pos W
  have hWlt : 2 ^ W < 2 ^ Wb := by nlinarith
  have hVlt : 2 ^ V < 2 ^ Wb := by nlinarith
  have hFR := mrN (MR := MR) (by decide : (0 : Fin 9) ≠ 1)
  have hFG := mrN (MR := MR) (by decide : (0 : Fin 9) ≠ 2)
  have hRG := mrN (MR := MR) (by decide : (1 : Fin 9) ≠ 2)
  refine Runs.seq (mCopy cap Wb 5 0 (by decide) hFR h hF hR hc') (fun τ1 ⟨h1, f1⟩ => ?_)
  obtain ⟨w1, h1, a1, o1⟩ := MV.ex h1
  have ok1 := hok.ext w1 5 (by decide) o1 (by rw [a1]; exact hok.lt 0)
  refine Runs.seq (mAnd cap Wb 5 15 (by decide) hFR h1 (by rw [f1.val (by simp)]; exact hF)
    (by rw [f1.val (by simp)]; exact hR) hc') (fun τ2 ⟨h2, f2⟩ => ?_)
  obtain ⟨w2, h2, a2, o2⟩ := MV.ex h2
  have hs : (rec &&& (2 ^ V - 1)) < 2 ^ V := by
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ hpowV
  have a2' : w2 5 = rec &&& (2 ^ V - 1) := by rw [a2, a1, o1 15 (by decide), hrec, hc.mv]
  have ok2 := ok1.ext w2 5 (by decide) o2 (by rw [a2']; exact lt_trans hs hVlt)
  have f02 : SameExcept σ τ2 [MB 5] [] := SameExcept.trans f1 f2
  have hsM : (rec &&& (2 ^ V - 1)) * 2 ^ W < 2 ^ Wb :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hs hpowW) (by nlinarith)
  have m2 : w2 13 = 2 ^ W := by rw [o2 13 (by decide), o1 13 (by decide), hc.m]
  refine Runs.seq (mMul cap Wb 5 13 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hFR hFG hRG
    h2 (by rw [f02.val (by simp)]; exact hF) (by rw [f02.val (by simp)]; exact hR) (by rw [f02.val (by simp)]; exact hG)
    (by rw [a2', m2]; exact hsM) (by rw [m2]; exact hWlt) hc') (fun τ3 ⟨h3, f3⟩ => ?_)
  obtain ⟨w3, h3, a3, b3, o3⟩ := MV.ex2 h3 (by decide)
  have ok3 : MOK Wb w3 := by
    refine ⟨fun j => ?_, ?_, ?_, ?_⟩
    · by_cases e2 : j = 2
      · subst e2; rw [a3, a2', m2]; exact hsM
      · by_cases e6 : j = 6
        · subst e6; rw [b3]; omega
        · rw [o3 j e2 e6]; exact ok2.lt j
    · rw [o3 12 (by decide) (by decide)]; exact ok2.mw
    · rw [o3 12 (by decide) (by decide), o3 4 (by decide) (by decide)]; exact ok2.acc
    · rw [o3 14 (by decide) (by decide)]; exact ok2.one
  have f03 : SameExcept σ τ3 [MB 5, MB 2, MB 6] [] := SameExcept.trans (se_sub f02 (by simp) (by simp))
    (se_sub f3 (by simp [List.cons_subset]) (by simp))
  have hF3 : τ3.val (MR 0) = 0 := by rw [f03.val (by simp)]; exact hF
  have hR3 : τ3.val (MR 1) = 0 := by rw [f03.val (by simp)]; exact hR
  have hG3 : τ3.val (MR 2) = 0 := by rw [f03.val (by simp)]; exact hG
  have w3o : ∀ j : Fin 18, j ≠ 2 → j ≠ 5 → j ≠ 6 → w3 j = v j := by
    intro j j2 j5 j6; rw [o3 j j2 j6, o2 j j5, o1 j j5]
  refine Runs.seq (mCopy cap Wb 5 0 (by decide) hFR h3 hF3 hR3 hc') (fun τ4 ⟨h4, f4⟩ => ?_)
  obtain ⟨w4, h4, a4, o4⟩ := MV.ex h4
  have ok4 := ok3.ext w4 5 (by decide) o4 (by rw [a4]; exact ok3.lt 0)
  refine Runs.seq (mAnd cap Wb 5 16 (by decide) hFR h4 (by rw [f4.val (by simp)]; exact hF3)
    (by rw [f4.val (by simp)]; exact hR3) hc') (fun τ5 ⟨h5, f5⟩ => ?_)
  obtain ⟨w5, h5, a5, o5⟩ := MV.ex h5
  have a5' : w5 5 = rec &&& 2 ^ V := by
    rw [a5, a4, o4 16 (by decide), w3o 0 (by decide) (by decide) (by decide), w3o 16 (by decide) (by decide) (by decide),
      hrec, hc.t]
  have hpT : (rec &&& 2 ^ V) ≤ 2 ^ V := Nat.and_le_right
  have hpM : (rec &&& 2 ^ V) * 2 ^ W < 2 ^ Wb := lt_of_le_of_lt (Nat.mul_le_mul_right _ hpT) (by nlinarith)
  have ok5 := ok4.ext w5 5 (by decide) o5 (by rw [a5']; exact lt_of_le_of_lt hpT hVlt)
  have f35 : SameExcept τ3 τ5 [MB 5] [] := SameExcept.trans f4 f5
  have m5 : w5 13 = 2 ^ W := by rw [o5 13 (by decide), o4 13 (by decide), w3o 13 (by decide) (by decide) (by decide), hc.m]
  refine Runs.seq (mMul cap Wb 5 13 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hFR hFG hRG
    h5 (by rw [f35.val (by simp)]; exact hF3) (by rw [f35.val (by simp)]; exact hR3) (by rw [f35.val (by simp)]; exact hG3)
    (by rw [a5', m5]; exact hpM) (by rw [m5]; exact hWlt) hc') (fun τ6 ⟨h6, f6⟩ => ?_)
  obtain ⟨w6, h6, a6, b6, o6⟩ := MV.ex2 h6 (by decide)
  have ok6 : MOK Wb w6 := by
    refine ⟨fun j => ?_, ?_, ?_, ?_⟩
    · by_cases e3 : j = 3
      · subst e3; rw [a6, a5', m5]; exact hpM
      · by_cases e6 : j = 6
        · subst e6; rw [b6]; omega
        · rw [o6 j e3 e6]; exact ok5.lt j
    · rw [o6 12 (by decide) (by decide)]; exact ok5.mw
    · rw [o6 12 (by decide) (by decide), o6 4 (by decide) (by decide)]; exact ok5.acc
    · rw [o6 14 (by decide) (by decide)]; exact ok5.one
  have f36 : SameExcept τ3 τ6 [MB 5, MB 3, MB 6] [] := SameExcept.trans (se_sub f35 (by simp) (by simp))
    (se_sub f6 (by simp [List.cons_subset]) (by simp))
  have hF6 : τ6.val (MR 0) = 0 := by rw [f36.val (by simp)]; exact hF3
  have hR6 : τ6.val (MR 1) = 0 := by rw [f36.val (by simp)]; exact hR3
  have hG6 : τ6.val (MR 2) = 0 := by rw [f36.val (by simp)]; exact hG3
  refine (mZero cap Wb 4 14 (by decide) hFR h6 hF6 hR6 hc').post (fun τ7 ⟨h7, f7⟩ => ?_)
  obtain ⟨w7, h7, a7, o7⟩ := MV.ex h7
  refine ⟨w7, h7, ?_, ?_, ?_, a7, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun j => ?_, ?_, ?_, ?_⟩
    · by_cases e4 : j = 4
      · subst e4; rw [a7]; exact Nat.two_pow_pos Wb
      · rw [o7 j e4]; exact ok6.lt j
    · rw [o7 12 (by decide)]; exact ok6.mw
    · rw [a7]; exact Nat.zero_le _
    · rw [o7 14 (by decide)]; exact ok6.one
  · rw [o7 2 (by decide), o6 2 (by decide) (by decide), o5 2 (by decide), o4 2 (by decide), a3, a2', m2]
  · rw [o7 3 (by decide), a6, a5', m5]
  · intro j j2 j3 j4 j5 j6
    rw [o7 j j4, o6 j j3 j6, o5 j j5, o4 j j5, w3o j j2 j5 j6]
  · rw [f7.val (by simp)]; exact hF6
  · rw [f7.val (by simp)]; exact hR6
  · rw [f7.val (by simp)]; exact hG6
  · exact SameExcept.trans (SameExcept.trans (se_sub f03 (by simp [List.cons_subset]) (by simp))
      (se_sub f36 (by simp [List.cons_subset]) (by simp))) (se_sub f7 (by simp) (by simp))

def mobTestCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + (mobEmitCost Wb + 1)

/-- After the inner loop: emit `rec·M + ACC` (and count it) if `ACC ≠ 0`. -/
theorem mobTest_spec (cap Wb W : ℕ) (hMS : ∀ i j, MB i ≠ MS j) (out L0 : List Bool) (σ : WState ns nr)
    (w : Fin 18 → ℕ) (h : MV MB Wb w σ) (hok : MOK Wb w) (rec acc : ℕ) (hw0 : w 0 = rec) (hw4 : w 4 = acc)
    (hw13 : w 13 = 2 ^ W) (hF : σ.val (MR 0) = 0) (hR : σ.val (MR 1) = 0) (hG : σ.val (MR 2) = 0)
    (hO : OutOn σ (MS 2) (MR 8) out L0) (hCS : σ.val (MR 7) = 0) (hacc : acc < 2 ^ W)
    (hrecW : (rec + 1) * 2 ^ W ≤ 2 ^ Wb) (hWlt : 2 ^ W < 2 ^ Wb) (hcnt : w 17 + 1 < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapO : out.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (mobTest MB MS MR) σ (mobTestCost Wb) (fun τ => ∃ w', MV MB Wb w' τ ∧ MOK Wb w' ∧
      w' 17 = w 17 + (if acc = 0 then 0 else 1) ∧ (∀ j : Fin 18, j ≠ 6 → j ≠ 9 → j ≠ 17 → w' j = w j) ∧
      OutOn τ (MS 2) (MR 8) (out ++ if acc = 0 then [] else frame (binary Wb (rec * 2 ^ W + acc))) L0 ∧
      τ.val (MR 0) = 0 ∧ τ.val (MR 1) = 0 ∧ τ.val (MR 2) = 0 ∧ τ.val (MR 7) = 0 ∧
      SameExcept σ τ [MB 6, MB 9, MB 17, MS 2] [MR 0, MR 8]) := by
  have hc' := hcap
  have hFR := mrN (MR := MR) (by decide : (0 : Fin 9) ≠ 1)
  have hFG := mrN (MR := MR) (by decide : (0 : Fin 9) ≠ 2)
  have hRG := mrN (MR := MR) (by decide : (1 : Fin 9) ≠ 2)
  refine Runs.seq (mLt cap Wb 4 14 (by decide) hFR h hF hR (hok.lt 4) (hok.lt 14) hc') (fun τ1 ⟨h1, hF1, f1⟩ => ?_)
  have hR1 : τ1.val (MR 1) = 0 := by rw [f1.val (by simp [hFR.symm])]; exact hR
  have hG1 : τ1.val (MR 2) = 0 := by rw [f1.val (by simp [hFG.symm])]; exact hG
  have hCS1 : τ1.val (MR 7) = 0 := by rw [f1.val (by simp [mrN])]; exact hCS
  have hO1 : OutOn τ1 (MS 2) (MR 8) out L0 :=
    ⟨by rw [f1.st (by simp)]; exact hO.1, by rw [f1.sh (by simp)]; exact hO.2.1,
      by rw [f1.val (by simp [mrN])]; exact hO.2.2⟩
  have e14 : w 14 = 1 := hok.one
  refine Runs.ifr (fun hne => ?_) (fun h0 => ?_)
  · have hz : acc = 0 := by rw [hF1, hw4, e14] at hne; by_contra hc2; simp at hne; omega
    refine (fDec1 (r := MR 0) cap τ1 (by rw [hF1, hw4, e14, hz]; rfl) (by omega)).mono (by unfold mobEmitCost; omega)
      (fun τ2 ⟨hF2, f2⟩ => ⟨w, h1.frame f2, hok, by simp [hz], fun j _ _ _ => rfl, ?_, hF2, ?_, ?_, ?_, ?_⟩)
    · rw [if_pos hz, List.append_nil]
      exact ⟨by rw [f2.st (by simp)]; exact hO1.1, by rw [f2.sh (by simp)]; exact hO1.2.1,
        by rw [f2.val (by simp [mrN])]; exact hO1.2.2⟩
    · rw [f2.val (by simp [mrN])]; exact hR1
    · rw [f2.val (by simp [mrN])]; exact hG1
    · rw [f2.val (by simp [mrN])]; exact hCS1
    · exact SameExcept.trans (se_sub f1 (by simp) (by simp)) (se_sub f2 (by simp) (by simp))
  · have hnz : acc ≠ 0 := by intro hz; rw [hF1, hw4, e14, hz] at h0; simp at h0
    have h10 : τ1.val (MR 0) = 0 := h0
    have hE : rec * 2 ^ W + acc < 2 ^ Wb := by nlinarith
    refine Runs.seq (mMul cap Wb 0 13 9 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hFR hFG hRG h1 h10 hR1 hG1 (by rw [hw0, hw13]; nlinarith) (by rw [hw13]; exact hWlt) hc') (fun τ2 ⟨h2, f2⟩ => ?_)
    obtain ⟨w2, h2, a2, b2, o2⟩ := MV.ex2 h2 (by decide)
    refine Runs.seq (mAdd cap Wb 9 4 (by decide) hFR h2 (by rw [f2.val (by simp)]; exact h10)
      (by rw [f2.val (by simp)]; exact hR1) (by rw [a2, o2 4 (by decide) (by decide), hw0, hw13, hw4]; exact hE) hc')
      (fun τ3 ⟨h3, f3⟩ => ?_)
    obtain ⟨w3, h3, a3, o3⟩ := MV.ex h3
    have e3 : w3 9 = rec * 2 ^ W + acc := by rw [a3, a2, o2 4 (by decide) (by decide), hw0, hw13, hw4]
    have f13 : SameExcept τ1 τ3 [MB 9, MB 6] [] := SameExcept.trans f2 (se_sub f3 (by simp) (by simp))
    have hO3 : OutOn τ3 (MS 2) (MR 8) out L0 :=
      ⟨by rw [f13.st (by simp [(hMS _ _).symm])]; exact hO1.1, by rw [f13.sh (by simp [(hMS _ _).symm])]; exact hO1.2.1,
        by rw [f13.val (by simp)]; exact hO1.2.2⟩
    refine Runs.seq (appendNum cap Wb (hMS 9 2) (mrN (by decide)) τ3 _ out L0 (h3 9)
      (by rw [f13.val (by simp)]; exact hCS1) hO3 hcapO) (fun τ4 ⟨hO4, f4⟩ => ?_)
    have h4 := h3.frame' f4 (fun i => by simp [hMS i 2])
    have hF4 : τ4.val (MR 0) = 0 := by rw [f4.val (by simp [mrN]), f13.val (by simp)]; exact h10
    have hR4 : τ4.val (MR 1) = 0 := by rw [f4.val (by simp [mrN]), f13.val (by simp)]; exact hR1
    have w3o : ∀ j : Fin 18, j ≠ 9 → j ≠ 6 → w3 j = w j := by intro j j9 j6; rw [o3 j j9, o2 j j9 j6]
    refine (mInc cap Wb 17 14 (by decide) hFR h4 hF4 hR4 (by rw [w3o 17 (by decide) (by decide)]; exact hcnt) hc').post
      (fun τ5 ⟨h5, f5⟩ => ⟨_, h5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · refine ⟨fun j => ?_, ?_, ?_, ?_⟩
      · by_cases e17 : j = 17
        · subst e17; simp only [Function.update_self]; rw [w3o 17 (by decide) (by decide)]; exact hcnt
        · rw [Function.update_of_ne e17]
          by_cases e9 : j = 9
          · subst e9; rw [e3]; exact hE
          · by_cases e6 : j = 6
            · subst e6; rw [o3 6 (by decide), b2]; omega
            · rw [w3o j e9 e6]; exact hok.lt j
      · rw [Function.update_of_ne (by decide), w3o 12 (by decide) (by decide)]; exact hok.mw
      · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), w3o 4 (by decide) (by decide),
          w3o 12 (by decide) (by decide)]; exact hok.acc
      · rw [Function.update_of_ne (by decide), w3o 14 (by decide) (by decide)]; exact hok.one
    · simp only [Function.update_self]; rw [w3o 17 (by decide) (by decide), if_neg hnz]
    · intro j j6 j9 j17; rw [Function.update_of_ne j17, w3o j j9 j6]
    · rw [if_neg hnz, ← e3]
      exact ⟨by rw [f5.st (by simp [(hMS _ _).symm])]; exact hO4.1, by rw [f5.sh (by simp [(hMS _ _).symm])]; exact hO4.2.1,
        by rw [f5.val (by simp)]; exact hO4.2.2⟩
    · rw [f5.val (by simp)]; exact hF4
    · rw [f5.val (by simp)]; exact hR4
    · rw [f5.val (by simp), f4.val (by simp [mrN]), f13.val (by simp)]; exact hG1
    · rw [f5.val (by simp), f4.val (by simp [mrN]), f13.val (by simp)]; exact hCS1
    · exact SameExcept.trans (SameExcept.trans (SameExcept.trans (se_sub f1 (by simp) (by simp))
        (se_sub f13 (by simp [List.cons_subset]) (by simp))) (se_sub f4 (by simp) (by simp)))
        (se_sub f5 (by simp) (by simp))

end Outer

end NearCubicGates.Close.Expand
