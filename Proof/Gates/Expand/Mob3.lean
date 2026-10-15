import Proof.Gates.Expand.Mob2

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

/-- The accumulator of a family record (the machine's constants filled in). -/
def accOf (V W : ℕ) (vals : List ℕ) (rec : ℕ) : ℕ :=
  mobAcc (2 ^ W - 1) ((2 ^ V - 1) * 2 ^ W) (2 ^ V * 2 ^ W) (2 ^ V - 1) (2 ^ V) rec vals

/-- What one family record contributes to ORC. -/
def orcOut (Wb V W : ℕ) (vals : List ℕ) (rec : ℕ) : List Bool :=
  if accOf V W vals rec = 0 then [] else frame (binary Wb (rec * 2 ^ W + accOf V W vals rec))

/-- The ORC records. -/
def orcRecs (V W : ℕ) (vals recs : List ℕ) : List ℕ :=
  recs.filterMap fun rec => if accOf V W vals rec = 0 then none else some (rec * 2 ^ W + accOf V W vals rec)

theorem orcOut_flat (Wb V W : ℕ) (vals recs : List ℕ) :
    recs.flatMap (orcOut Wb V W vals) = (orcRecs V W vals recs).flatMap fun x => frame (binary Wb x) := by
  induction recs with
  | nil => simp [orcRecs]
  | cons r rs ih =>
    simp only [List.flatMap_cons, ih, orcRecs, List.filterMap_cons, orcOut]
    split_ifs <;> simp

theorem accOf_lt (V W : ℕ) (vals : List ℕ) (rec : ℕ) : accOf V W vals rec < 2 ^ W := by
  unfold accOf mobAcc
  have key : ∀ (l : List ℕ) (a : ℕ), a < 2 ^ W →
      l.foldl (mobStep (2 ^ W - 1) ((2 ^ V - 1) * 2 ^ W) (2 ^ V * 2 ^ W)
        ((rec &&& (2 ^ V - 1)) * (2 ^ W - 1 + 1)) ((rec &&& 2 ^ V) * (2 ^ W - 1 + 1))) a < 2 ^ W := by
    intro l
    induction l with
    | nil => intro a ha; exact ha
    | cons x l ih =>
      intro a ha
      apply ih
      unfold mobStep
      have hm : 0 < 2 ^ W := Nat.two_pow_pos W
      split_ifs
      · exact lt_of_le_of_lt Nat.and_le_right (by omega)
      · exact lt_of_le_of_lt Nat.and_le_right (by omega)
      · exact ha
  exact key vals 0 (Nat.two_pow_pos W)

section Outer
variable {MB : Fin 18 ↪ Fin (ns + 1)} {MS : Fin 3 ↪ Fin (ns + 1)} {MR : Fin 9 ↪ Fin nr}

def mobOuterCost (Wb n : ℕ) : ℕ := mobSetCost Wb + 1 + (mobLoopInCost Wb n + 1 + mobTestCost Wb)

theorem mobOuter_spec (cap Wb V W : ℕ) (hMS : ∀ i j, MB i ≠ MS j) (vals : List ℕ) (hvals : ∀ x ∈ vals, x < 2 ^ Wb)
    (junk out L0 : List Bool) (σ : WState ns nr) (v : Fin 18 → ℕ) (h : MV MB Wb v σ) (hok : MOK Wb v)
    (hc : MConst Wb V W v) (rec : ℕ) (hrec : v 0 = rec)
    (hF : σ.val (MR 0) = 0) (hR : σ.val (MR 1) = 0) (hG : σ.val (MR 2) = 0)
    (hI : σ.st (MS 1) = recStream (vals.map (binary Wb)) ++ junk) (hIh : σ.sh (MS 1) = 0)
    (hCI : σ.val (MR 5) = 0) (hCW : σ.val (MR 6) = 0)
    (hO : OutOn σ (MS 2) (MR 8) out L0) (hCS : σ.val (MR 7) = 0)
    (hW1 : 1 ≤ Wb) (hrecW : (rec + 1) * 2 ^ W ≤ 2 ^ Wb) (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb)
    (hcnt : v 17 + 1 < 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapV : vals.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) (hcapO : out.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (mobOuter MB MS MR) σ (mobOuterCost Wb vals.length) (fun τ => ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧
      (∀ j : Fin 18, j = 0 ∨ 10 ≤ j.val ∧ j.val ≤ 16 → w j = v j) ∧
      w 17 = v 17 + (if accOf V W vals rec = 0 then 0 else 1) ∧
      OutOn τ (MS 2) (MR 8) (out ++ orcOut Wb V W vals rec) L0 ∧
      τ.val (MR 0) = 0 ∧ τ.val (MR 1) = 0 ∧ τ.val (MR 2) = 0 ∧ τ.val (MR 5) = 0 ∧ τ.val (MR 6) = 0 ∧
      τ.val (MR 7) = 0 ∧ τ.sh (MS 1) = 0 ∧ τ.st (MS 1) = σ.st (MS 1) ∧
      SameExcept σ τ [MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 1, MS 2]
        [MR 0, MR 5, MR 8]) := by
  have hWlt : 2 ^ W < 2 ^ Wb := by have := Nat.two_pow_pos V; nlinarith
  refine Runs.seq (mobSet_spec cap Wb V W σ v h hok hc rec hrec hF hR hG hTW hcap)
    (fun τ1 ⟨w1, h1, ok1, a12, a13, a14, o1, hF1, hR1, hG1, f1⟩ => ?_)
  have nI : ∀ j : Fin 3, MS j ∉ [MB 2, MB 3, MB 4, MB 5, MB 6] := by
    intro j hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm <;> exact hMS _ _ hm.symm
  have hW1h : τ1.sh (MB 1) = 0 := (h1 1).2
  refine Runs.seq (mobLoopIn_spec cap Wb hMS vals hvals junk τ1 w1 h1 ok1 hF1 hR1
    (by rw [f1.st (nI 1)]; exact hI) (by rw [f1.sh (nI 1)]; exact hIh)
    (by rw [f1.val (by simp)]; exact hCI) (by rw [f1.val (by simp)]; exact hCW) hW1h hW1 hcap hcapV)
    (fun τ2 ⟨w2, h2, ok2, a24, o2, hF2, hR2, hCI2, hCW2, hIh2, hIst2, f2⟩ => ?_)
  have f12 : SameExcept σ τ2 [MB 2, MB 3, MB 4, MB 5, MB 6, MB 1, MB 7, MB 8, MS 1] [MR 0, MR 5] :=
    SameExcept.trans (se_sub f1 (by simp [List.cons_subset]) (by simp))
      (se_sub f2 (by simp [List.cons_subset]) (by simp [List.cons_subset]))
  have hacc : w2 4 = accOf V W vals rec := by
    rw [a24, a14, o1 12 (by decide) (by decide) (by decide) (by decide) (by decide),
      o1 10 (by decide) (by decide) (by decide) (by decide) (by decide),
      o1 11 (by decide) (by decide) (by decide) (by decide) (by decide), a12, a13, hc.mw, hc.mh, hc.tm]
    unfold accOf mobAcc
    rw [show 2 ^ W - 1 + 1 = 2 ^ W by have := Nat.two_pow_pos W; omega]
  have w2o : ∀ j : Fin 18, j = 0 ∨ 10 ≤ j.val ∧ j.val ≤ 17 → w2 j = v j := by
    intro j hj
    have h1 : j ≠ 1 := by rintro rfl; omega
    have h2 : j ≠ 2 := by rintro rfl; omega
    have h3 : j ≠ 3 := by rintro rfl; omega
    have h4 : j ≠ 4 := by rintro rfl; omega
    have h5 : j ≠ 5 := by rintro rfl; omega
    have h6 : j ≠ 6 := by rintro rfl; omega
    have h7 : j ≠ 7 := by rintro rfl; omega
    have h8 : j ≠ 8 := by rintro rfl; omega
    rw [o2 j h1 h4 h5 h6 h7 h8, o1 j h2 h3 h4 h5 h6]
  have hO2 : OutOn τ2 (MS 2) (MR 8) out L0 :=
    ⟨by rw [f12.st (by simp [(hMS _ _).symm, msN])]; exact hO.1,
      by rw [f12.sh (by simp [(hMS _ _).symm, msN])]; exact hO.2.1, by rw [f12.val (by simp [mrN])]; exact hO.2.2⟩
  have hG2 : τ2.val (MR 2) = 0 := by rw [f2.val (by simp [mrN])]; exact hG1
  have hCS2 : τ2.val (MR 7) = 0 := by rw [f12.val (by simp [mrN])]; exact hCS
  refine (mobTest_spec cap Wb W hMS out L0 τ2 w2 h2 ok2 rec (accOf V W vals rec)
    (by rw [w2o 0 (Or.inl rfl), hrec]) hacc (by rw [w2o 13 (Or.inr ⟨by decide, by decide⟩), hc.m]) hF2 hR2 hG2 hO2 hCS2
    (accOf_lt V W vals rec) hrecW hWlt (by rw [w2o 17 (Or.inr ⟨by decide, by decide⟩)]; exact hcnt) hcap hcapO).post
    (fun τ3 ⟨w3, h3, ok3, a317, o3, hO3, hF3, hR3, hG3, hCS3, f3⟩ => ⟨w3, h3, ok3, ?_, ?_, ?_, hF3, hR3, hG3, ?_, ?_, hCS3,
      ?_, ?_, ?_⟩)
  · intro j hj
    have h6 : j ≠ 6 := by rintro rfl; omega
    have h9 : j ≠ 9 := by rintro rfl; omega
    have h17 : j ≠ 17 := by rintro rfl; omega
    rw [o3 j h6 h9 h17, w2o j (by omega)]
  · rw [a317, w2o 17 (Or.inr ⟨by decide, by decide⟩)]
  · exact hO3
  · rw [f3.val (by simp [mrN])]; exact hCI2
  · rw [f3.val (by simp [mrN])]; exact hCW2
  · rw [f3.sh (by simp [(hMS _ _).symm, msN])]; exact hIh2
  · rw [f3.st (by simp [(hMS _ _).symm, msN]), hIst2, f1.st (nI 1)]
  · exact SameExcept.trans (se_sub f12 (by simp [List.cons_subset]) (by simp [List.cons_subset]))
      (se_sub f3 (by simp [List.cons_subset]) (by simp [List.cons_subset]))

/-- The outer loop's invariant. -/
def OInv (MB : Fin 18 ↪ Fin (ns + 1)) (MS : Fin 3 ↪ Fin (ns + 1)) (MR : Fin 9 ↪ Fin nr) (Wb V W : ℕ)
    (v0 : Fin 18 → ℕ) (vals recs : List ℕ) (L0 : List Bool) (σ0 : WState ns nr) (i : ℕ) (τ : WState ns nr) : Prop :=
  ∃ w, MV MB Wb w τ ∧ MOK Wb w ∧ (∀ j : Fin 18, 10 ≤ j.val ∧ j.val ≤ 16 → w j = v0 j) ∧
    w 17 = v0 17 + (orcRecs V W vals (recs.take i)).length ∧
    OutOn τ (MS 2) (MR 8) ((recs.take i).flatMap (orcOut Wb V W vals)) L0 ∧
    τ.val (MR 0) = 0 ∧ τ.val (MR 1) = 0 ∧ τ.val (MR 2) = 0 ∧ τ.val (MR 5) = 0 ∧ τ.val (MR 6) = 0 ∧
    τ.val (MR 7) = 0 ∧ τ.sh (MS 1) = 0 ∧ τ.st (MS 1) = σ0.st (MS 1) ∧
    SameExcept σ0 τ [MB 0, MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 0, MS 1, MS 2]
      [MR 0, MR 3, MR 5, MR 8]

theorem orcRecs_take_succ (V W : ℕ) (vals recs : List ℕ) (i : ℕ) (hi : i < recs.length) :
    (orcRecs V W vals (recs.take (i + 1))).length = (orcRecs V W vals (recs.take i)).length +
      (if accOf V W vals recs[i] = 0 then 0 else 1) := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [orcRecs, List.filterMap_append, List.length_append, List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp

theorem mobBodyJ (cap Wb V W : ℕ) (hMS : ∀ i j, MB i ≠ MS j) (vals recs : List ℕ) (hvals : ∀ x ∈ vals, x < 2 ^ Wb)
    (hrecs : ∀ x ∈ recs, (x + 1) * 2 ^ W ≤ 2 ^ Wb) (junkV junkF L0 : List Bool) (σ0 : WState ns nr) (v0 : Fin 18 → ℕ)
    (hc : MConst Wb V W v0) (hV : σ0.st (MS 1) = recStream (vals.map (binary Wb)) ++ junkV)
    (hW1 : 1 ≤ Wb) (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hcnt : v0 17 + recs.length + 1 < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapV : vals.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap)
    (hcapO : recs.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    BodySpecJ cap Wb (I := MS 0) (Wk := MB 0) (CI := MR 3) (CW := MR 4) (mobOuter MB MS MR)
      (recs.map (binary Wb)) (OInv MB MS MR Wb V W v0 vals recs L0 σ0) (fun _ => mobOuterCost Wb vals.length)
      junkF := by
  intro i hi τ ⟨w, hw, okw, wc, w17, hO, hF, hR, hG, hCI2, hCW2, hCS, hIh, hIst, fr⟩ _ _ _ hcw hwh _
  have hil : i < recs.length := by simpa using hi
  set rec := recs[i] with hrecd
  have hrw : (rec + 1) * 2 ^ W ≤ 2 ^ Wb := hrecs rec (List.getElem_mem hil)
  have hrec_lt : rec < 2 ^ Wb := by
    have : rec + 1 ≤ (rec + 1) * 2 ^ W := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos W)
    omega
  set τa := atRec (MS 0) (MB 0) (MR 3) τ (recs.map (binary Wb))[i] ((i + 1) * (2 * Wb + 1)) with hτa
  have fa : SameExcept τ τa [MS 0, MB 0] [MR 3] := by
    rw [hτa]; unfold atRec
    exact SameExcept.trans (SameExcept.trans (sameExcept_sets τ (by simp) _) (sameExcept_seth _ (by simp) _))
      (sameExcept_setv _ (by simp) _)
  have hMVa : MV MB Wb (Function.update w 0 rec) τa := by
    intro j
    by_cases e : j = 0
    · subst e
      simp only [Function.update_self]
      exact ⟨by simp [hτa, atRec, Function.update_of_ne (hMS 0 0), hrecd], by
        simp [hτa, atRec, Function.update_of_ne (hMS 0 0), hwh]⟩
    · rw [Function.update_of_ne e]
      exact fa.numOn (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hMS j 0, fun h' => e (MB.injective h')⟩) (hw j)
  have okA : MOK Wb (Function.update w 0 rec) := okw.ext _ 0 (by decide) (fun j hj => by simp [hj]) (by simpa using hrec_lt)
  have hcA : MConst Wb V W (Function.update w 0 rec) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_of_ne (show (10 : Fin 18) ≠ 0 by decide), Function.update_of_ne (show (11 : Fin 18) ≠ 0 by decide),
        Function.update_of_ne (show (12 : Fin 18) ≠ 0 by decide), Function.update_of_ne (show (13 : Fin 18) ≠ 0 by decide),
        Function.update_of_ne (show (14 : Fin 18) ≠ 0 by decide), Function.update_of_ne (show (15 : Fin 18) ≠ 0 by decide),
        Function.update_of_ne (show (16 : Fin 18) ≠ 0 by decide)]
    · rw [wc 10 ⟨by decide, by decide⟩, hc.mh]
    · rw [wc 11 ⟨by decide, by decide⟩, hc.tm]
    · rw [wc 12 ⟨by decide, by decide⟩, hc.mw]
    · rw [wc 13 ⟨by decide, by decide⟩, hc.m]
    · rw [wc 14 ⟨by decide, by decide⟩, hc.one]
    · rw [wc 15 ⟨by decide, by decide⟩, hc.mv]
    · rw [wc 16 ⟨by decide, by decide⟩, hc.t]
  have nR3 : ∀ k : Fin 9, k ≠ 3 → MR k ∉ [MR 3] := by
    intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (MR.injective hm)
  have nS : ∀ k : Fin 3, k ≠ 0 → MS k ∉ [MS 0, MB 0] := by
    intro k hk hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm
    · exact hk (MS.injective hm)
    · exact hMS 0 k hm.symm
  have hlenO : ((recs.take i).flatMap (orcOut Wb V W vals)).length + 2 * Wb + 2 ≤ cap := by
    have : ((recs.take i).flatMap (orcOut Wb V W vals)).length ≤ (recs.take i).length * (2 * Wb + 1) := by
      rw [List.length_flatMap]
      have hb : ∀ x ∈ recs.take i, (orcOut Wb V W vals x).length ≤ 2 * Wb + 1 := by
        intro x _; unfold orcOut; split_ifs <;> simp [frame_length]
      calc ((recs.take i).map fun x => (orcOut Wb V W vals x).length).sum
          ≤ ((recs.take i).map fun _ => 2 * Wb + 1).sum := List.sum_le_sum (fun x hx => hb x hx)
        _ = (recs.take i).length * (2 * Wb + 1) := by simp
    have h2 : (recs.take i).length ≤ recs.length := by simp
    nlinarith
  have hcntA : (Function.update w 0 rec) 17 + 1 < 2 ^ Wb := by
    simp only [Function.update_of_ne (show (17 : Fin 18) ≠ 0 by decide)]
    rw [w17]
    have : (orcRecs V W vals (recs.take i)).length ≤ recs.length := by
      unfold orcRecs
      exact le_trans (List.length_filterMap_le _ _) (by simp)
    omega
  obtain ⟨τ', hrun, w', hw', okw', wc', w17', hO', hF', hR', hG', hCI', hCW', hCS', hIh', hIst', f'⟩ :=
    mobOuter_spec (MB := MB) (MS := MS) (MR := MR) cap Wb V W hMS vals hvals junkV _ L0 τa _ hMVa okA hcA rec (by simp)
      (by rw [fa.val (by simp [mrN])]; exact hF) (by rw [fa.val (by simp [mrN])]; exact hR)
      (by rw [fa.val (by simp [mrN])]; exact hG)
      (by rw [fa.st (nS 1 (by decide)), hIst, hV]) (by rw [fa.sh (nS 1 (by decide))]; exact hIh)
      (by rw [fa.val (nR3 5 (by decide))]; exact hCI2) (by rw [fa.val (nR3 6 (by decide))]; exact hCW2)
      ⟨by rw [fa.st (nS 2 (by decide))]; exact hO.1, by rw [fa.sh (nS 2 (by decide))]; exact hO.2.1,
        by rw [fa.val (nR3 8 (by decide))]; exact hO.2.2⟩
      (by rw [fa.val (nR3 7 (by decide))]; exact hCS) hW1 hrw hTW hcntA hcap hcapV hlenO
  have nB : MS 0 ∉ [MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 1, MS 2] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(hMS 1 0).symm, (hMS 2 0).symm, (hMS 3 0).symm, (hMS 4 0).symm, (hMS 5 0).symm, (hMS 6 0).symm,
      (hMS 7 0).symm, (hMS 8 0).symm, (hMS 9 0).symm, (hMS 17 0).symm, msN (by decide), msN (by decide)⟩
  have nW : MB 0 ∉ [MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 1, MS 2] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨MB.injective.ne (by decide), MB.injective.ne (by decide), MB.injective.ne (by decide),
      MB.injective.ne (by decide), MB.injective.ne (by decide), MB.injective.ne (by decide),
      MB.injective.ne (by decide), MB.injective.ne (by decide), MB.injective.ne (by decide),
      MB.injective.ne (by decide), hMS 0 1, hMS 0 2⟩
  have hwk1 : τ'.sh (MB 0) = 0 := by
    rw [f'.sh nW]; simp [hτa, atRec, Function.update_of_ne (hMS 0 0), hwh]
  have hwl1 : (τ'.st (MB 0)).length ≤ 2 * Wb + 1 := by
    rw [f'.st nW]; simp [hτa, atRec, frame_length]
  refine ⟨τ', hrun, ⟨w', hw', okw', fun j hj => ?_, ?_, ?_, hF', hR', hG', hCI', hCW', hCS', hIh', ?_, ?_⟩,
    ⟨f'.st nB, f'.sh nB, f'.val (by simp [mrN]), f'.val (by simp [mrN]), hwk1, hwl1⟩⟩
  · rw [wc' j (Or.inr hj)]
    have j0 : j ≠ 0 := by rintro rfl; simp at hj
    rw [Function.update_of_ne j0, wc j hj]
  · rw [w17', Function.update_of_ne (show (17 : Fin 18) ≠ 0 by decide), w17, orcRecs_take_succ V W vals recs i hil]
    ring
  · rw [WordPrograms.flatMap_take_succ' _ _ i hil]; exact hO'
  · rw [hIst', fa.st (nS 1 (by decide)), hIst]
  · exact SameExcept.trans (SameExcept.trans fr (se_sub fa (by simp [List.cons_subset]) (by simp [List.cons_subset])))
      (se_sub f' (by simp [List.cons_subset]) (by simp [List.cons_subset]))

def mobPhaseCost (Wb n m : ℕ) : ℕ :=
  (m * (mobOuterCost Wb n + (50 * Wb + 30)) + 3) + 1 + (5 * (m * (2 * Wb + 1)) + 3)

/-- **The Möbius phase.** -/
theorem mobPhase_spec (cap Wb V W : ℕ) (hMS : ∀ i j, MB i ≠ MS j) (vals recs : List ℕ)
    (hvals : ∀ x ∈ vals, x < 2 ^ Wb) (hrecs : ∀ x ∈ recs, (x + 1) * 2 ^ W ≤ 2 ^ Wb) (junkV junkF : List Bool)
    (σ : WState ns nr) (v0 : Fin 18 → ℕ) (h : MV MB Wb v0 σ) (hok : MOK Wb v0) (hc : MConst Wb V W v0)
    (hV : σ.st (MS 1) = recStream (vals.map (binary Wb)) ++ junkV) (hVh : σ.sh (MS 1) = 0)
    (hFAM : σ.st (MS 0) = recStream (recs.map (binary Wb)) ++ junkF) (hFh : σ.sh (MS 0) = 0)
    (hOh : σ.sh (MS 2) = 0) (hregs : ∀ k : Fin 9, σ.val (MR k) = 0)
    (hW1 : 1 ≤ Wb) (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hcnt : v0 17 + recs.length + 1 < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapV : vals.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap)
    (hcapO : recs.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (mobPhase MB MS MR) σ (mobPhaseCost Wb vals.length recs.length) (fun τ => ∃ w, MV MB Wb w τ ∧
      w 17 = v0 17 + (orcRecs V W vals recs).length ∧
      (∃ junk, τ.st (MS 2) = recStream ((orcRecs V W vals recs).map (binary Wb)) ++ junk) ∧ τ.sh (MS 2) = 0 ∧
      (∀ k : Fin 9, τ.val (MR k) = 0) ∧
      SameExcept σ τ [MB 0, MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 0, MS 1, MS 2]
        [MR 0, MR 3, MR 4, MR 5, MR 8] ∧ τ.sh (MS 0) = 0 ∧ τ.sh (MS 1) = 0) := by
  set L0 := σ.st (MS 2) with hL0
  have hb := mobBodyJ (MB := MB) (MS := MS) (MR := MR) cap Wb V W hMS vals recs hvals hrecs junkV junkF L0 σ v0 hc hV hW1
    hTW hcnt hcap hcapV hcapO
  have hw : ∀ w ∈ recs.map (binary Wb), w.length = Wb := by
    intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp
  have hlen : (recs.map (binary Wb)).length = recs.length := by simp
  have hInv0 : OInv MB MS MR Wb V W v0 vals recs L0 σ 0 σ :=
    ⟨v0, h, hok, fun _ _ => rfl, by simp [orcRecs], ⟨by simp [hL0, overlay], by simpa using hOh,
      by simpa using hregs 8⟩, hregs 0, hregs 1, hregs 2, hregs 5, hregs 6, hregs 7, hVh, rfl, SameExcept.refl _ _ _⟩
  obtain ⟨τ, ⟨w, hw', okw, wc, w17, hO, hF, hR, hG, hCI2, hCW2, hCS, hIh, hIst, fr⟩, hst, hcw, hloop⟩ :=
    recLoopJ_spec (cap := cap) (L := Wb) (hMS 0 0).symm (mrN (by decide)) hw hW1 (by rw [hlen]; omega) hb σ hInv0 hFAM hFh
      (hregs 3) (hregs 4) (h 0).2 (by rw [(h 0).1]; simp [frame_length])
  rw [hlen] at hloop w17 hO
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  rw [List.take_length] at w17 hO
  refine Runs.seq ⟨_, hloop, rfl⟩ (fun ρ hρ => ?_)
  subst hρ
  set ρ1 := (τ.setv (MR 3) 0).seth (MS 0) 0 with hρ1
  have f1 : SameExcept τ ρ1 [MS 0] [MR 3] := by
    rw [hρ1]; exact SameExcept.trans (sameExcept_setv _ (by simp) _) (sameExcept_seth _ (by simp) _)
  have hO1 : OutOn ρ1 (MS 2) (MR 8) (recs.flatMap (orcOut Wb V W vals)) L0 :=
    ⟨by rw [f1.st (by simp [msN])]; exact hO.1, by rw [f1.sh (by simp [msN])]; exact hO.2.1,
      by rw [f1.val (by simp [mrN])]; exact hO.2.2⟩
  have hlenO : (recs.flatMap (orcOut Wb V W vals)).length ≤ recs.length * (2 * Wb + 1) := by
    rw [List.length_flatMap]
    have hb : ∀ x ∈ recs, (orcOut Wb V W vals x).length ≤ 2 * Wb + 1 := by
      intro x _; unfold orcOut; split_ifs <;> simp [frame_length]
    calc (recs.map fun x => (orcOut Wb V W vals x).length).sum
        ≤ (recs.map fun _ => 2 * Wb + 1).sum := List.sum_le_sum (fun x hx => hb x hx)
      _ = recs.length * (2 * Wb + 1) := by simp
  refine (closeNum cap ρ1 _ L0 hO1 (by omega)).mono (by omega) (fun ρ2 ⟨hst2, hsh2, hco2, f2⟩ => ?_)
  refine ⟨w, (hw'.frame' f1 (fun i => by simp [hMS i 0])).frame' f2 (fun i => by simp [hMS i 2]), w17, ?_, hsh2, ?_, ?_,
    by rw [f2.sh (by simp [msN]), hρ1]; simp, by rw [f2.sh (by simp [msN]), f1.sh (by simp [msN])]; exact hIh⟩
  · obtain ⟨jk, hj⟩ := overlay_rec (recs.flatMap (orcOut Wb V W vals)) L0
    refine ⟨jk, ?_⟩
    rw [hst2, hj, orcOut_flat]; simp [recStream, List.flatMap_map]
  · intro k
    by_cases k8 : k = 8
    · subst k8; exact hco2
    · rw [f2.val (by simp [k8])]
      by_cases k3 : k = 3
      · subst k3; simp [hρ1]
      · rw [f1.val (by simp [k3])]
        by_cases k4 : k = 4
        · subst k4; exact hcw
        · fin_cases k
          · exact hF
          · exact hR
          · exact hG
          · exact absurd rfl k3
          · exact absurd rfl k4
          · exact hCI2
          · exact hCW2
          · exact hCS
          · exact absurd rfl k8
  · have f1' : SameExcept τ ρ1 [MB 0, MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 0, MS 1, MS 2]
        [MR 0, MR 3, MR 4, MR 5, MR 8] := se_sub f1 (by simp [List.cons_subset]) (by simp [List.cons_subset])
    have f2' : SameExcept ρ1 ρ2 [MB 0, MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 0, MS 1, MS 2]
        [MR 0, MR 3, MR 4, MR 5, MR 8] := se_sub f2 (by simp [List.cons_subset]) (by simp [List.cons_subset])
    have fr' : SameExcept σ τ [MB 0, MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 0, MS 1, MS 2]
        [MR 0, MR 3, MR 4, MR 5, MR 8] := se_sub fr (fun x hx => hx) (by simp [List.cons_subset])
    exact SameExcept.trans (SameExcept.trans fr' f1') f2'

end Outer

end NearCubicGates.Close.Expand
