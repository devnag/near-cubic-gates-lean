import Proof.Gates.TabMachine.Explode
import Proof.Gates.WordPrograms.RegArith

/-! # The tuple step

Proof of lem:print: one cut per tuple of children, one child per variable of the monomial. Tuples are built one
variable at a time, from the last variable to the first (`tuples (L :: Ls) = L.flatMap (a ↦ (tuples Ls).map
(a :: ·))`). A tuple is stored as its fields side by side (`flatten`), every field one record. **`tupleStep_spec`**:
from the children's fields `kf` (stream `KF`) and the current tuples `tf` (stream `TP`), the output stream gains
`newT kf tf = kf.flatMap (a ↦ tf.map (a ++ ·))`, field by field. -/

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
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Value level -/

/-- One more variable: every child `a` before every current tuple. -/
def newT (kf tf : List (List ℤ)) : List (List ℤ) := kf.flatMap fun a => tf.map fun t => a ++ t

theorem tuples_flatten (L : List (List ℤ)) (Ls : List (List (List ℤ))) :
    (tuples (L :: Ls)).map List.flatten = newT L ((tuples Ls).map List.flatten) := by
  simp [tuples, newT, List.map_flatMap, List.map_map, Function.comp_def]

theorem chunk_drop_take {α : Type} (N : ℕ) : ∀ (l : List (List α)) (a : ℕ), (∀ c ∈ l, c.length = N) →
    ∀ (ha : a < l.length), (l.flatten.drop (a * N)).take N = l[a]
  | [], a, _, ha => by simp at ha
  | c :: cs, 0, h, _ => by
    simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by rw [h c (by simp)]), List.take_of_length_le (by rw [h c (by simp)])]
  | c :: cs, a + 1, h, ha => by
    simp only [List.flatten_cons, List.getElem_cons_succ]
    rw [show (a + 1) * N = c.length + a * N by rw [h c (by simp)]; ring, ← List.drop_drop, List.drop_left]
    exact chunk_drop_take N cs a (fun d hd => h d (by simp [hd])) (by simp at ha; omega)

/-- The records of a list of field lists, as the numbers `encS z`. -/
def fieldNums (l : List (List ℤ)) : List ℕ := l.flatten.map encS

theorem segRecs_chunk (L N : ℕ) (l : List (List ℤ)) (a : ℕ) (h : ∀ c ∈ l, c.length = N) (ha : a < l.length) :
    segRecs L (fieldNums l) (a * N) N = l[a].flatMap (fieldRec L) := by
  unfold segRecs fieldNums
  rw [← List.map_drop, ← List.map_take, chunk_drop_take N l a h ha, List.flatMap_map]
  rfl

theorem fieldNums_length (N : ℕ) (l : List (List ℤ)) (h : ∀ c ∈ l, c.length = N) :
    (fieldNums l).length = l.length * N := by
  unfold fieldNums
  rw [List.length_map]
  have := flatten_take_length N l l.length h le_rfl
  rwa [List.take_of_length_le le_rfl] at this

/-- The fields of a list of field lists, as records of width `L`. -/
def fieldsRecs (L : ℕ) (l : List (List ℤ)) : List Bool := l.flatten.flatMap (fieldRec L)

theorem recStream_fieldNums (L : ℕ) (l : List (List ℤ)) :
    recStream ((fieldNums l).map (binary L)) = fieldsRecs L l ++ [false] := by
  unfold fieldNums fieldsRecs recStream
  rw [List.map_map, List.flatMap_map]
  rfl

end NearCubicGates.Close.TabMachine

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Step

variable (P : Fin 4 ↪ Fin (ns + 1)) (Q : Fin 17 ↪ Fin nr)

theorem outOn_frame {σ τ : WState ns nr} {Ls : List (Fin (ns + 1))} {Rs : List (Fin nr)} {O : Fin (ns + 1)}
    {CO : Fin nr} {out L0 : List Bool} (h : OutOn σ O CO out L0) (hfr : SameExcept σ τ Ls Rs) (hO : O ∉ Ls)
    (hC : CO ∉ Rs) : OutOn τ O CO out L0 :=
  ⟨by rw [hfr.st hO]; exact h.1, by rw [hfr.sh hO]; exact h.2.1, by rw [hfr.val hC]; exact h.2.2⟩

/-- The data of the tuple step at rest. -/
structure TPre (L N M : ℕ) (kf tf : List (List ℤ)) (σ : WState ns nr) : Prop where
  kf : ∃ junk, σ.st (P 0) = recStream ((fieldNums kf).map (binary L)) ++ junk
  kfh : σ.sh (P 0) = 0
  tf : ∃ junk, σ.st (P 1) = recStream ((fieldNums tf).map (binary L)) ++ junk
  tfh : σ.sh (P 1) = 0
  wh : σ.sh (P 3) = 0
  wl : (σ.st (P 3)).length ≤ 2 * L + 1
  r0 : σ.val (Q 0) = 0
  r1 : σ.val (Q 1) = 0
  r3 : σ.val (Q 3) = 0
  r4 : σ.val (Q 4) = 0
  r7 : σ.val (Q 7) = 0
  r10 : σ.val (Q 10) = 0
  r16 : σ.val (Q 16) = 0
  ks : σ.val (Q 6) = N
  mc : σ.val (Q 9) = M

theorem tPre_frame {L N M : ℕ} {kf tf : List (List ℤ)} {σ τ : WState ns nr} (h : TPre P Q L N M kf tf σ)
    (hfr : SameExcept σ τ [P 3, P 2] [Q 2, Q 5, Q 8, Q 11, Q 12, Q 13, Q 14, Q 15]) (hwh : τ.sh (P 3) = 0)
    (hwl : (τ.st (P 3)).length ≤ 2 * L + 1) : TPre P Q L N M kf tf τ := by
  have hs : ∀ k : Fin 4, k ≠ 3 → k ≠ 2 → τ.st (P k) = σ.st (P k) ∧ τ.sh (P k) = σ.sh (P k) := fun k a b =>
    hfr.1 _ (by simp [emb_eq_iff, a, b])
  have hv : ∀ k : Fin 17, k ∈ [(0 : Fin 17), 1, 3, 4, 6, 7, 9, 10, 16] → τ.val (Q k) = σ.val (Q k) := fun k hk =>
    hfr.2.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [emb_eq_iff])
  exact ⟨by rw [(hs 0 (by decide) (by decide)).1]; exact h.kf, by rw [(hs 0 (by decide) (by decide)).2]; exact h.kfh,
    by rw [(hs 1 (by decide) (by decide)).1]; exact h.tf, by rw [(hs 1 (by decide) (by decide)).2]; exact h.tfh,
    hwh, hwl, by rw [hv 0 (by simp)]; exact h.r0, by rw [hv 1 (by simp)]; exact h.r1,
    by rw [hv 3 (by simp)]; exact h.r3, by rw [hv 4 (by simp)]; exact h.r4, by rw [hv 7 (by simp)]; exact h.r7,
    by rw [hv 10 (by simp)]; exact h.r10, by rw [hv 16 (by simp)]; exact h.r16, by rw [hv 6 (by simp)]; exact h.ks,
    by rw [hv 9 (by simp)]; exact h.mc⟩

/-- One (child, tuple) pair: the child's `N` fields, then the tuple's `M` fields. -/
def tInner : WMX ns nr :=
  .seq (addR (Q 15) (Q 2) (Q 16))
  (.seq (copyN (P 0) (P 3) (P 2) (Q 0) (Q 1) (Q 2) (Q 3) (Q 4) (Q 5) (Q 6) (Q 7))
  (.seq (.wm (WM.clear (Q 2)))
  (copyN (P 1) (P 3) (P 2) (Q 0) (Q 1) (Q 8) (Q 3) (Q 4) (Q 5) (Q 9) (Q 10))))

def tInnerCost (L N M K T : ℕ) : ℕ :=
  18 * (K * N) + 3 + 1 + (N * (copyStep L (K * N) + 8) + 7 * N + 3) + 1 + (3 * (K * N) + 1) + 1 +
    (M * (copyStep L (T * M) + 8) + 7 * M + 3)

/-- The capacity the step needs. -/
def TCap (cap L N M K T : ℕ) (o : List Bool) : Prop :=
  (K * N + 1) * (2 * L + 1) + 2 * (K * N) ≤ cap ∧ (T * M + 1) * (2 * L + 1) + 2 * (T * M) ≤ cap ∧
    o.length + K * T * ((N + M) * (2 * L + 1)) + 1 ≤ cap ∧ 2 * K + 2 * T + K * N + N ≤ cap

theorem fr_length (L : ℕ) (l : List ℤ) : (l.flatMap (fieldRec L)).length = l.length * (2 * L + 1) :=
  fieldRecs_length L l

theorem tInner_spec (cap L N M : ℕ) (hL : 1 ≤ L) (kf tf : List (List ℤ)) (σ : WState ns nr) (a t : ℕ)
    (o pre L0 : List Bool) (hkf : ∀ c ∈ kf, c.length = N) (htf : ∀ c ∈ tf, c.length = M)
    (ha : a < kf.length) (ht : t < tf.length) (hpre : TPre P Q L N M kf tf σ) (hCK : σ.val (Q 2) = 0)
    (hOA : σ.val (Q 15) = a * N) (hCT : σ.val (Q 8) = t * M) (hO : OutOn σ (P 2) (Q 5) (o ++ pre) L0)
    (hcap : TCap cap L N M kf.length tf.length o)
    (hpl : pre.length + (N + M) * (2 * L + 1) ≤ kf.length * tf.length * ((N + M) * (2 * L + 1))) :
    Runs cap (tInner P Q) σ (tInnerCost L N M kf.length tf.length) (fun ρ =>
      TPre P Q L N M kf tf ρ ∧
        OutOn ρ (P 2) (Q 5) (o ++ pre ++ (kf[a].flatMap (fieldRec L) ++ tf[t].flatMap (fieldRec L))) L0 ∧
        ρ.val (Q 2) = 0 ∧ ρ.val (Q 8) = (t + 1) * M ∧ ρ.val (Q 15) = a * N ∧
        SameExcept σ ρ [P 3, P 2] [Q 2, Q 5, Q 8]) := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → P i ≠ P j := fun h => emb_ne P h
  have hner : ∀ {i j : Fin 17}, i ≠ j → Q i ≠ Q j := fun h => emb_ne Q h
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcap
  have hKN : (fieldNums kf).length = kf.length * N := fieldNums_length N kf hkf
  have hTM : (fieldNums tf).length = tf.length * M := fieldNums_length M tf htf
  have haN : a * N + N ≤ kf.length * N := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ha
  have htM : t * M + M ≤ tf.length * M := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
  -- (1) `CK := a·N`
  have h1 := addR_spec cap (A := Q 15) (B := Q 2) (T := Q 16) (hner (by decide)) (hner (by decide)) (hner (by decide))
    σ hpre.r16 (by rw [hCK, hOA]; omega)
  rw [hCK, hOA, Nat.zero_add] at h1
  set σ1 := σ.setv (Q 2) (a * N) with hσ1
  have hfr1 : SameExcept σ σ1 [] [Q 2] := sameExcept_setv σ (by simp) _
  have hpre1 : TPre P Q L N M kf tf σ1 :=
    tPre_frame P Q hpre (hfr1.weaken (by simp) (by simp)) (by simp [hσ1, hpre.wh]) (by simp [hσ1, hpre.wl])
  -- (2) the child's fields
  obtain ⟨jk, hjk⟩ := hpre1.kf
  have h2 := copyN_spec cap (A := P 0) (Wk := P 3) (O := P 2) (CA := Q 0) (CW := Q 1) (CUR := Q 2) (K2 := Q 3)
    (CS := Q 4) (CO := Q 5) (KC := Q 6) (KC2 := Q 7) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) L hL
    (fieldNums kf) (a * N) N (by rw [hKN]; exact haN) σ1 jk (o ++ pre) L0 hjk hpre1.kfh hpre1.r0 hpre1.r1 hpre1.r3
    hpre1.r4 hpre1.wh hpre1.wl (by simp [hσ1]) hpre1.ks (by
      rw [hfr1.val (by simp [emb_eq_iff])]; exact hpre.r7.symm ▸ hpre.r7)
    (outOn_frame hO hfr1 (by simp) (by simp [emb_eq_iff]))
    (by rw [hKN]; exact hc1) (by
      rw [List.length_append]
      have : N * (2 * L + 1) ≤ (N + M) * (2 * L + 1) := Nat.mul_le_mul_right _ (by omega)
      omega)
  refine (Runs.seqE h1 (Runs.seq (c2 := 3 * (a * N + N) + 1 + 1 + (M * (copyStep L (fieldNums tf).length + 8) +
    7 * M + 3)) h2 fun σ2 hσ2 => ?_)).cost ?_
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hσ2
    rw [segRecs_chunk L N kf a hkf ha] at b1
    have hc := wclear_spec (cap := cap) (Q 2) (a * N + N) σ2 b2 (by omega)
    set σ3 := σ2.setv (Q 2) 0 with hσ3
    have hfr3 : SameExcept σ σ3 [P 3, P 2] [Q 2, Q 5] :=
      ((hfr1.comp' b7).comp' (sameExcept_setv σ2 (S := []) (Rg := [Q 2]) (by simp) 0)).weaken
        (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
    have hpre3 : TPre P Q L N M kf tf σ3 :=
      tPre_frame P Q hpre (hfr3.weaken (by simp) (by simp)) (by simp [hσ3, b3]) (by simp [hσ3, b4])
    obtain ⟨jt, hjt⟩ := hpre3.tf
    have h4 := copyN_spec cap (A := P 1) (Wk := P 3) (O := P 2) (CA := Q 0) (CW := Q 1) (CUR := Q 8) (K2 := Q 3)
      (CS := Q 4) (CO := Q 5) (KC := Q 9) (KC2 := Q 10) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) L hL
      (fieldNums tf) (t * M) M (by rw [hTM]; exact htM) σ3 jt _ L0 hjt hpre3.tfh hpre3.r0 hpre3.r1 hpre3.r3
      hpre3.r4 hpre3.wh hpre3.wl (by rw [hfr3.val (by simp [emb_eq_iff])]; exact hCT) hpre3.mc hpre3.r10
      (outOn_frame b1 (sameExcept_setv σ2 (S := []) (Rg := [Q 2]) (by simp) 0) (by simp) (by simp [emb_eq_iff]))
      (by rw [hTM]; exact hc2)
      (by
        simp only [List.length_append, fr_length, hkf _ (List.getElem_mem ha)]
        have : (N + M) * (2 * L + 1) = N * (2 * L + 1) + M * (2 * L + 1) := by ring
        have h5 : kf.length * tf.length * ((N + M) * (2 * L + 1)) ≤ o.length + kf.length * tf.length * ((N + M) *
          (2 * L + 1)) := Nat.le_add_left _ _
        omega)
    refine Runs.seqE (WXExec.wm hc) (h4.post fun σ4 hσ4 => ?_)
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hσ4
    rw [segRecs_chunk L M tf t htf ht] at d1
    have hfr4 : SameExcept σ σ4 [P 3, P 2] [Q 2, Q 5, Q 8] :=
      (hfr3.comp' d7).weaken
        (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
    refine ⟨tPre_frame P Q hpre (hfr4.weaken (by simp) (by simp)) d3 d4, by simpa [List.append_assoc] using d1, ?_,
      by rw [d2]; ring, ?_, hfr4⟩
    · rw [d7.val (by simp [emb_eq_iff])]; simp [hσ3]
    · rw [hfr4.val (by simp [emb_eq_iff])]; exact hOA
  · rw [hKN, hTM]
    unfold tInnerCost
    have e1 : a * N ≤ kf.length * N := Nat.mul_le_mul_right _ ha.le
    omega

theorem pairs_length (L N M : ℕ) (x : List ℤ) (hx : x.length = N) (tf : List (List ℤ))
    (htf : ∀ c ∈ tf, c.length = M) (i : ℕ) (hi : i ≤ tf.length) :
    ((tf.take i).flatMap fun t => x.flatMap (fieldRec L) ++ t.flatMap (fieldRec L)).length =
      i * ((N + M) * (2 * L + 1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [flatMap_take_succ' tf _ i (by omega), List.length_append, ih (by omega), List.length_append, fr_length,
      fr_length, hx, htf _ (List.getElem_mem (by omega))]
    ring

/-- One child against every current tuple, then `OA += N`. -/
def tOuter : WMX ns nr :=
  .seq (repK (Q 13) (Q 14) (tInner P Q)) (.seq (.wm (WM.clear (Q 8))) (addR (Q 6) (Q 15) (Q 16)))

def tOuterCost (L N M K T : ℕ) : ℕ :=
  T * (tInnerCost L N M K T + 8) + 7 * T + 3 + 1 + (3 * (T * M) + 1) + 1 + (18 * N + 3)

theorem tOuter_spec (cap L N M : ℕ) (hL : 1 ≤ L) (kf tf : List (List ℤ)) (σ : WState ns nr) (a : ℕ)
    (o pre L0 : List Bool) (hkf : ∀ c ∈ kf, c.length = N) (htf : ∀ c ∈ tf, c.length = M)
    (ha : a < kf.length) (hpre : TPre P Q L N M kf tf σ) (hCK : σ.val (Q 2) = 0) (hCT : σ.val (Q 8) = 0)
    (hOA : σ.val (Q 15) = a * N) (hNT : σ.val (Q 13) = tf.length) (hNT2 : σ.val (Q 14) = 0)
    (hO : OutOn σ (P 2) (Q 5) (o ++ pre) L0) (hcap : TCap cap L N M kf.length tf.length o)
    (hpl : pre.length = a * tf.length * ((N + M) * (2 * L + 1))) :
    Runs cap (tOuter P Q) σ (tOuterCost L N M kf.length tf.length) (fun ρ =>
      TPre P Q L N M kf tf ρ ∧
        OutOn ρ (P 2) (Q 5) (o ++ pre ++ tf.flatMap fun t => kf[a].flatMap (fieldRec L) ++ t.flatMap (fieldRec L))
          L0 ∧
        ρ.val (Q 2) = 0 ∧ ρ.val (Q 8) = 0 ∧ ρ.val (Q 15) = (a + 1) * N ∧ ρ.val (Q 13) = tf.length ∧
        ρ.val (Q 14) = 0 ∧ SameExcept σ ρ [P 3, P 2] [Q 2, Q 5, Q 8, Q 15]) := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → P i ≠ P j := fun h => emb_ne P h
  have hner : ∀ {i j : Fin 17}, i ≠ j → Q i ≠ Q j := fun h => emb_ne Q h
  set T := tf.length with hT
  let fr2 : List ℤ → List Bool := fun t => kf[a].flatMap (fieldRec L) ++ t.flatMap (fieldRec L)
  let Inv : ℕ → WState ns nr → Prop := fun i ρ =>
    TPre P Q L N M kf tf ρ ∧ OutOn ρ (P 2) (Q 5) (o ++ pre ++ (tf.take i).flatMap fr2) L0 ∧ ρ.val (Q 2) = 0 ∧
      ρ.val (Q 8) = i * M ∧ ρ.val (Q 15) = a * N ∧ SameExcept σ ρ [P 3, P 2] [Q 2, Q 5, Q 8, Q 13, Q 14]
  have hInv : ∀ i ρ (k : Fin 17), k = 13 ∨ k = 14 → ∀ v, Inv i ρ → Inv i (ρ.setv (Q k) v) := by
    rintro i ρ k hk v ⟨a1, a2, a3, a4, a5, a6⟩
    have hk' : Q k ∈ [Q 2, Q 5, Q 8, Q 13, Q 14] := by rcases hk with rfl | rfl <;> simp
    have hs : SameExcept ρ (ρ.setv (Q k) v) [] [Q k] := sameExcept_setv ρ (by simp) v
    have hn2 : (2 : Fin 17) ≠ k := by rcases hk with rfl | rfl <;> decide
    have hn8 : (8 : Fin 17) ≠ k := by rcases hk with rfl | rfl <;> decide
    have hn15 : (15 : Fin 17) ≠ k := by rcases hk with rfl | rfl <;> decide
    have hn5 : (5 : Fin 17) ≠ k := by rcases hk with rfl | rfl <;> decide
    refine ⟨tPre_frame P Q a1 (hs.weaken (by simp) (by rcases hk with rfl | rfl <;> simp)) (by simpa using a1.wh)
      (by simpa using a1.wl), outOn_frame a2 hs (by simp) (by simp [emb_eq_iff, hn5]), ?_, ?_, ?_,
      a6.trans (sameExcept_setv ρ hk' v)⟩
    · rw [WState.setv_val, Function.update_of_ne (hner hn2)]; exact a3
    · rw [WState.setv_val, Function.update_of_ne (hner hn8)]; exact a4
    · rw [WState.setv_val, Function.update_of_ne (hner hn15)]; exact a5
  have hrep := Runs.rep (cap := cap) (K := Q 13) (K2 := Q 14) (body := tInner P Q) (hner (by decide))
    (tInnerCost L N M kf.length T) T Inv (by have := hcap.2.2.2; omega)
    (fun i ρ v hI => hInv i ρ 13 (Or.inl rfl) v hI) (fun i ρ v hI => hInv i ρ 14 (Or.inr rfl) v hI) ?_ σ
    ⟨hpre, by simpa using hO, hCK, by simp [hCT], hOA, SameExcept.refl _ _ _⟩ hNT hNT2
  · have haN : a * N ≤ kf.length * N := Nat.mul_le_mul_right _ ha.le
    have hc4 := hcap.2.2.2
    have hc2 := hcap.2.1
    refine (Runs.seq (c2 := 3 * (T * M) + 1 + 1 + (18 * N + 3)) hrep fun ρ hρ => ?_).cost
      (by unfold tOuterCost; omega)
    obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, a7, a8⟩ := hρ
    rw [List.take_of_length_le (le_refl _)] at a2
    have hc := wclear_spec (cap := cap) (Q 8) (T * M) ρ a4 (by rw [a4]; omega)
    set ρ1 := ρ.setv (Q 8) 0 with hρ1
    have hd := addR_spec cap (A := Q 6) (B := Q 15) (T := Q 16) (hner (by decide)) (hner (by decide))
      (hner (by decide)) ρ1 (by simp [hρ1, a1.r16]) (by simp [hρ1, a1.ks, a5]; omega)
    have e1 : ρ1.val (Q 6) = N := by simp [hρ1, a1.ks]
    have e2 : ρ1.val (Q 15) = a * N := by simp [hρ1, a5]
    rw [e1, e2] at hd
    refine Runs.of (WXExec.seq (WXExec.wm hc) hd) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact tPre_frame P Q a1 (((sameExcept_setv ρ (S := []) (Rg := [Q 8]) (by simp) 0).comp'
        (sameExcept_setv ρ1 (S := []) (Rg := [Q 15]) (by simp) _)).weaken (by simp) (by simp)) (by simp [hρ1, a1.wh])
        (by simp [hρ1, a1.wl])
    · exact outOn_frame a2 ((sameExcept_setv ρ (S := []) (Rg := [Q 8]) (by simp) 0).comp'
        (sameExcept_setv ρ1 (S := []) (Rg := [Q 15]) (by simp) _)) (by simp) (by simp [emb_eq_iff])
    · simp [hρ1, a3]
    · simp [hρ1]
    · simp; ring
    · simp [hρ1, a7]
    · simp [hρ1, a8]
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ1, a6.cell]⟩
      · have := a6.1 x hx; simp [hρ1, this.1, this.2]
      · by_cases r13 : r = Q 13
        · rw [r13]; simp [hρ1, a7, hNT]
        · by_cases r14 : r = Q 14
          · rw [r14]; simp [hρ1, a8, hNT2]
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            simp [hρ1, Function.update_of_ne hr.2.2.2, Function.update_of_ne hr.2.2.1]
            exact a6.2.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, r13, r14])
  · intro i hi ρ ⟨a1, a2, a3, a4, a5, a6⟩
    have hpl' : (pre ++ (tf.take i).flatMap fr2).length + (N + M) * (2 * L + 1) ≤
        kf.length * T * ((N + M) * (2 * L + 1)) := by
      rw [List.length_append, hpl, pairs_length L N M kf[a] (hkf _ (List.getElem_mem ha)) tf htf i hi.le]
      have h1 : a * T + i + 1 ≤ kf.length * T := by
        have : (a + 1) * T ≤ kf.length * T := Nat.mul_le_mul_right _ ha
        nlinarith
      have h2 := Nat.mul_le_mul_right ((N + M) * (2 * L + 1)) h1
      have e : (a * T + i + 1) * ((N + M) * (2 * L + 1)) = a * T * ((N + M) * (2 * L + 1)) +
        i * ((N + M) * (2 * L + 1)) + (N + M) * (2 * L + 1) := by ring
      rw [e] at h2
      exact h2
    have hx := tInner_spec P Q cap L N M hL kf tf ρ a i o (pre ++ (tf.take i).flatMap fr2) L0 hkf htf ha hi a1 a3 a5
      a4 (by simpa [List.append_assoc] using a2) hcap hpl'
    refine hx.post fun τ ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨⟨b1, ?_, b3, b4, b5, ?_⟩, ?_, ?_⟩
    · have e : (tf.take (i + 1)).flatMap fr2 = (tf.take i).flatMap fr2 ++ fr2 tf[i] := flatMap_take_succ' tf fr2 i hi
      show OutOn τ (P 2) (Q 5) (o ++ pre ++ (tf.take (i + 1)).flatMap fr2) L0
      rw [e]; simpa [List.append_assoc, fr2] using b2
    · exact a6.trans (b6.weaken (by simp) (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
    · exact b6.val (by simp [emb_eq_iff])
    · exact b6.val (by simp [emb_eq_iff])

theorem newT_recs (L : ℕ) (kf tf : List (List ℤ)) :
    fieldsRecs L (newT kf tf) = kf.flatMap fun a => tf.flatMap fun t => a.flatMap (fieldRec L) ++ t.flatMap (fieldRec L) := by
  unfold fieldsRecs newT
  induction kf with
  | nil => simp
  | cons a kf ih =>
    simp only [List.flatMap_cons, List.flatten_append, List.flatMap_append, ih]
    congr 1
    clear ih
    induction tf with
    | nil => simp
    | cons t tf ih2 => simp [List.flatMap_append, ih2]

/-- **The tuple step**: every child before every current tuple, field by field. -/
def tupleStep : WMX ns nr := .seq (repK (Q 11) (Q 12) (tOuter P Q)) (.wm (WM.clear (Q 15)))

def tupleCost (L N M K T : ℕ) : ℕ := K * (tOuterCost L N M K T + 8) + 7 * K + 3 + 1 + (3 * (K * N) + 1)

theorem tupleStep_spec (cap L N M : ℕ) (hL : 1 ≤ L) (kf tf : List (List ℤ)) (σ : WState ns nr)
    (o L0 : List Bool) (hkf : ∀ c ∈ kf, c.length = N) (htf : ∀ c ∈ tf, c.length = M)
    (hpre : TPre P Q L N M kf tf σ) (hCK : σ.val (Q 2) = 0) (hCT : σ.val (Q 8) = 0) (hOA : σ.val (Q 15) = 0)
    (hNK : σ.val (Q 11) = kf.length) (hNK2 : σ.val (Q 12) = 0) (hNT : σ.val (Q 13) = tf.length)
    (hNT2 : σ.val (Q 14) = 0) (hO : OutOn σ (P 2) (Q 5) o L0) (hcap : TCap cap L N M kf.length tf.length o) :
    Runs cap (tupleStep P Q) σ (tupleCost L N M kf.length tf.length) (fun ρ =>
      TPre P Q L N M kf tf ρ ∧ OutOn ρ (P 2) (Q 5) (o ++ fieldsRecs L (newT kf tf)) L0 ∧
        SameExcept σ ρ [P 3, P 2] [Q 5]) := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → P i ≠ P j := fun h => emb_ne P h
  have hner : ∀ {i j : Fin 17}, i ≠ j → Q i ≠ Q j := fun h => emb_ne Q h
  set K := kf.length with hK
  set T := tf.length with hT
  let blk : List ℤ → List Bool := fun a => tf.flatMap fun t => a.flatMap (fieldRec L) ++ t.flatMap (fieldRec L)
  have hblk : ∀ j ≤ K, ((kf.take j).flatMap blk).length = j * T * ((N + M) * (2 * L + 1)) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [flatMap_take_succ' kf blk j (by omega), List.length_append, ih (by omega)]
      have := pairs_length L N M kf[j] (hkf _ (List.getElem_mem (by omega))) tf htf T le_rfl
      rw [List.take_of_length_le le_rfl] at this
      show _ + (tf.flatMap fun t => kf[j].flatMap (fieldRec L) ++ t.flatMap (fieldRec L)).length = _
      rw [this]; ring
  let Inv : ℕ → WState ns nr → Prop := fun j ρ =>
    TPre P Q L N M kf tf ρ ∧ OutOn ρ (P 2) (Q 5) (o ++ (kf.take j).flatMap blk) L0 ∧ ρ.val (Q 2) = 0 ∧
      ρ.val (Q 8) = 0 ∧ ρ.val (Q 15) = j * N ∧ ρ.val (Q 13) = T ∧ ρ.val (Q 14) = 0 ∧
      SameExcept σ ρ [P 3, P 2] [Q 2, Q 5, Q 8, Q 15, Q 11, Q 12]
  have hInv : ∀ j ρ (k : Fin 17), k = 11 ∨ k = 12 → ∀ v, Inv j ρ → Inv j (ρ.setv (Q k) v) := by
    rintro j ρ k hk v ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    have hs : SameExcept ρ (ρ.setv (Q k) v) [] [Q k] := sameExcept_setv ρ (by simp) v
    have hne' : ∀ m : Fin 17, m ∈ [(2 : Fin 17), 5, 8, 15, 13, 14] → m ≠ k := by
      intro m hm; rcases hk with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;>
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨tPre_frame P Q a1 (hs.weaken (by simp) (by rcases hk with rfl | rfl <;> simp)) (by simpa using a1.wh)
      (by simpa using a1.wl), outOn_frame a2 hs (by simp) (by simp [emb_eq_iff, hne' 5 (by simp)]), ?_, ?_, ?_, ?_,
      ?_, a8.trans (sameExcept_setv ρ (by rcases hk with rfl | rfl <;> simp) v)⟩
    · rw [WState.setv_val, Function.update_of_ne (hner (hne' 2 (by simp)))]; exact a3
    · rw [WState.setv_val, Function.update_of_ne (hner (hne' 8 (by simp)))]; exact a4
    · rw [WState.setv_val, Function.update_of_ne (hner (hne' 15 (by simp)))]; exact a5
    · rw [WState.setv_val, Function.update_of_ne (hner (hne' 13 (by simp)))]; exact a6
    · rw [WState.setv_val, Function.update_of_ne (hner (hne' 14 (by simp)))]; exact a7
  have hc4 := hcap.2.2.2
  have hrep := Runs.rep (cap := cap) (K := Q 11) (K2 := Q 12) (body := tOuter P Q) (hner (by decide))
    (tOuterCost L N M K T) K Inv (by omega)
    (fun j ρ v hI => hInv j ρ 11 (Or.inl rfl) v hI) (fun j ρ v hI => hInv j ρ 12 (Or.inr rfl) v hI) ?_ σ
    ⟨hpre, by simpa using hO, hCK, hCT, by simp [hOA], hNT, hNT2, SameExcept.refl _ _ _⟩ hNK hNK2
  · refine (Runs.seq (c2 := 3 * (K * N) + 1) hrep fun ρ hρ => ?_).cost (by unfold tupleCost; omega)
    obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, a9, a10⟩ := hρ
    rw [List.take_of_length_le (le_refl _)] at a2
    have hc := wclear_spec (cap := cap) (Q 15) (K * N) ρ a5 (by rw [a5]; omega)
    have hs : SameExcept ρ (ρ.setv (Q 15) 0) [] [Q 15] := sameExcept_setv ρ (by simp) 0
    refine Runs.of (WXExec.wm hc) ⟨tPre_frame P Q a1 (hs.weaken (by simp) (by simp)) (by simpa using a1.wh)
      (by simpa using a1.wl), ?_, ?_⟩
    · rw [newT_recs]; exact outOn_frame a2 hs (by simp) (by simp [emb_eq_iff])
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [a8.cell]⟩
      · have := a8.1 x hx; simp [this.1, this.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        by_cases r15 : r = Q 15
        · rw [r15]; simp [hOA]
        · rw [WState.setv_val, Function.update_of_ne r15]
          by_cases r2 : r = Q 2
          · rw [r2, a3, hCK]
          · by_cases r8 : r = Q 8
            · rw [r8, a4, hCT]
            · by_cases r11 : r = Q 11
              · rw [r11, a9, hNK]
              · by_cases r12 : r = Q 12
                · rw [r12, a10, hNK2]
                · exact a8.2.1 r (by simp [r2, r8, r15, r11, r12, hr])
  · intro j hj ρ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    have hx := tOuter_spec P Q cap L N M hL kf tf ρ j o ((kf.take j).flatMap blk) L0 hkf htf hj a1 a3 a4 a5 a6 a7
      a2 hcap (hblk j hj.le)
    refine hx.post fun τ ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ => ⟨⟨b1, ?_, b3, b4, b5, b6, b7, ?_⟩, ?_, ?_⟩
    · show OutOn τ (P 2) (Q 5) (o ++ (kf.take (j + 1)).flatMap blk) L0
      rw [flatMap_take_succ' kf blk j hj, ← List.append_assoc]; exact b2
    · exact a8.trans (b8.weaken (by simp) (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
    · exact b8.val (by simp [emb_eq_iff])
    · exact b8.val (by simp [emb_eq_iff])

end Step

end NearCubicGates.Close.TabMachine
