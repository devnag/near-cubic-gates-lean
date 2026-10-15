import Proof.Gates.WorkerArith.SuppEqB
import Proof.Gates.WorkerArith.CtrCall

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (listWord)

variable {ns nr : ℕ}

theorem listWord_nat_inj (xs ys : List ℕ) : listWord natWord xs = listWord natWord ys ↔ xs = ys := by
  constructor
  · intro h
    exact (Counter.listWord_prefixCode Counter.natWord_prefixCode xs ys [] [] (by simpa using h)).1
  · rintro rfl; rfl

theorem sysList_len (q : ℕ) (rows : ℕ → List ℕ) (R Lb u : ℕ) (hu : u < q + R)
    (hLR : (Codec.rowPrefix rows R).length ≤ Lb) :
    (marks (listWord natWord (sysList q rows u))).length ≤ Lb + 4 * u + 12 := by
  unfold sysList
  split_ifs with h
  · rw [Codec.marks_length]
    simp only [listWord, List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_singleton, natWord_len_c]
    have := nbl_le u; have : natBitLength 1 = 1 := rfl; omega
  · have := row_le_record rows R (u - q) (by omega); omega

theorem suppCost_le (Lb q u v rb ka kb : ℕ) (hka : 2 * ka ≤ Lb + 4 * u + 12) (hkb : 2 * kb ≤ Lb + 4 * v + 12) :
    wlCost (Lb + q + u) rb + 1 + (wlCost (Lb + q + v) rb + 1 + (18 * (2 * ka) + 3 + 1 + (5 * (2 * ka) + 1 + 1 +
      (18 * (2 * kb) + 3 + 1 + (5 * (2 * kb) + 1 + 1 + (40 * ka + 15 + 1 + (20 * (2 * ka) + 3 + 1 +
      (20 * (2 * kb) + 3 + 1 + (5 + 1 + (18 * Lb + 3 + 1 + (5 * Lb + 1))))))))))) ≤ suppCost (Lb + q + u + v) rb := by
  have m1 : (Lb + q + u + 1) ^ 2 ≤ (Lb + q + u + v + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have m2 : (Lb + q + v + 1) ^ 2 ≤ (Lb + q + u + v + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have w1 : wlCost (Lb + q + u) rb ≤ 6000 * ((Lb + q + u + v + 1) ^ 2 * (rb + 1)) := by
    unfold wlCost
    rw [show 6000 * (Lb + q + u + 1) ^ 2 * (rb + 1) = 6000 * ((Lb + q + u + 1) ^ 2 * (rb + 1)) by ring]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ m1)
  have w2 : wlCost (Lb + q + v) rb ≤ 6000 * ((Lb + q + u + v + 1) ^ 2 * (rb + 1)) := by
    unfold wlCost
    rw [show 6000 * (Lb + q + v + 1) ^ 2 * (rb + 1) = 6000 * ((Lb + q + v + 1) ^ 2 * (rb + 1)) by ring]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ m2)
  have h1 : (Lb + q + u + v + 1) ^ 2 * 1 ≤ (Lb + q + u + v + 1) ^ 2 * (rb + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : Lb + q + u + v + 1 ≤ (Lb + q + u + v + 1) ^ 2 := by nlinarith
  have e : suppCost (Lb + q + u + v) rb = 20000 * ((Lb + q + u + v + 1) ^ 2 * (rb + 1)) := by unfold suppCost; ring
  rw [e]
  generalize (Lb + q + u + v + 1) ^ 2 * (rb + 1) = W2 at *
  generalize (Lb + q + u + v + 1) ^ 2 = W1 at *
  generalize wlCost (Lb + q + u) rb = C1 at *
  generalize wlCost (Lb + q + v) rb = C2 at *
  omega

open Classical in
theorem suppEqW_spec (cap : ℕ) (S A B : Fin (ns + 1)) (Rw : Fin 16 ↪ Fin nr) (Q : Fin 12 ↪ Fin nr)
    (rows : ℕ → List ℕ) (R q u v rb Lb : ℕ) (rest : List Bool) (σ : WState ns nr) :
    SuppEqSpec cap S A B Rw Q rows R q u v rb Lb rest σ := by
  intro hd hQR hu hv hrb hfit hcap hst hshL hLR hAb hAh hBb hBh hRw hQ hu' hv' hq' hLv
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨hSA, hSB⟩, hAB, -⟩ := hd
  have hQne : ∀ {i j : Fin 12}, i ≠ j → Q i ≠ Q j := fun h => Q.injective.ne h
  set La := listWord natWord (sysList q rows u) with hLa
  set Lv := listWord natWord (sysList q rows v) with hLv'
  -- the exact start
  set σ0 := (σ.sets A []).sets B [] with hσ0
  have hsim0 : SimW σ0 σ := by
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    by_cases hiB : i = B
    · subst hiB; simp [hσ0]; exact (Worker.blank_rdEq _ hBb 0).symm
    · by_cases hiA : i = A
      · subst hiA; simp [hσ0, Function.update_of_ne hiB]; exact (Worker.blank_rdEq _ hAb 0).symm
      · simp [hσ0, Function.update_of_ne hiB, Function.update_of_ne hiA]; exact RdEq.refl _
  -- write both lists
  obtain ⟨h1, hh1, e1⟩ := writeListM cap S A hSA Rw Q hQR 0 9 (by decide) (by decide) (by decide) rows R q u rb Lb hu
    hrb hfit (by omega) rest σ0 (by simp [hσ0, Function.update_of_ne hSB, Function.update_of_ne hSA, hst])
    (by simp [hσ0]; exact hshL) hLR (by simp [hσ0, Function.update_of_ne hAB, hAh])
    (fun k h12 h13 h15 => by simp [hσ0]; exact hRw k h12 h13 h15)
    (fun i h5 h8 => by simp [hσ0]; exact hQ i (by omega)) (by simp [hσ0]; exact hQ 9 (by decide))
    (by simp [hσ0, hu']) (by simp [hσ0, hq']) (by simp [hσ0, hLv])
  set σ1 := (((appendO σ0 A (Rw 7) (marks La)).setv (Rw 7) 0).setv (Q 9) (marks La).length).seth S h1 with hσ1
  have v1 : ∀ r, r ≠ Rw 7 → r ≠ Q 9 → σ1.val r = σ.val r := fun r h7 h9 => by
    simp [hσ1, Function.update_of_ne h9, Function.update_of_ne h7, appendO, hσ0]
  obtain ⟨h2, hh2, e2⟩ := writeListM cap S B hSB Rw Q hQR 1 10 (by decide) (by decide) (by decide) rows R q v rb Lb hv
    hrb hfit (by omega) rest σ1
    (by simp [hσ1, appendO, Function.update_of_ne hSA, hσ0, Function.update_of_ne hSB, hst])
    (by simp [hσ1]; exact hh1) hLR
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm hAB), Function.update_of_ne (Ne.symm hSB), hσ0, hBh])
    (fun k h12 h13 h15 => by
      by_cases h7 : k = 7
      · subst h7; simp [hσ1, Function.update_of_ne (hQR 9 7).symm]
      · rw [v1 _ (Rw.injective.ne h7) (hQR 9 k).symm]; exact hRw k h12 h13 h15)
    (fun i h5 h8 => by
      rw [v1 _ (hQR i 7) (hQne (by intro h; subst h; simp at h8))]; exact hQ i (by omega))
    (by rw [v1 _ (hQR 10 7) (hQne (by decide))]; exact hQ 10 (by decide))
    (by rw [v1 _ (hQR 1 7) (hQne (by decide)), hv'])
    (by rw [v1 _ (hQR 2 7) (hQne (by decide)), hq'])
    (by rw [v1 _ (hQR 3 7) (hQne (by decide)), hLv])
  set σ2 := (((appendO σ1 B (Rw 7) (marks Lv)).setv (Rw 7) 0).setv (Q 10) (marks Lv).length).seth S h2 with hσ2
  have v2 : ∀ r, r ≠ Rw 7 → r ≠ Q 9 → r ≠ Q 10 → σ2.val r = σ.val r := fun r h7 h9 h10 => by
    rw [← v1 r h7 h9]; simp [hσ2, Function.update_of_ne h10, Function.update_of_ne h7, appendO]
  have s2A : σ2.st A = marks La := by
    simp [hσ2, appendO, Function.update_of_ne hAB, hσ1, hσ0, Function.update_of_ne (Ne.symm hAB)]
  have s2B : σ2.st B = marks Lv := by simp [hσ2, appendO, hσ1, hσ0, Function.update_of_ne (Ne.symm hAB)]
  have s2Ah : σ2.sh A = (marks La).length := by
    simp [hσ2, appendO, Function.update_of_ne (Ne.symm hSA), Function.update_of_ne hAB, hσ1, hσ0, hAh]
  have s2Bh : σ2.sh B = (marks Lv).length := by
    simp [hσ2, appendO, Function.update_of_ne (Ne.symm hSB), hσ1, Function.update_of_ne (Ne.symm hAB), hσ0, hBh]
  have r9 : σ2.val (Q 9) = (marks La).length := by
    simp [hσ2, Function.update_of_ne (hQne (show (9 : Fin 12) ≠ 10 by decide)), appendO,
      Function.update_of_ne (hQR 9 7), hσ1]
  have r10 : σ2.val (Q 10) = (marks Lv).length := by simp [hσ2]
  have r5 : σ2.val (Q 5) = 0 := by
    rw [v2 _ (hQR 5 7) (hQne (by decide)) (hQne (by decide))]; exact hQ 5 (by decide)
  have r8 : σ2.val (Q 8) = 0 := by
    rw [v2 _ (hQR 8 7) (hQne (by decide)) (hQne (by decide))]; exact hQ 8 (by decide)
  have r7 : σ2.val (Q 7) = 0 := by
    rw [v2 _ (hQR 7 7) (hQne (by decide)) (hQne (by decide))]; exact hQ 7 (by decide)
  have r11 : σ2.val (Q 11) = 0 := by
    rw [v2 _ (hQR 11 7) (hQne (by decide)) (hQne (by decide))]; exact hQ 11 (by decide)
  have hLaL : (marks La).length ≤ Lb + 4 * u + 12 := sysList_len q rows R Lb u hu hLR
  have hLvL : (marks Lv).length ≤ Lb + 4 * v + 12 := sysList_len q rows R Lb v hv hLR
  have hLa2 : 2 * La.length ≤ Lb + 4 * u + 12 := by rw [← Codec.marks_length]; exact hLaL
  have hLv2 : 2 * Lv.length ≤ Lb + 4 * v + 12 := by rw [← Codec.marks_length]; exact hLvL
  -- rewind `A` and `B`
  have e3 := Codec.dupR_spec cap (Q 9) (Q 5) (Q 8) (hQne (by decide)) (hQne (by decide)) (hQne (by decide)) σ2 r8
    (by rw [r9, r5]; omega)
  rw [r9, r5, Nat.zero_add] at e3
  set σ3 := σ2.setv (Q 5) (marks La).length with hσ3
  have e4 := wrewind_spec (cap := cap) A (Q 5) (marks La).length σ3 (by simp [hσ3]) (by simp [hσ3]; omega)
  set σ4 := (σ3.setv (Q 5) 0).seth A (σ3.sh A - (marks La).length) with hσ4
  have e5 := Codec.dupR_spec cap (Q 10) (Q 5) (Q 8) (hQne (by decide)) (hQne (by decide)) (hQne (by decide)) σ4
    (by simp [hσ4, hσ3, Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 5 by decide)), r8])
    (by simp [hσ4, hσ3, Function.update_of_ne (hQne (show (10 : Fin 12) ≠ 5 by decide)), r10]; omega)
  have r10' : σ4.val (Q 10) = (marks Lv).length := by
    simp [hσ4, hσ3, Function.update_of_ne (hQne (show (10 : Fin 12) ≠ 5 by decide)), r10]
  rw [r10', show σ4.val (Q 5) = 0 by simp [hσ4], Nat.zero_add] at e5
  set σ5 := σ4.setv (Q 5) (marks Lv).length with hσ5
  have e6 := wrewind_spec (cap := cap) B (Q 5) (marks Lv).length σ5 (by simp [hσ5]) (by simp [hσ5]; omega)
  set σ6 := (σ5.setv (Q 5) 0).seth B (σ5.sh B - (marks Lv).length) with hσ6
  -- compare
  have s6A : σ6.st A = marks La := by simp [hσ6, hσ5, hσ4, hσ3, s2A]
  have s6B : σ6.st B = marks Lv := by simp [hσ6, hσ5, hσ4, hσ3, s2B]
  have e7 := cmpM cap A B (Q 11) (Q 7) hAB (hQne (by decide)) σ6 La Lv s6A s6B
    (by simp [hσ6, hσ5, hσ4, hσ3, Function.update_of_ne hAB, s2Ah])
    (by simp [hσ6, hσ5, hσ4, hσ3, Function.update_of_ne (Ne.symm hAB), s2Bh])
    (by simp [hσ6, hσ5, hσ4, hσ3, Function.update_of_ne (hQne (show (11 : Fin 12) ≠ 5 by decide)), r11])
    (by simp [hσ6, hσ5, hσ4, hσ3, Function.update_of_ne (hQne (show (7 : Fin 12) ≠ 5 by decide)), r7])
    (by rw [Codec.marks_length] at hLaL; omega)
  set σ7 := σ6.setv (Q 11) (decide (La ≠ Lv)).toNat with hσ7
  -- blank both
  have e8 := blankM cap A (Q 9) (Q 8) (hQne (by decide)) σ7 (marks La) (by simp [hσ7, s6A])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, Function.update_of_ne hAB, s2Ah])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, Function.update_of_ne (hQne (show (9 : Fin 12) ≠ 11 by decide)),
      Function.update_of_ne (hQne (show (9 : Fin 12) ≠ 5 by decide)), r9])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 11 by decide)),
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 5 by decide)), r8]) (by omega)
  set σ8 := (σ7.sets A (List.replicate (marks La).length false)).setv (Q 9) 0 with hσ8
  have e9 := blankM cap B (Q 10) (Q 8) (hQne (by decide)) σ8 (marks Lv)
    (by simp [hσ8, Function.update_of_ne (Ne.symm hAB), hσ7, s6B])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, Function.update_of_ne (Ne.symm hAB), s2Bh])
    (by simp [hσ8, Function.update_of_ne (hQne (show (10 : Fin 12) ≠ 9 by decide)), hσ7, hσ6, hσ5, hσ4, hσ3,
      Function.update_of_ne (hQne (show (10 : Fin 12) ≠ 11 by decide)),
      Function.update_of_ne (hQne (show (10 : Fin 12) ≠ 5 by decide)), r10])
    (by simp [hσ8, Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 9 by decide)), hσ7, hσ6, hσ5, hσ4, hσ3,
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 11 by decide)),
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 5 by decide)), r8]) (by omega)
  set σ9 := (σ8.sets B (List.replicate (marks Lv).length false)).setv (Q 10) 0 with hσ9
  -- the flag
  have r9_4 : σ9.val (Q 4) = 0 := by
    have : σ.val (Q 4) = 0 := hQ 4 (by decide)
    simp [hσ9, Function.update_of_ne (hQne (show (4 : Fin 12) ≠ 10 by decide)), hσ8,
      Function.update_of_ne (hQne (show (4 : Fin 12) ≠ 9 by decide)), hσ7,
      Function.update_of_ne (hQne (show (4 : Fin 12) ≠ 11 by decide)), hσ6, hσ5, hσ4, hσ3,
      Function.update_of_ne (hQne (show (4 : Fin 12) ≠ 5 by decide))]
    rw [v2 _ (hQR 4 7) (hQne (by decide)) (hQne (by decide))]; exact this
  have r9_11 : σ9.val (Q 11) = (decide (La ≠ Lv)).toNat := by
    simp [hσ9, Function.update_of_ne (hQne (show (11 : Fin 12) ≠ 10 by decide)), hσ8,
      Function.update_of_ne (hQne (show (11 : Fin 12) ≠ 9 by decide)), hσ7]
  set b := decide (sysList q rows u = sysList q rows v) with hbdef
  have hbL : decide (La = Lv) = b := by rw [hLa, hLv', hbdef]; exact decide_eq_decide.mpr (listWord_nat_inj _ _)
  set σ10 := (σ9.setv (Q 11) 0).setv (Q 4) b.toNat with hσ10
  have e10 : WExec cap (.ifr (Q 11) (WM.clear (Q 11)) (.inc (Q 4))) σ9 σ10 5 := by
    by_cases hne : La = Lv
    · have hb : b = true := by rw [← hbL]; simp [hne]
      have h0 : σ9.val (Q 11) = 0 := by rw [r9_11]; simp [hne]
      have e := WExec.inc (cap := cap) (Q 4) σ9 (by rw [r9_4]; omega)
      rw [r9_4] at e
      refine (WExec.ifrF h0 e).cast cap ?_ (by omega)
      have hs : σ9.setv (Q 11) 0 = σ9 := by rw [← h0, wsetv_same]
      rw [hσ10, hb, hs]; rfl
    · have hb : b = false := by rw [← hbL]; simp [hne]
      have h1' : σ9.val (Q 11) = 1 := by rw [r9_11]; simp [hne]
      have e := wclear_spec (cap := cap) (Q 11) 1 σ9 h1' (by omega)
      refine (WExec.ifrT (by omega) e).cast cap ?_ (by omega)
      rw [hσ10, hb]
      apply WState.eq <;> try rfl
      funext r; by_cases hr4 : r = Q 4
      · subst hr4; simp [Function.update_of_ne (hQne (show (4 : Fin 12) ≠ 11 by decide)), r9_4]
      · simp [Function.update_of_ne hr4]
  -- rewind the record
  have h3 : σ10.val (Q 3) = Lb := by
    simp [hσ10, Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 4 by decide)),
      Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 11 by decide)), hσ9,
      Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 10 by decide)), hσ8,
      Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 9 by decide)), hσ7, hσ6, hσ5, hσ4, hσ3,
      Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 5 by decide))]
    rw [v2 _ (hQR 3 7) (hQne (by decide)) (hQne (by decide)), hLv]
  have e11 := Codec.rewindCW_spec cap S (Q 3) (Q 7) (Q 8) (hQne (by decide)) (hQne (by decide)) (hQne (by decide)) σ10
    (by simp [hσ10, Function.update_of_ne (hQne (show (7 : Fin 12) ≠ 4 by decide)), hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3,
      Function.update_of_ne (hQne (show (7 : Fin 12) ≠ 10 by decide)),
      Function.update_of_ne (hQne (show (7 : Fin 12) ≠ 9 by decide)),
      Function.update_of_ne (hQne (show (7 : Fin 12) ≠ 11 by decide)),
      Function.update_of_ne (hQne (show (7 : Fin 12) ≠ 5 by decide)), r7])
    (by simp [hσ10, Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 4 by decide)), hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3,
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 10 by decide)),
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 9 by decide)),
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 11 by decide)),
      Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 5 by decide)), r8])
    (by
      have h3 : σ10.val (Q 3) = Lb := by
        simp [hσ10, Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 4 by decide)),
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 11 by decide)), hσ9,
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 10 by decide)), hσ8,
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 9 by decide)), hσ7, hσ6, hσ5, hσ4, hσ3,
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 5 by decide))]
        rw [v2 _ (hQR 3 7) (hQne (by decide)) (hQne (by decide)), hLv]
      have hS : σ10.sh S = h2 := by
        simp [hσ10, hσ9, hσ8, hσ7, hσ6, Function.update_of_ne hSB, hσ5, hσ4, Function.update_of_ne hSA, hσ3, hσ2]
      rw [h3, hS]; exact hh2)
    (by
      have h3 : σ10.val (Q 3) = Lb := by
        simp [hσ10, Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 4 by decide)),
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 11 by decide)), hσ9,
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 10 by decide)), hσ8,
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 9 by decide)), hσ7, hσ6, hσ5, hσ4, hσ3,
          Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 5 by decide))]
        rw [v2 _ (hQR 3 7) (hQne (by decide)) (hQne (by decide)), hLv]
      rw [h3]; omega)
  set σ11 := σ10.seth S 0 with hσ11
  have E := WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
    (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11)))))))))
  obtain ⟨τ, eτ, hsτ⟩ := wxexec_sim (WXExec.wm E) σ hsim0
  refine ⟨τ, eτ.mono ?_, CheckedPCPP.SimW.trans ?_ hsτ⟩
  · rw [h3]
    simp only [Codec.marks_length]
    exact suppCost_le Lb q u v rb _ _ hLa2 hLv2
  · -- the end state reads like the ideal
    have hva : ∀ r, r ≠ Q 4 → σ11.val r = σ.val r := by
      intro r h4
      by_cases h11 : r = Q 11
      · subst h11; simp [hσ11, hσ10, Function.update_of_ne h4]; exact (hQ 11 (by decide)).symm
      by_cases h10 : r = Q 10
      · subst h10; simp [hσ11, hσ10, Function.update_of_ne h4, Function.update_of_ne h11, hσ9]
        exact (hQ 10 (by decide)).symm
      by_cases h9 : r = Q 9
      · subst h9; simp [hσ11, hσ10, Function.update_of_ne h4, Function.update_of_ne h11, hσ9,
          Function.update_of_ne h10, hσ8]; exact (hQ 9 (by decide)).symm
      by_cases h5 : r = Q 5
      · subst h5; simp [hσ11, hσ10, Function.update_of_ne h4, Function.update_of_ne h11, hσ9,
          Function.update_of_ne h10, hσ8, Function.update_of_ne h9, hσ7, hσ6]; exact (hQ 5 (by decide)).symm
      by_cases h7 : r = Rw 7
      · subst h7; simp [hσ11, hσ10, Function.update_of_ne h4, Function.update_of_ne h11, hσ9,
          Function.update_of_ne h10, hσ8, Function.update_of_ne h9, hσ7, hσ6, Function.update_of_ne h5, hσ5, hσ4, hσ3,
          hσ2]
        exact (hRw 7 (by decide) (by decide) (by decide)).symm
      simp [hσ11, hσ10, Function.update_of_ne h4, Function.update_of_ne h11, hσ9, Function.update_of_ne h10, hσ8,
        Function.update_of_ne h9, hσ7, hσ6, Function.update_of_ne h5, hσ5, hσ4, hσ3]
      exact v2 r h7 h9 h10
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · funext i
      by_cases hiS : i = S
      · subst hiS; simp [suppIdeal, hσ11, Function.update_of_ne hSA, Function.update_of_ne hSB]
      by_cases hiA : i = A
      · subst hiA
        simp [suppIdeal, hσ11, Function.update_of_ne (Ne.symm hSA), Function.update_of_ne hAB, hσ10, hσ9, hσ8, hσ7, hσ6,
          hσ5, hσ4, hσ3, s2Ah]
      by_cases hiB : i = B
      · subst hiB
        simp [suppIdeal, hσ11, Function.update_of_ne (Ne.symm hSB), hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4,
          Function.update_of_ne (Ne.symm hAB), hσ3, s2Bh]
      simp [suppIdeal, hσ11, Function.update_of_ne hiS, Function.update_of_ne hiA, Function.update_of_ne hiB, hσ10, hσ9,
        hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, appendO, hσ1, hσ0]
    · funext r
      by_cases h4 : r = Q 4
      · subst h4; simp [suppIdeal, hσ11, hσ10]
      · rw [hva r h4]; simp [suppIdeal, Function.update_of_ne h4]
    · simp [suppIdeal, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, appendO, hσ1, hσ0]
    · by_cases hiA : i = A
      · subst hiA
        simp [suppIdeal, Function.update_of_ne hAB, Function.update_of_ne (Ne.symm hAB), hσ11, hσ10, hσ9, hσ8]
        exact (blank_nil (replicate_false_blank _)).symm
      by_cases hiB : i = B
      · subst hiB
        simp [suppIdeal, hσ11, hσ10, hσ9]
        exact (blank_nil (replicate_false_blank _)).symm
      have : σ11.st i = σ.st i := by
        simp [hσ11, hσ10, hσ9, Function.update_of_ne hiB, hσ8, Function.update_of_ne hiA, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2,
          appendO, hσ1, hσ0]
      rw [this]; simp [suppIdeal, Function.update_of_ne hiA, Function.update_of_ne hiB]; exact RdEq.refl _

end NearCubicGates.Close.WorkerArith
