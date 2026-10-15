import Proof.Gates.WorkerArith.SuppEqA
import Proof.Gates.Counter.Main

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (listWord)

variable {ns nr : ℕ}

theorem natWord_mem_len {l : List ℕ} {x : ℕ} (hx : x ∈ l) : (natWord x).length ≤ (l.flatMap natWord).length := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with rfl | h
    · omega
    · have := ih h; omega

theorem list_len_le_flat (l : List ℕ) : l.length ≤ (l.flatMap natWord).length := by
  induction l with
  | nil => simp
  | cons y l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; rw [natWord_len_c]; omega

/-- A row of the record is no longer than the record. -/
theorem row_le_record (rows : ℕ → List ℕ) (R r : ℕ) (hr : r < R) :
    (marks (listWord natWord (rows r))).length ≤ (Codec.rowPrefix rows R).length := by
  have := congrArg List.length (Codec.rowPrefix_split rows hr)
  simp only [List.length_append] at this; omega

/-- The cost class of one list writer. -/
def wlCost (Z rb : ℕ) : ℕ := 6000 * (Z + 1) ^ 2 * (rb + 1)

theorem wlSysCost (u q Lb rb P M : ℕ) (hP : P ≤ 3300 * (Lb + q + u + 1) ^ 2) (hM : M ≤ 4 * u + 12) :
    18 * u + 3 + 1 + (18 * q + 3 + 1 + (8 * q + 1)) + 1 +
      (3 * (q - u) + 1 + 1 +
              (18 * u + 3 + 1 +
                (16 * (natWord 1).length + 1 + P + 1 + (3 * u + 1))) +
            1 +
          1 +
        (7 * M + 1)) ≤ wlCost (Lb + q + u) rb := by
  have h1 : (Lb + q + u + 1) ^ 2 * 1 ≤ (Lb + q + u + 1) ^ 2 * (rb + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : Lb + q + u + 1 ≤ (Lb + q + u + 1) ^ 2 := by nlinarith
  have e : wlCost (Lb + q + u) rb = 6000 * ((Lb + q + u + 1) ^ 2 * (rb + 1)) := by unfold wlCost; ring
  have h3 : (natWord 1).length = 3 := rfl
  rw [e, h3]
  generalize (Lb + q + u + 1) ^ 2 * (rb + 1) = W2 at *
  generalize (Lb + q + u + 1) ^ 2 = W1 at *
  omega

theorem wlRowCost (u q Lb rb X M : ℕ) (hX : X ≤ 4000 * (Lb + q + u + 1) ^ 2 * (rb + 1)) (hM : M ≤ Lb) :
    18 * u + 3 + 1 + (18 * q + 3 + 1 + (8 * q + 1)) + 1 +
      (7 * (u - q) + 1 + 1 + (X + 1 + (3 * (u - q) + 1)) + 1 + 1 + (7 * M + 1)) ≤ wlCost (Lb + q + u) rb := by
  have h1 : (Lb + q + u + 1) ^ 2 * 1 ≤ (Lb + q + u + 1) ^ 2 * (rb + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : Lb + q + u + 1 ≤ (Lb + q + u + 1) ^ 2 := by nlinarith
  have e : wlCost (Lb + q + u) rb = 6000 * ((Lb + q + u + 1) ^ 2 * (rb + 1)) := by unfold wlCost; ring
  have e2 : 4000 * (Lb + q + u + 1) ^ 2 * (rb + 1) = 4000 * ((Lb + q + u + 1) ^ 2 * (rb + 1)) := by ring
  rw [e]; rw [e2] at hX
  generalize (Lb + q + u + 1) ^ 2 * (rb + 1) = W2 at *
  generalize (Lb + q + u + 1) ^ 2 = W1 at *
  omega

theorem writeListM (cap : ℕ) (S o : Fin (ns + 1)) (hSo : S ≠ o) (Rw : Fin 16 ↪ Fin nr) (Q : Fin 12 ↪ Fin nr)
    (hQR : ∀ i k, Q i ≠ Rw k) (iU iO : Fin 12) (hiU : iU.val ≤ 1) (hiO1 : 9 ≤ iO.val) (hiO2 : iO.val ≤ 10)
    (rows : ℕ → List ℕ) (R q u rb Lb : ℕ) (hu : u < q + R) (hrb : ∀ j < R, Codec.rowCost (rows j) ≤ rb)
    (hfit : ∀ j < R, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
      ∀ x ∈ rows j, natBitLength x + 1 ≤ cap)
    (hcap : 20 * (Lb + q + u + 10) ≤ cap) (rest : List Bool) (τ : WState ns nr)
    (hst : τ.st S = Codec.rowPrefix rows R ++ rest) (hshL : τ.sh S ≤ Lb) (hLR : (Codec.rowPrefix rows R).length ≤ Lb)
    (ho : τ.sh o = (τ.st o).length) (hRw : ∀ k : Fin 16, k ≠ 12 → k ≠ 13 → k ≠ 15 → τ.val (Rw k) = 0)
    (hQz : ∀ i : Fin 12, 5 ≤ i.val → i.val ≤ 8 → τ.val (Q i) = 0) (hQO : τ.val (Q iO) = 0)
    (hU : τ.val (Q iU) = u) (hq : τ.val (Q 2) = q) (hLv : τ.val (Q 3) = Lb) :
    ∃ h', h' ≤ Lb ∧ WExec cap (writeListW S o Rw Q (Q iU) (Q iO)) τ
      ((((appendO τ o (Rw 7) (marks (listWord natWord (sysList q rows u)))).setv (Rw 7) 0).setv (Q iO)
        (marks (listWord natWord (sysList q rows u))).length).seth S h') (wlCost (Lb + q + u) rb) := by
  have hQne : ∀ {i j : Fin 12}, i ≠ j → Q i ≠ Q j := fun h => Q.injective.ne h
  have hRne : ∀ {a b : Fin 16}, a ≠ b → Rw a ≠ Rw b := fun h => Rw.injective.ne h
  have hiU2 : iU ≠ 2 := fun h => by subst h; simp at hiU
  have hU5 : iU ≠ 5 := fun h => by subst h; simp at hiU
  have hU6 : iU ≠ 6 := fun h => by subst h; simp at hiU
  have hU7 : iU ≠ 7 := fun h => by subst h; simp at hiU
  have hU8 : iU ≠ 8 := fun h => by subst h; simp at hiU
  have hUO : iU ≠ iO := fun h => by subst h; omega
  -- `D := u − q`, `F := q − u`
  have hnd0 : ([iU, 2, 5, 6, 7, 8] : List (Fin 12)).Nodup :=
    List.nodup_cons.2 ⟨by simp [hiU2, hU5, hU6, hU7, hU8], by decide⟩
  have hnd : [Q iU, Q 2, Q 5, Q 6, Q 7, Q 8].Nodup := by
    have := hnd0.map Q.injective; simpa using this
  have e1 := Worker.ltSubW_spec (cap := cap) (Q iU) (Q 2) (Q 5) (Q 6) (Q 7) (Q 8) hnd τ (hQz 5 (by decide) (by decide))
    (hQz 6 (by decide) (by decide)) (hQz 7 (by decide) (by decide)) (hQz 8 (by decide) (by decide)) (by omega)
  rw [hU, hq] at e1
  set τ1 := (τ.setv (Q 5) (u - q)).setv (Q 6) (q - u) with hτ1
  have v1 : ∀ k : Fin 16, τ1.val (Rw k) = τ.val (Rw k) := fun k => by
    simp [hτ1, Function.update_of_ne (hQR 6 k).symm, Function.update_of_ne (hQR 5 k).symm]
  set L := listWord natWord (sysList q rows u) with hL
  by_cases hlt : u < q
  · -- the outer randomness coordinate: `parSys`
    have hsys : sysList q rows u = [u] := by simp [sysList, hlt]
    have e2 := wclear_spec (cap := cap) (Q 6) (q - u) τ1 (by simp [hτ1]) (by simp [hτ1]; omega)
    set τ2 := τ1.setv (Q 6) 0 with hτ2
    have hU2 : τ2.val (Q iU) = u := by
      simp [hτ2, hτ1, Function.update_of_ne (hQne hU6), Function.update_of_ne (hQne hU5), hU]
    have h14 : τ2.val (Rw 14) = 0 := by
      rw [hτ2, WState.setv_val, Function.update_of_ne (hQR 6 14).symm, v1, hRw 14 (by decide) (by decide) (by decide)]
    have e3 := Codec.dupR_spec cap (Q iU) (Rw 14) (Q 8) (hQR iU 14) (hQne (by intro h; subst h; simp at hiU))
      (hQR 8 14).symm τ2 (by simp [hτ2, hτ1, Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 6 by decide)),
        Function.update_of_ne (hQne (show (8 : Fin 12) ≠ 5 by decide)), hQz 8 (by decide) (by decide)])
      (by rw [hU2, h14]; omega)
    rw [hU2, h14, Nat.zero_add] at e3
    set τ3 := τ2.setv (Rw 14) u with hτ3
    have e4 := Codec.parSys_spec cap o Rw u τ3 (by simp [hτ3, hτ2, hτ1, ho]) (by simp [hτ3])
      (fun k hk1 hk6 => by
        have : k ≠ 14 := by intro h; subst h; simp at hk6
        simp [hτ3, Function.update_of_ne (hRne this), hτ2, Function.update_of_ne (hQR 6 k).symm, v1]
        exact hRw k (by intro h; subst h; simp at hk6) (by intro h; subst h; simp at hk6)
          (by intro h; subst h; simp at hk6))
      (by
        have h7 : τ3.val (Rw 7) = 0 := by
          simp [hτ3, Function.update_of_ne (hRne (show (7 : Fin 16) ≠ 14 by decide)), hτ2,
            Function.update_of_ne (hQR 6 7).symm, v1, hRw 7 (by decide) (by decide) (by decide)]
        rw [h7]; have := nbl_le u; have : (natWord 1).length = 3 := rfl; omega)
    have hlen : (marks (listWord natWord [u])).length ≤ 4 * u + 12 := by
      rw [Codec.marks_length]
      simp only [listWord, List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_singleton, natWord_len_c]
      have := nbl_le u; have : natBitLength 1 = 1 := rfl; omega
    set τ4 := appendO τ3 o (Rw 7) (marks (listWord natWord [u])) with hτ4
    have e5 := wclear_spec (cap := cap) (Rw 14) u τ4
      (by simp [hτ4, appendO, Function.update_of_ne (hRne (show (14 : Fin 16) ≠ 7 by decide)), hτ3])
      (by simp [hτ4, appendO, Function.update_of_ne (hRne (show (14 : Fin 16) ≠ 7 by decide)), hτ3]; omega)
    set τ5 := τ4.setv (Rw 14) 0 with hτ5
    have hm7 : τ5.val (Rw 7) = (marks (listWord natWord [u])).length := by
      simp [hτ5, Function.update_of_ne (hRne (show (7 : Fin 16) ≠ 14 by decide)), hτ4, appendO, hτ3,
        hτ2, Function.update_of_ne (hQR 6 7).symm, v1, hRw 7 (by decide) (by decide) (by decide)]
    have hO5 : τ5.val (Q iO) = 0 := by
      simp [hτ5, Function.update_of_ne (hQR iO 14), hτ4, appendO, Function.update_of_ne (hQR iO 7), hτ3,
        hτ2, Function.update_of_ne (hQne (show iO ≠ 6 by intro h; subst h; simp at hiO1)), hτ1,
        Function.update_of_ne (hQne (show iO ≠ 5 by intro h; subst h; simp at hiO1)), hQO]
    have e6 := wmove_spec (cap := cap) (Rw 7) (Q iO) (hQR iO 7).symm _ τ5 hm7 (by rw [hm7]; omega)
      (by rw [hO5, hm7]; omega)
    rw [hO5, hm7, Nat.zero_add] at e6
    refine ⟨τ.sh S, hshL, ?_⟩
    rw [hL, hsys]
    refine WExec.cast cap (WExec.seq e1 (WExec.seq (WExec.ifrT (by simp [hτ1]; omega)
      (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) e6)) ?_ ?_
    · apply WState.eq
      · funext i; by_cases hi : i = S
        · subst hi; simp [hτ5, hτ4, appendO, Function.update_of_ne hSo, hτ3, hτ2, hτ1]
        · simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1, Function.update_of_ne hi]
      · simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1]
      · funext r
        by_cases hr1 : r = Q iO
        · subst hr1; simp
        · by_cases hr2 : r = Rw 7
          · subst hr2; simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1, Function.update_of_ne hr1]
          · by_cases hr3 : r = Rw 14
            · subst hr3
              simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                Function.update_of_ne (hQR 6 14).symm, Function.update_of_ne (hQR 5 14).symm,
                hRw 14 (by decide) (by decide) (by decide)]
            · by_cases hr4 : r = Q 6
              · subst hr4; simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                  Function.update_of_ne hr3, hQz 6 (by decide) (by decide)]
              · by_cases hr5 : r = Q 5
                · subst hr5
                  simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                    Function.update_of_ne hr3, Function.update_of_ne hr4, hQz 5 (by decide) (by decide)]
                  omega
                · simp [hτ5, hτ4, appendO, hτ3, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                    Function.update_of_ne hr3, Function.update_of_ne hr4, Function.update_of_ne hr5]
      · rfl
    · exact wlSysCost u q Lb rb _ _ (nbl_mul_le u (Lb + q + u) 100 200 10 (by omega)) hlen
  · -- a code row: `parRow`
    have hr : u - q < R := by omega
    have hsys : sysList q rows u = rows (u - q) := by simp [sysList, hlt]
    have hrow := row_le_record rows R (u - q) hr
    have hrowL : (listWord natWord (rows (u - q))).length ≤ Lb := by rw [Codec.marks_length] at hrow; omega
    have hlenL : (rows (u - q)).length ≤ Lb := by
      have := list_len_le_flat (rows (u - q)); simp only [listWord, List.length_append] at hrowL; omega
    have hxL : ∀ x ∈ rows (u - q), natBitLength x ≤ Lb := by
      intro x hx; have := natWord_mem_len hx; rw [natWord_len_c] at this
      simp only [listWord, List.length_append] at hrowL; omega
    have h5 : τ1.val (Q 5) = u - q := by
      simp [hτ1, Function.update_of_ne (hQne (show (5 : Fin 12) ≠ 6 by decide))]
    have h14' : τ1.val (Rw 14) = 0 := by rw [v1, hRw 14 (by decide) (by decide) (by decide)]
    have e2 := wmove_spec (cap := cap) (Q 5) (Rw 14) (hQR 5 14) (u - q) τ1 h5 (by rw [h5]; omega)
      (by rw [h5, h14']; omega)
    rw [h5, h14', Nat.zero_add] at e2
    set τ2 := (τ1.setv (Q 5) 0).setv (Rw 14) (u - q) with hτ2
    have v2 : ∀ k : Fin 16, k ≠ 14 → τ2.val (Rw k) = τ.val (Rw k) := fun k hk => by
      simp [hτ2, Function.update_of_ne (hRne hk), Function.update_of_ne (hQR 5 k).symm, v1]
    have e3 := Codec.parRow_spec cap S o hSo Rw (Q 3) (fun k => hQR 3 k) rows R (u - q) hr rb
      (marks (listWord natWord (rows (u - q)))).length Lb hrb hfit (by omega) (by omega)
      (by rw [Codec.marks_length]; have := nbl_le (rows (u - q)).length; omega) rest τ2
      (by simp [hτ2, hτ1, hst]) (by simp [hτ2, hτ1]; exact hshL) (by simp [hτ2, hτ1, ho])
      (fun k h7 h12 h13 h14 h15 => by rw [v2 k h14]; exact hRw k h12 h13 h15) (by simp [hτ2])
      (by simp [hτ2, Function.update_of_ne (hQR 3 14), hτ1, Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 5 by decide)),
        Function.update_of_ne (hQne (show (3 : Fin 12) ≠ 6 by decide)), hLv])
      (by rw [v2 7 (by decide), hRw 7 (by decide) (by decide) (by decide)]; omega)
    set τ3 := appendO (τ2.seth S (Codec.rowPrefix rows (u - q + 1)).length) o (Rw 7)
      (marks (listWord natWord (rows (u - q)))) with hτ3
    have e4 := wclear_spec (cap := cap) (Rw 14) (u - q) τ3
      (by simp [hτ3, appendO, Function.update_of_ne (hRne (show (14 : Fin 16) ≠ 7 by decide)), hτ2])
      (by simp [hτ3, appendO, Function.update_of_ne (hRne (show (14 : Fin 16) ≠ 7 by decide)), hτ2]; omega)
    set τ4 := τ3.setv (Rw 14) 0 with hτ4
    have hm7 : τ4.val (Rw 7) = (marks (listWord natWord (rows (u - q)))).length := by
      simp [hτ4, Function.update_of_ne (hRne (show (7 : Fin 16) ≠ 14 by decide)), hτ3, appendO,
        v2 7 (by decide), hRw 7 (by decide) (by decide) (by decide)]
    have hO4 : τ4.val (Q iO) = 0 := by
      simp [hτ4, Function.update_of_ne (hQR iO 14), hτ3, appendO, Function.update_of_ne (hQR iO 7), hτ2,
        hτ1, Function.update_of_ne (hQne (show iO ≠ 6 by intro h; subst h; simp at hiO1)),
        Function.update_of_ne (hQne (show iO ≠ 5 by intro h; subst h; simp at hiO1)), hQO]
    have e5 := wmove_spec (cap := cap) (Rw 7) (Q iO) (hQR iO 7).symm _ τ4 hm7 (by rw [hm7]; omega)
      (by rw [hO4, hm7]; omega)
    rw [hO4, hm7, Nat.zero_add] at e5
    have hSlen : (Codec.rowPrefix rows (u - q + 1)).length ≤ Lb := by
      have e := congrArg List.length (Codec.rowPrefix_split rows hr)
      have e2 := congrArg List.length (Codec.rowPrefix_succ rows (u - q))
      simp only [List.length_append] at e e2; omega
    refine ⟨(Codec.rowPrefix rows (u - q + 1)).length, hSlen, ?_⟩
    rw [hL, hsys]
    refine WExec.cast cap (WExec.seq e1 (WExec.seq (WExec.ifrF (by simp [hτ1]; omega)
      (WExec.seq e2 (WExec.seq e3 e4))) e5)) ?_ ?_
    · apply WState.eq
      · funext i; by_cases hi : i = S
        · subst hi; simp [hτ4, hτ3, appendO, Function.update_of_ne hSo]
        · by_cases hio : i = o
          · subst hio; simp [hτ4, hτ3, appendO, Function.update_of_ne hi, hτ2, hτ1]
          · simp [hτ4, hτ3, appendO, hτ2, hτ1, Function.update_of_ne hi, Function.update_of_ne hio]
      · simp [hτ4, hτ3, appendO, hτ2, hτ1]
      · funext r
        by_cases hr1 : r = Q iO
        · subst hr1; simp
        · by_cases hr2 : r = Rw 7
          · subst hr2; simp [hτ4, hτ3, appendO, hτ2, hτ1, Function.update_of_ne hr1]
          · by_cases hr3 : r = Rw 14
            · subst hr3
              simp [hτ4, hτ3, appendO, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                Function.update_of_ne (hQR 6 14).symm, Function.update_of_ne (hQR 5 14).symm,
                hRw 14 (by decide) (by decide) (by decide)]
            · by_cases hr4 : r = Q 5
              · subst hr4; simp [hτ4, hτ3, appendO, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                  Function.update_of_ne hr3, hQz 5 (by decide) (by decide)]
              · by_cases hr5 : r = Q 6
                · subst hr5
                  simp [hτ4, hτ3, appendO, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                    Function.update_of_ne hr3, Function.update_of_ne hr4, hQz 6 (by decide) (by decide)]
                  omega
                · simp [hτ4, hτ3, appendO, hτ2, hτ1, Function.update_of_ne hr1, Function.update_of_ne hr2,
                    Function.update_of_ne hr3, Function.update_of_ne hr4, Function.update_of_ne hr5]
      · rfl
    · have hp := parRow_cost_le Lb (u - q) rb (rows (u - q)) (Lb + q + u) rb (by omega) (by omega) le_rfl
        (by omega) (fun x hx => le_trans (hxL x hx) (by omega))
      exact wlRowCost u q Lb rb _ _ hp (le_trans hrow hLR)

end NearCubicGates.Close.WorkerArith
