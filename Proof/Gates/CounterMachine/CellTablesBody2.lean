import Proof.Gates.CounterMachine.CellTablesBody1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

theorem digitsM_rep (q t : ℕ) : ∀ D : ℕ,
    Cells.digitsM (List.replicate D q) t = (List.range D).map (fun i => t / q ^ (D - 1 - i) % q)
  | 0 => rfl
  | D + 1 => by
    rw [List.replicate_succ, Cells.digitsM, List.prod_replicate, digitsM_rep q t D, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    refine List.cons_eq_cons.mpr ⟨by simp, ?_⟩
    apply List.map_congr_left; intro i hi
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show D + 1 - 1 - (i + 1) = D - 1 - i by omega]

def hfold (B : ℕ) (k : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc x => acc * B + x) k

theorem foldl_lt (B : ℕ) : ∀ (l : List ℕ) (k : ℕ), (∀ x ∈ l, x < B) → hfold B k l < (k + 1) * B ^ l.length
  | [], k, _ => by simp [hfold]
  | x :: l, k, h => by
    have hx := h x (by simp)
    have ih := foldl_lt B l (k * B + x) (fun y hy => h y (by simp [hy]))
    simp only [hfold, List.foldl_cons, List.length_cons] at ih ⊢
    calc _ < (k * B + x + 1) * B ^ l.length := ih
      _ ≤ ((k + 1) * B) * B ^ l.length := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (k + 1) * B ^ (l.length + 1) := by ring

theorem hfold_snoc (B k : ℕ) (l : List ℕ) (x : ℕ) : hfold B k (l ++ [x]) = hfold B k l * B + x := by
  simp [hfold, List.foldl_append]

def digB : St VV MM :=
  .seq (.op (.dm bPw lQ bQu bJk)) (.seq (.op (.copy bPw bQu)) (.seq (.op (.dm lT bPw bQu bJk))
  (.seq (.op (.dm bQu lQ bJk bDig)) (.seq (emV bDig) (.seq (.op (.mul bKey kB2 bTmp)) (.seq (.op (.copy bKey bTmp))
  (.op (.add bKey bDig))))))))

def digL : St VV MM := forS bI kD digB

def digT : List (Fin VV) := [bI, bPw, bQu, bJk, bDig, bTmp, bKey, t3, t5, t6, t7, t8, t9]

/-- The digits of `t`. -/
def digs (q t D : ℕ) : List ℕ := (List.range D).map (fun i => t / q ^ (D - 1 - i) % q)

theorem digs_take (q t D i : ℕ) (hi : i < D) : (digs q t D).take (i + 1) = (digs q t D).take i ++
    [t / q ^ (D - 1 - i) % q] := by
  unfold digs
  rw [List.take_add_one]
  simp [List.getElem?_map, List.getElem?_range hi]

theorem digL_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (q t D B key0 Λ : ℕ) (hq : 2 ≤ q)
    (hQ : a.env lQ = q) (hT : a.env lT = t) (hD : a.env kD = D) (hB : a.env kB2 = B) (hP : a.env bPw = q ^ D)
    (hK : a.env bKey = key0) (hqD : 2 * q ^ D ≤ 2 ^ C.Wd) (hDW : D < 2 ^ C.Wd) (hqB : q ≤ B)
    (hkey : (key0 + 1) * B ^ D ≤ 2 ^ C.Wd) (hΛ : natBitLength q ≤ Λ)
    (hk : a.kin.length + ((digs q t D).flatMap natWord).length ≤ C.Lk) :
    Hs C digL a (D * (40 * Λ + 60 + 4) + 4) (fun e => e.kin = a.kin ++ (digs q t D).flatMap natWord ∧
      e.env bKey = hfold B key0 (digs q t D) ∧ SameN a e ∧ Cst e ∧ Fr a e digT) := by
  have hqpos : 0 < q := by omega
  have hdl : ∀ x ∈ digs q t D, x < B := by
    intro x hx; unfold digs at hx; simp only [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx; exact lt_of_lt_of_le (Nat.mod_lt _ hqpos) hqB
  let I : ℕ → DS VV MM → Prop := fun i e => e.env bPw = q ^ (D - i) ∧ e.env bKey = hfold B key0 ((digs q t D).take i) ∧
    e.kin = a.kin ++ ((digs q t D).take i).flatMap natWord ∧ SameN a e ∧ Cst e ∧ Fr a e digT
  refine Hs.mono (forS_spec' (C := C) bI kD (by decide) digB a D hDW I (40 * Λ + 60)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i2, i3, i4.trans (SameN.set _ _ _),
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i5.z, by rw [DS.set_env_ne _ _ (by decide)]; exact i5.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact i5.two⟩, Fr.trans i6 (Fr.set e v (by decide))⟩)
    ⟨by rw [hP]; simp, by rw [hK]; simp [hfold], by simp, SameN.refl _, hc, Fr.refl _ _⟩ hD ?_) le_rfl ?_
  · intro i hi e ⟨i1, i2, i3, i4, i5, i6⟩ hei hem
    have eQ : e.env lQ = q := by rw [i6 lQ (by decide)]; exact hQ
    have eT : e.env lT = t := by rw [i6 lT (by decide)]; exact hT
    have eB : e.env kB2 = B := by rw [i6 kB2 (by decide)]; exact hB
    have hpw : q ^ (D - i) = q ^ (D - 1 - i) * q := by rw [← pow_succ]; congr 1; omega
    have hpwle : q ^ (D - i) ≤ q ^ D := Nat.pow_le_pow_right hqpos (by omega)
    have hpw1 : 0 < q ^ (D - 1 - i) := Nat.pow_pos hqpos
    have hq1 : q ≤ q ^ D := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ D := Nat.pow_le_pow_right hqpos (by omega)
    set dg := t / q ^ (D - 1 - i) % q with hdg
    have hdgq : dg < q := Nat.mod_lt _ hqpos
    have htk := digs_take q t D i hi
    rw [← hdg] at htk
    have hlt := foldl_lt B ((digs q t D).take (i + 1)) key0 (fun x hx => hdl x (List.mem_of_mem_take hx))
    have hlen : ((digs q t D).take (i + 1)).length = i + 1 := by simp [digs]; omega
    rw [hlen] at hlt
    have hBi : B ^ (i + 1) ≤ B ^ D := Nat.pow_le_pow_right (by omega) (by omega)
    have hkeyW : hfold B key0 ((digs q t D).take (i + 1)) < 2 ^ C.Wd := by
      have := Nat.mul_le_mul_left (key0 + 1) hBi; omega
    rw [htk, hfold_snoc] at hkeyW
    apply Hx.hs
    refine Hs.then (hs_dm C bPw lQ bQu bJk e (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [eQ]; omega) (by rw [eQ]; omega)) (fun e1 he1 n1 hn1 => ?_); subst he1
    refine Hs.then (hs_copy C bPw bQu _ (by decide)) (fun e2 he2 n2 hn2 => ?_); subst he2
    have v2 : ((((e.set bQu (e.env bPw / e.env lQ)).set bJk (e.env bPw % e.env lQ)).set bPw
        (((e.set bQu (e.env bPw / e.env lQ)).set bJk (e.env bPw % e.env lQ)).env bQu)).env bPw) = q ^ (D - 1 - i) := by
      vsimp [i1, eQ, hpw]; exact Nat.mul_div_cancel _ hqpos
    have hpw2 : q ^ (D - 1 - i) ≤ q ^ D := Nat.pow_le_pow_right hqpos (by omega)
    refine Hs.then (hs_dm C lT bPw bQu bJk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [v2]; exact hpw1) (by rw [v2]; omega)) (fun e3 he3 n3 hn3 => ?_); subst he3
    refine Hs.then (hs_dm C bQu lQ bJk bDig _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by vsimp [eQ]; omega) (by vsimp [eQ]; omega)) (fun e4 he4 n4 hn4 => ?_)
    have hdiv : e.env bPw / q = q ^ (D - 1 - i) := by rw [i1, hpw]; exact Nat.mul_div_cancel _ hqpos
    have v4 : e4.env bDig = dg := by rw [he4, hdg]; vsimp [eQ, eT, hdiv]
    have s4 : SameN e e4 := by
      rw [he4]
      exact (SameN.set _ _ _).trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans
        ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans (SameN.set _ _ _))))))
    have c4 : Cst e4 := by rw [he4]; exact ⟨by vsimp [i5.z], by vsimp [i5.one], by vsimp [i5.two]⟩
    have hdgW : dg < 2 ^ C.Wd := by omega
    have hkin4 : e4.kin.length + (natWord dg).length ≤ C.Lk := by
      have e4k : e4.kin = e.kin := by rw [he4]; rfl
      have h1 : ((digs q t D).take (i + 1)).flatMap natWord ++ ((digs q t D).drop (i + 1)).flatMap natWord =
          (digs q t D).flatMap natWord := by rw [← List.flatMap_append, List.take_append_drop]
      have h2 := congrArg List.length h1
      rw [htk, List.flatMap_append, List.length_append, List.length_append] at h2
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h2
      rw [e4k, i3, List.length_append]
      omega
    refine Hs.then (emV_spec C bDig (by decide) e4 c4 hW dg v4 hdgW hkin4) (fun e5 ⟨k5, s5, c5, f5⟩ n5 hn5 => ?_)
    have e5K : e5.env bKey = hfold B key0 ((digs q t D).take i) := by
      rw [f5 bKey (by decide), he4]; vsimp [i2]
    have e5B : e5.env kB2 = B := by rw [f5 kB2 (by decide), he4]; vsimp [eB]
    have e5D : e5.env bDig = dg := by rw [f5 bDig (by decide)]; exact v4
    refine Hs.then (hs_mul C bKey kB2 bTmp e5 (by decide) (by decide) (by decide) (by rw [e5K, e5B]; omega))
      (fun e6 he6 n6 hn6 => ?_); subst he6
    refine Hs.then (hs_copy C bKey bTmp _ (by decide)) (fun e7 he7 n7 hn7 => ?_); subst he7
    refine Hs.last (hs_add C bKey bDig _ (by decide) (by vsimp [e5K, e5B, e5D]; omega)) (fun e8 he8 n8 hn8 => ?_)
    subst he8
    have fr4 : Fr e e4 digT := by
      rw [he4]
      exact Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.set _ _ (by decide)))))))
    have hfr : Fr e e5 digT := Fr.trans fr4 (Fr.weaken f5 (by decide))
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide),
        f5 bPw (by decide), he4, show D - (i + 1) = D - 1 - i by omega]
      vsimp [eQ, hdiv]
    · rw [htk, hfold_snoc]; vsimp [e5K, e5B, e5D]
    · rw [htk]; simp only [DS.set]; rw [k5, he4]; simp [i3, List.flatMap_append]
    · exact i4.trans (s4.trans (s5.trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans (SameN.set _ _ _)))))
    · exact ⟨by vsimp [c5.z], by vsimp [c5.one], by vsimp [c5.two]⟩
    · exact Fr.trans i6 (Fr.trans hfr (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.set _ _ (by decide)))))
    · vsimp [f5 bI (by decide), he4, hei]
    · vsimp [f5 kD (by decide), he4, hem]
    · have hnb : natBitLength dg ≤ natBitLength q := by
        unfold natBitLength
        have := Nat.log_mono_right (b := 2) (le_of_lt hdgq)
        omega
      omega
  · rintro e ⟨⟨i1, i2, i3, i4, i5, i6⟩, _, _⟩
    have : (digs q t D).take D = digs q t D := List.take_of_length_le (by simp [digs])
    rw [this] at i2 i3
    exact ⟨i3, i2, i4, i5, i6⟩

end NearCubicGates.Close.CounterMachine.CellTablesProg
