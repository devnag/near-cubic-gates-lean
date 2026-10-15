import Proof.Wire_3_5.PrimAsmPopLink

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec

/-- **The factor-cost bound** (`BL` bounds `2·|block| + 2`). -/
def popKc (L d c CAP BL : ℕ) : ℕ :=
  2 * BL + 3 + ((8 * L + 2) ^ d * (118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * CAP + 100 * (4 * L + 1) ^ 2) + 3)

/-- **The print-length bound.** -/
def popPW (L d Mlab : ℕ) : ℕ := (8 * L + 2) ^ d * (2 * d * (Mlab + 1) + 2) + 1

/-- **The log capacity bound** at scrub capacity `R`. -/
def popCapB (n R PW : ℕ) : ℕ := 2 * n * (4 * R + 9) + n * (2 * PW + 13) + 2 * n + 20

theorem loadCost_le (ws : List (List Bool)) : loadCost ws ≤ 2 * (fieldsWord ws).length := by
  induction ws with
  | nil => simp [loadCost, fieldsWord]
  | cons w ws ih =>
    simp only [loadCost, fieldsWord, List.flatMap_cons, List.length_append, frame_length] at ih ⊢
    omega

theorem costC_le_popKc (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) (hlen : labs.length = 4 * L)
    (BL : ℕ) (hBL : 2 * (blockC D L s sgn neg labs).length + 2 ≤ BL) :
    costC D L s sgn neg labs ≤ popKc L (3 * listBound D) (capC D L) (labSum labs) BL := by
  have hload := loadCost_le (factorFields (4 * L) (3 * listBound D) labs (cap1C L labs) 0 (dataC D L s sgn neg))
  have hbw : (fieldsWord (factorFields (4 * L) (3 * listBound D) labs (cap1C L labs) 0 (dataC D L s sgn neg))).length =
      (blockC D L s sgn neg labs).length := rfl
  have hlab : labCost (4 * L) labs = labSum labs := by rw [← hlen]; exact FiltRec.labCost_eq labs
  have hst : Pop.stage35Cost D.M D.J D.W (ListEval.rowsOf D L) L + 1 + 1 = 118 * L + 10 + 50 * (capC D L + 1) ^ 3 := by
    unfold Pop.stage35Cost Pop.passCost ListEval.mainCost capC
    ring
  have hpow : (4 * L + 1) ^ (3 * listBound D) * 2 ^ (3 * listBound D) = (8 * L + 2) ^ (3 * listBound D) := by
    rw [← mul_pow]; ring_nf
  unfold costC popKc
  rw [hlab, hst, hpow]
  generalize (8 * L + 2) ^ (3 * listBound D) * (118 * L + 10 + 50 * (capC D L + 1) ^ 3 + 2 * labSum labs +
    100 * (4 * L + 1) ^ 2) = X
  omega

theorem labOf_le (labs : List ℕ) (Mlab : ℕ) (h : ∀ lab ∈ labs, lab ≤ Mlab) (i : ℕ) : Print.labOf labs i ≤ Mlab := by
  unfold Print.labOf
  rcases Nat.lt_or_ge i labs.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; exact Nat.zero_le _

theorem monoBits_length_le (B : ℕ) : ∀ (m : List ℕ), (∀ i ∈ m, i ≤ B) → (Rec.monoBits m).length ≤ m.length * (B + 1)
  | [], _ => by simp [Rec.monoBits]
  | a :: m, h => by
    have ih := monoBits_length_le B m (fun i hi => h i (List.mem_cons_of_mem a hi))
    have ha := h a List.mem_cons_self
    have e : (Rec.monoBits (a :: m)).length = a + 1 + (Rec.monoBits m).length := by
      simp [Rec.monoBits, Rec.atomCode]; omega
    have : (m.length + 1) * (B + 1) = m.length * (B + 1) + (B + 1) := by ring
    rw [e, List.length_cons]
    omega

/-- **Every printed POP factor is short**: `|polyWord (polyC …)| ≤ popPW L d Mlab`. -/
theorem polyWord_polyC_le (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) (Mlab : ℕ)
    (hlab : ∀ lab ∈ labs, lab ≤ Mlab) :
    (Rec.polyWord (polyC D L s sgn neg labs)).length ≤ popPW L (3 * listBound D) Mlab := by
  obtain ⟨d, hd⟩ : ∃ x, x = 3 * listBound D := ⟨_, rfl⟩
  rw [← hd]
  have hB : ∀ m ∈ polyC D L s sgn neg labs, (Rec.recW m).length ≤ 2 * d * (Mlab + 1) + 2 := by
    intro m hm
    unfold polyC factorPoly at hm
    rw [← hd] at hm
    obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
    have hmono := Interp.mem_monos (List.mem_filter.mp hm0).1
    rw [Rec.recW_length]
    have h1 := monoBits_length_le Mlab (m0.map (Print.labOf labs)) (fun i hi => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi; exact labOf_le labs Mlab hlab j)
    rw [List.length_map] at h1
    have h2 : m0.length * (Mlab + 1) ≤ d * (Mlab + 1) := Nat.mul_le_mul_right _ hmono.2.2
    have : 2 * d * (Mlab + 1) = 2 * (d * (Mlab + 1)) := by ring
    omega
  have hlen : (polyC D L s sgn neg labs).length ≤ (8 * L + 2) ^ d := by
    unfold polyC factorPoly
    rw [← hd, List.length_map]
    calc (Interp.interpPrint (fC D L s sgn neg) (4 * L) d).length ≤ (Interp.monos (4 * L) d).length :=
          List.length_filter_le _ _
      _ = (Interp.goods (4 * L) d).length := by rw [Interp.monos_eq_goods, List.length_map]
      _ ≤ (4 * L + 1) ^ d := Print.goods_length_le _ _
      _ ≤ (8 * L + 2) ^ d := Nat.pow_le_pow_left (by omega) _
  unfold Rec.polyWord popPW
  rw [List.length_append, List.length_singleton, List.length_flatMap]
  have hs := List.sum_le_card_nsmul ((polyC D L s sgn neg labs).map fun m => (Rec.recW m).length)
    (2 * d * (Mlab + 1) + 2) (by intro x hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx; exact hB m hm)
  simp only [List.length_map, smul_eq_mul] at hs
  have := Nat.mul_le_mul_right (2 * d * (Mlab + 1) + 2) hlen
  omega

theorem coefWord_pm (c : ℤ) (hc : c = 1 ∨ c = -1) : (Rec.coefWord c).length = 5 := by
  rcases hc with rfl | rfl <;> decide

section
variable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)

theorem statesC_coef (s : Fin (P.M + 1)) (st : ℤ × Fin (P.M + 1)) (h : st ∈ statesC P s) : st.1 = 1 ∨ st.1 = -1 := by
  unfold statesC at h
  split_ifs at h
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h; right; rfl
  · simp only [List.mem_singleton] at h; subst h; left; rfl

theorem pairsC_getD (s' : Fin (P.M + 1)) (j : ℕ) (hj : j < P.walkLen) :
    (pairsC P e L sgn labs s').getD j ([], []) =
      (polyC (visitData P e ⟨j, hj⟩) L s'.val sgn true labs, polyC (visitData P e ⟨j, hj⟩) L s'.val sgn false labs) := by
  unfold pairsC
  rw [List.getD_eq_getElem _ _ (by simp; exact hj)]
  simp

theorem popStates_okB (hlabs : 4 * L ≤ labs.length) (hlen : labs.length = 4 * L) (Mlab : ℕ)
    (hlab : ∀ lab ∈ labs, lab ≤ Mlab) (BL : ℕ)
    (hBL : ∀ (s' : Fin (P.M + 1)) (k : Fin P.walkLen) (neg : Bool),
      2 * (blockC (visitData P e k) L s'.val sgn neg labs).length + 2 ≤ BL) (s : Fin (P.M + 1)) :
    ∀ st ∈ popStates P e L sgn labs hlabs s,
      StateOk P.walkLen (popKc L (3 * PopLink.lbP P) (PopLink.capP P L) (labSum labs) BL + 1)
        (popCapB P.walkLen (popKc L (3 * PopLink.lbP P) (PopLink.capP P L) (labSum labs) BL + 1)
          (popPW L (3 * PopLink.lbP P) Mlab)) st := by
  intro st hst
  rw [popStates_eq] at hst
  obtain ⟨st0, h0, rfl⟩ := List.mem_map.mp hst
  obtain ⟨R, hR⟩ : ∃ x, x = popKc L (3 * PopLink.lbP P) (PopLink.capP P L) (labSum labs) BL + 1 := ⟨_, rfl⟩
  obtain ⟨PW, hPW⟩ : ∃ x, x = popPW L (3 * PopLink.lbP P) Mlab := ⟨_, rfl⟩
  rw [← hR, ← hPW]
  have hcost : ∀ x ∈ visitFs P e L sgn labs hlabs st0.2, x.cost + 1 ≤ R := by
    intro x hx
    obtain ⟨k, neg, rfl⟩ := mem_visitFs P e L sgn labs hlabs st0.2 x hx
    have h1 := visitSpec_cost_le (visitData P e k) L st0.2.val sgn (Nat.le_of_lt_succ st0.2.isLt) neg labs hlabs
    have h2 := costC_le_popKc (visitData P e k) L st0.2.val sgn neg labs hlen BL (hBL st0.2 k neg)
    rw [PopLink.listBound_visit, PopLink.capC_visit] at h2
    omega
  have hpw : ∀ (k : Fin P.walkLen) (neg : Bool),
      (Rec.polyWord (polyC (visitData P e k) L st0.2.val sgn neg labs)).length ≤ PW := by
    intro k neg
    have := polyWord_polyC_le (visitData P e k) L st0.2.val sgn neg labs Mlab hlab
    rw [PopLink.listBound_visit] at this
    rw [hPW]; exact this
  unfold StateOk
  dsimp only
  refine ⟨visitFs_length P e L sgn labs hlabs st0.2, hcost, ?_, ?_, ?_, ?_⟩
  · have := storeCost_le _ _ hcost
    rw [visitFs_length] at this
    unfold popCapB
    omega
  · rw [coefWord_pm _ (statesC_coef P s st0 h0)]
    unfold popCapB; omega
  · unfold popCapB; omega
  · rw [statePairs_eq]
    have hsum := sum_range_le P.walkLen (2 * PW + 13) (fun j => selPass (pairsC P e L sgn labs st0.2) j + 2) (by
      intro j hj
      unfold selPass
      rw [pairsC_getD P e L sgn labs st0.2 j hj]
      have ht := hpw ⟨j, hj⟩ true
      have hf := hpw ⟨j, hj⟩ false
      dsimp only
      omega)
    unfold popCapB
    omega

end

end NearCubicWires.WireExponent3_5.PrimAsm.PopCap
