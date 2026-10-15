import Proof.Gates.Expand.PolyTabHead5

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def l3 : List (Fin 64) := [20, 21, 53, 55]
def l4 : List (Fin 64) := [26, 44, 45]
def constL : List (Fin 64) := w1List ++ wcList ++ l3 ++ l4

def phD1 : WX :=
  .seq (initZ 42 w1List) <| .seq (initZ 44 wcList) <| .seq (initZ 42 l3) <| .seq (initZ 44 l4) <|
  .seq (incZ 21 20 2) <| .seq (incZ 53 20 2) <| .seq (incZ 55 20 1) <| .seq (incZ 45 44 2) <| .seq (incZ 26 44 1) <|
  .seq (addR (rX 42) (rX 31) (rX 7)) (powZ 31)

structure D1End (Wb Wc : ℕ) (τ : WSt) : Prop where
  w1 : ∀ i ∈ w1List, NumOn τ (sZ i) Wb 0
  wc : ∀ i ∈ wcList, NumOn τ (sZ i) Wc 0
  c20 : NumOn τ (sZ 20) Wb 0
  c21 : NumOn τ (sZ 21) Wb 2
  c53 : NumOn τ (sZ 53) Wb 2
  c55 : NumOn τ (sZ 55) Wb 1
  c26 : NumOn τ (sZ 26) Wc (2 ^ Wb)
  c44 : NumOn τ (sZ 44) Wc 0
  c45 : NumOn τ (sZ 45) Wc 2

def phD1Cost (Wb Wc : ℕ) : ℕ :=
  w1List.length * (initCost Wb + 1) + 1 + (wcList.length * (initCost Wc + 1) + 1 + (4 * (initCost Wb + 1) + 1 +
    (3 * (initCost Wc + 1) + 1 + (2 * (41 * Wb + 8) + 1 + (2 * (41 * Wb + 8) + 1 + (1 * (41 * Wb + 8) + 1 +
    (2 * (41 * Wc + 8) + 1 + (1 * (41 * Wc + 8) + 1 + ((18 * Wb + 3) + 1 + (Wb * (41 * Wc + 8 + 4) + 1))))))))))

theorem sZ_nm (i : Fin 64) (l : List (Fin 64)) (h : i ∉ l) : sZ (te := te) (qa := qa) i ∉ l.map sZ := fun hm => by
  obtain ⟨j, hj, e⟩ := List.mem_map.mp hm; exact h (by rw [← sZ.injective e]; exact hj)

theorem phD1_spec (cap Wb Wc : ℕ) (hWb : 2 ≤ Wb) (hWc : Wb ≤ Wc) (hcap : 2 * Wc + 2 ≤ cap) (τ : WSt)
    (hb : ∀ i ∈ constL, τ.st (sZ i) = [] ∧ τ.sh (sZ i) = 0) (h42 : τ.val (rX 42) = Wb) (h44 : τ.val (rX 44) = Wc)
    (h51 : τ.val (rX 51) = 0) (h3 : τ.val (rX 3) = 0) (h4 : τ.val (rX 4) = 0) (h7 : τ.val (rX 7) = 0)
    (h31 : τ.val (rX 31) = 0) :
    Runs cap phD1 τ (phD1Cost Wb Wc) (fun ρ => D1End Wb Wc ρ ∧ ρ.val (rX 31) = 0 ∧
      SameExcept τ ρ (constL.map sZ) [rX 31]) := by
  have p2 : 4 ≤ 2 ^ Wb := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Wb := Nat.pow_le_pow_right (by norm_num) hWb
  have p2c : 4 ≤ 2 ^ Wc := le_trans p2 (Nat.pow_le_pow_right (by norm_num) hWc)
  have hb' : ∀ (l : List (Fin 64)), (∀ i ∈ l, i ∈ constL) → ∀ (σ : WSt), SameExcept τ σ (List.map sZ (constL.filter
      (fun j => j ∉ l))) [] → ∀ i ∈ l, σ.st (sZ i) = [] ∧ σ.sh (sZ i) = 0 := fun l hl σ hσ i hi => by
    have hn : sZ (te := te) (qa := qa) i ∉ List.map sZ (constL.filter (fun j => j ∉ l)) := fun hm => by
      obtain ⟨j, hj, e⟩ := List.mem_map.mp hm
      have := sZ.injective e; subst this
      simp at hj; exact hj.2 hi
    rw [hσ.st hn, hσ.sh hn]; exact hb i (hl i hi)
  -- (1) the w1 words
  obtain ⟨τ1, e1, n1, s1⟩ := initZ_spec cap 42 (by decide) Wb (by omega) w1List τ (by decide)
    (fun i hi => hb i (by simp [constL, hi])) h42 h51
  -- (2) the wc words
  have hb1 : ∀ i ∈ wcList ++ l3 ++ l4, τ1.st (sZ i) = [] ∧ τ1.sh (sZ i) = 0 := fun i hi => by
    have hn : i ∉ w1List := by revert i; decide
    rw [s1.st (sZ_nm i _ hn), s1.sh (sZ_nm i _ hn)]
    exact hb i (by simp only [constL, List.mem_append] at hi ⊢; tauto)
  obtain ⟨τ2, e2, n2, s2⟩ := initZ_spec cap 44 (by decide) Wc (by omega) wcList τ1 (by decide)
    (fun i hi => hb1 i (by simp [hi])) (by rw [s1.val (by simp), h44]) (by rw [s1.val (by simp), h51])
  have hb2 : ∀ i ∈ l3 ++ l4, τ2.st (sZ i) = [] ∧ τ2.sh (sZ i) = 0 := fun i hi => by
    have hn : i ∉ wcList := by revert i; decide
    rw [s2.st (sZ_nm i _ hn), s2.sh (sZ_nm i _ hn)]
    exact hb1 i (by simp only [List.mem_append] at hi ⊢; tauto)
  obtain ⟨τ3, e3, n3, s3⟩ := initZ_spec cap 42 (by decide) Wb (by omega) l3 τ2 (by decide)
    (fun i hi => hb2 i (by simp [hi])) (by rw [s2.val (by simp), s1.val (by simp), h42])
    (by rw [s2.val (by simp), s1.val (by simp), h51])
  have hb3 : ∀ i ∈ l4, τ3.st (sZ i) = [] ∧ τ3.sh (sZ i) = 0 := fun i hi => by
    have hn : i ∉ l3 := by revert i; decide
    rw [s3.st (sZ_nm i _ hn), s3.sh (sZ_nm i _ hn)]
    exact hb2 i (by simp [hi])
  obtain ⟨τ4, e4, n4, s4⟩ := initZ_spec cap 44 (by decide) Wc (by omega) l4 τ3 (by decide)
    hb3 (by rw [s3.val (by simp), s2.val (by simp), s1.val (by simp), h44])
    (by rw [s3.val (by simp), s2.val (by simp), s1.val (by simp), h51])
  have v4 : ∀ q, τ4.val q = τ.val q := fun q => by
    rw [s4.val (by simp), s3.val (by simp), s2.val (by simp), s1.val (by simp)]
  -- numbers after the four inits
  have N20 : NumOn τ4 (sZ 20) Wb 0 := s4.numOn (sZ_nm 20 _ (by decide)) (n3 20 (by decide))
  have N21 : NumOn τ4 (sZ 21) Wb 0 := s4.numOn (sZ_nm 21 _ (by decide)) (n3 21 (by decide))
  have N53 : NumOn τ4 (sZ 53) Wb 0 := s4.numOn (sZ_nm 53 _ (by decide)) (n3 53 (by decide))
  have N55 : NumOn τ4 (sZ 55) Wb 0 := s4.numOn (sZ_nm 55 _ (by decide)) (n3 55 (by decide))
  -- (5) the increments
  have N44 : NumOn τ4 (sZ 44) Wc 0 := n4 44 (by decide)
  have N45 : NumOn τ4 (sZ 45) Wc 0 := n4 45 (by decide)
  have N26 : NumOn τ4 (sZ 26) Wc 0 := n4 26 (by decide)
  have z3 : ∀ σ : WSt, (∀ q, σ.val q = τ.val q) → σ.val (rX 3) = 0 := fun σ h => by rw [h, h3]
  have z4 : ∀ σ : WSt, (∀ q, σ.val q = τ.val q) → σ.val (rX 4) = 0 := fun σ h => by rw [h, h4]
  have e5 := incZ_spec cap Wb 21 20 (by decide) (by omega) 2 0 0 τ4 N21 N20 (z3 _ v4) (z4 _ v4) (by omega)
  simp only [show (2 : ℕ) ≠ 0 by decide, if_false, Nat.zero_add] at e5
  have ne : ∀ i j : Fin 64, i ≠ j → sZ (te := te) (qa := qa) i ≠ sZ j := fun i j h e => h (sZ.injective e)
  have v5 : ∀ q, (τ4.sets (sZ 21) (frame (binary Wb 2))).val q = τ.val q := fun q => by simp [v4]
  have e6 := incZ_spec cap Wb 53 20 (by decide) (by omega) 2 0 0 _ (BinW.numOn_sets_ne N53 (ne 53 21 (by decide)) _)
    (BinW.numOn_sets_ne N20 (ne 20 21 (by decide)) _) (z3 _ v5) (z4 _ v5) (by omega)
  simp only [show (2 : ℕ) ≠ 0 by decide, if_false, Nat.zero_add] at e6
  have v6 : ∀ q, ((τ4.sets (sZ 21) (frame (binary Wb 2))).sets (sZ 53) (frame (binary Wb 2))).val q = τ.val q :=
    fun q => by simp [v4]
  have e7 := incZ_spec cap Wb 55 20 (by decide) (by omega) 1 0 0 _
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne N55 (ne 55 21 (by decide)) _) (ne 55 53 (by decide)) _)
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne N20 (ne 20 21 (by decide)) _) (ne 20 53 (by decide)) _) (z3 _ v6) (z4 _ v6)
    (by omega)
  simp only [show (1 : ℕ) ≠ 0 by decide, if_false, Nat.zero_add] at e7
  set τ7 := ((τ4.sets (sZ 21) (frame (binary Wb 2))).sets (sZ 53) (frame (binary Wb 2))).sets (sZ 55)
    (frame (binary Wb 1)) with hτ7
  have v7 : ∀ q, τ7.val q = τ.val q := fun q => by simp [hτ7, v4]
  have up7 : ∀ {i : Fin 64} {W v : ℕ}, i ∉ [21, 53, 55] → NumOn τ4 (sZ i) W v → NumOn τ7 (sZ i) W v := by
    intro i W v hi h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    exact BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne h (ne _ _ hi.1) _) (ne _ _ hi.2.1) _) (ne _ _ hi.2.2) _
  have e8 := incZ_spec cap Wc 45 44 (by decide) (by omega) 2 0 0 τ7 (up7 (by decide) N45) (up7 (by decide) N44)
    (z3 _ v7) (z4 _ v7) (by omega)
  simp only [show (2 : ℕ) ≠ 0 by decide, if_false, Nat.zero_add] at e8
  have v8 : ∀ q, (τ7.sets (sZ 45) (frame (binary Wc 2))).val q = τ.val q := fun q => by simp [v7]
  have e9 := incZ_spec cap Wc 26 44 (by decide) (by omega) 1 0 0 _
    (BinW.numOn_sets_ne (up7 (by decide) N26) (ne 26 45 (by decide)) _) (BinW.numOn_sets_ne (up7 (by decide) N44) (ne 44 45 (by decide)) _)
    (z3 _ v8) (z4 _ v8) (by omega)
  simp only [show (1 : ℕ) ≠ 0 by decide, if_false, Nat.zero_add] at e9
  set τ9 := (τ7.sets (sZ 45) (frame (binary Wc 2))).sets (sZ 26) (frame (binary Wc 1)) with hτ9
  have v9 : ∀ q, τ9.val q = τ.val q := fun q => by simp [hτ9, v7]
  -- (10) the counter, (11) the doublings
  have e10 := addR_spec cap (A := rX 42) (B := rX 31) (T := rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe) τ9 (by rw [v9, h7])
    (by rw [v9, v9, h31, h42]; omega)
  rw [v9, v9, h31, h42, Nat.zero_add] at e10
  have N26' : NumOn (τ9.setv (rX 31) Wb) (sZ 26) Wc 1 :=
    BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ (by
      simp [hτ7, Function.update_of_ne (ne 26 45 (by decide)), Function.update_of_ne (ne 26 55 (by decide)),
        Function.update_of_ne (ne 26 53 (by decide)), Function.update_of_ne (ne 26 21 (by decide)), N26.2])) _ _
  have N44' : NumOn (τ9.setv (rX 31) Wb) (sZ 44) Wc 0 :=
    BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne (up7 (by decide) N44) (ne 44 45 (by decide)) _) (ne 44 26 (by decide)) _) _ _
  obtain ⟨τ11, e11, n11, z11, s11⟩ := powZ_spec cap Wc 31 (by decide) (by omega) Wb 1 0 (τ9.setv (rX 31) Wb) N26' N44'
    (by simp [Function.update_of_ne (show rX 3 ≠ rX 31 by polyTabNe), v9, h3])
    (by simp [Function.update_of_ne (show rX 4 ≠ rX 31 by polyTabNe), v9, h4]) (by simp) (by omega)
  rw [mul_one] at n11
  -- the end state
  have nm9 : ∀ {i : Fin 64} {W v : ℕ}, i ∉ [21, 53, 55, 45, 26] → NumOn τ4 (sZ i) W v → NumOn τ11 (sZ i) W v := by
    intro i W v hi h
    have hi' : i ∉ [21, 53, 55] := by simp at hi ⊢; omega
    have h7' := up7 hi' h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    have h9 : NumOn (τ9.setv (rX 31) Wb) (sZ i) W v :=
      BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne h7' (ne _ _ hi.2.2.2.1) _) (ne _ _ hi.2.2.2.2) _) _ _
    exact s11.numOn (nm1 (ne _ _ hi.2.2.2.2)) h9
  have nmS : ∀ {i : Fin 64} {W v : ℕ}, i ∈ [21, 53, 55, 45] → NumOn τ9 (sZ i) W v → NumOn τ11 (sZ i) W v := by
    intro i W v hi h
    have : i ≠ 26 := by simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> decide
    exact s11.numOn (nm1 (ne _ _ this)) (BinW.numOn_setv h _ _)
  have dw1 : ∀ i ∈ w1List, i ∉ wcList ∧ i ∉ l3 ∧ i ∉ l4 ∧ i ∉ ([21, 53, 55, 45, 26] : List (Fin 64)) := by decide
  have dwc : ∀ i ∈ wcList, i ∉ l3 ∧ i ∉ l4 ∧ i ∉ ([21, 53, 55, 45, 26] : List (Fin 64)) := by decide
  have w1' : ∀ i ∈ w1List, NumOn τ4 (sZ i) Wb 0 := fun i hi => by
    obtain ⟨hn2, hn3, hn4, -⟩ := dw1 i hi
    exact s4.numOn (sZ_nm i _ hn4) (s3.numOn (sZ_nm i _ hn3) (s2.numOn (sZ_nm i _ hn2) (n1 i hi)))
  have wc' : ∀ i ∈ wcList, NumOn τ4 (sZ i) Wc 0 := fun i hi => by
    obtain ⟨hn3, hn4, -⟩ := dwc i hi
    exact s4.numOn (sZ_nm i _ hn4) (s3.numOn (sZ_nm i _ hn3) (n2 i hi))
  refine ⟨τ11, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 e11))))))))) |>.mono (by unfold phD1Cost l3 l4; simp only [List.length_cons, List.length_nil]; omega),
    ⟨fun i hi => nm9 (dw1 i hi).2.2.2 (w1' i hi), fun i hi => nm9 (dwc i hi).2.2 (wc' i hi),
      nm9 (by decide) N20, nmS (by decide) ?_, nmS (by decide) ?_, nmS (by decide) ?_, n11,
      nm9 (by decide) N44, nmS (by decide) ?_⟩, z11, ?_⟩
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by simp [N21.2]))
      (ne 21 53 (by decide)) _) (ne 21 55 (by decide)) _) (ne 21 45 (by decide)) _) (ne 21 26 (by decide)) _
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by
      simp [Function.update_of_ne (ne 53 21 (by decide)), N53.2])) (ne 53 55 (by decide)) _) (ne 53 45 (by decide)) _)
      (ne 53 26 (by decide)) _
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by
      simp [Function.update_of_ne (ne 55 21 (by decide)), Function.update_of_ne (ne 55 53 (by decide)), N55.2]))
      (ne 55 45 (by decide)) _) (ne 55 26 (by decide)) _
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by
      simp [hτ7, Function.update_of_ne (ne 45 21 (by decide)), Function.update_of_ne (ne 45 53 (by decide)),
        Function.update_of_ne (ne 45 55 (by decide)), N45.2])) (ne 45 26 (by decide)) _
  · have mC : ∀ i : Fin 64, i ∈ constL → sZ (te := te) (qa := qa) i ∈ constL.map sZ := fun i hi => List.mem_map_of_mem hi
    have wk : ∀ (l : List (Fin 64)), (∀ i ∈ l, i ∈ constL) → ∀ σ σ' : WSt, SameExcept σ σ' (l.map sZ) [] →
        SameExcept σ σ' (constL.map sZ) [rX 31] := fun l hl σ σ' h => h.weaken (fun x hx => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact mC i (hl i hi)) (fun q hq => by simp at hq)
    have ss : ∀ (i : Fin 64), i ∈ constL → ∀ (σ : WSt) (l : List Bool),
        SameExcept σ (σ.sets (sZ i) l) (constL.map sZ) [rX 31] := fun i hi σ l => sameExcept_sets σ (mC i hi) l
    have t5 := ss 21 (by decide) τ4 (frame (binary Wb 2))
    have t6 := ss 53 (by decide) (τ4.sets (sZ 21) (frame (binary Wb 2))) (frame (binary Wb 2))
    have t7 := ss 55 (by decide) ((τ4.sets (sZ 21) (frame (binary Wb 2))).sets (sZ 53) (frame (binary Wb 2)))
      (frame (binary Wb 1))
    have t8 := ss 45 (by decide) τ7 (frame (binary Wc 2))
    have t9 := ss 26 (by decide) (τ7.sets (sZ 45) (frame (binary Wc 2))) (frame (binary Wc 1))
    have t10 : SameExcept τ9 (τ9.setv (rX 31) Wb) (constL.map sZ) [rX 31] :=
      sameExcept_setv _ (List.mem_singleton_self _) _
    refine (wk _ (by decide) _ _ s1).trans <| (wk _ (by decide) _ _ s2).trans <| (wk _ (by decide) _ _ s3).trans <|
      (wk _ (by decide) _ _ s4).trans <| t5.trans <| t6.trans <| t7.trans <| t8.trans <| t9.trans <| t10.trans ?_
    exact s11.weaken (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact mC 26 (by decide))
      (fun q hq => hq)

end NearCubicGates.Close.Expand.PolyTab

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def phD2 : WX :=
  .seq (addR (rX 12) (rY 13) (rX 7)) <| .seq (addR (rX 45) (rY 32) (rX 7)) <| .seq (addR (rX 45) (rY 41) (rX 7)) <|
  .seq (addR (rX 45) (rY 66) (rX 7)) <| .seq (addR (rX 11) (rY 84) (rX 7)) <| .seq (addR (rX 12) (rY 89) (rX 7)) <|
  .seq (addR (rX 41) (rY 106) (rX 7)) <| .seq (addR (rX 12) (rX 36) (rX 7)) (halfL (rX 36))

def phD2Cost (s k Wd : ℕ) : ℕ :=
  (18 * s + 3) + 1 + ((18 * (s + 1) + 3) + 1 + ((18 * (s + 1) + 3) + 1 + ((18 * (s + 1) + 3) + 1 + ((18 * k + 3) + 1 +
    ((18 * s + 3) + 1 + ((18 * Wd + 3) + 1 + ((18 * s + 3) + 1 + (s * (8 + 4) + 1))))))))

def RD2 : List (Fin NRk) := [rY 13, rY 32, rY 41, rY 66, rY 84, rY 89, rY 106, rY 105, rY 107, rX 36]

theorem phD2_spec (cap s k Wd : ℕ) (τ : WSt) (h12 : τ.val (rX 12) = s) (h45 : τ.val (rX 45) = s + 1)
    (h11 : τ.val (rX 11) = k) (h41 : τ.val (rX 41) = Wd) (h7 : τ.val (rX 7) = 0) (h36 : τ.val (rX 36) = 0)
    (hy : ∀ j : Fin 112, j.val ∈ [13, 32, 41, 66, 84, 89, 106, 105, 107] → τ.val (rY j) = 0)
    (hcap : 2 * s + k + Wd + 10 ≤ cap) :
    Runs cap phD2 τ (phD2Cost s k Wd) (fun ρ => (∀ x, ρ.st x = τ.st x ∧ ρ.sh x = τ.sh x) ∧ ρ.cell = τ.cell ∧
      (∀ q, q ∉ (RD2 : List (Fin NRk)) → ρ.val q = τ.val q) ∧ ρ.val (rY 13) = s ∧ ρ.val (rY 32) = s + 1 ∧
      ρ.val (rY 41) = s + 1 ∧ ρ.val (rY 66) = s + 1 ∧ ρ.val (rY 84) = k ∧ ρ.val (rY 89) = s ∧
      ρ.val (rY 106) = Wd ∧ ρ.val (rY 105) = (s + 1) / 2 ∧ ρ.val (rY 107) = (decide (s % 2 = 1)).toNat ∧
      ρ.val (rX 36) = 0) := by
  have r0 : RS τ τ.val τ := ⟨fun _ => rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩
  have y0 : ∀ j : Fin 112, j.val ∈ [13, 32, 41, 66, 84, 89, 106, 105, 107] → τ.val (rY j) = 0 := hy
  obtain ⟨τ1, e1, m1⟩ := rs_add cap r0 (rX 12) (rY 13) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe) h7
    (by rw [y0 13 (by decide), h12]; omega)
  obtain ⟨τ2, e2, m2⟩ := rs_add cap m1 (rX 45) (rY 32) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 32 (by decide), h45]; omega)
  obtain ⟨τ3, e3, m3⟩ := rs_add cap m2 (rX 45) (rY 41) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 41 (by decide), h45]; omega)
  obtain ⟨τ4, e4, m4⟩ := rs_add cap m3 (rX 45) (rY 66) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 66 (by decide), h45]; omega)
  obtain ⟨τ5, e5, m5⟩ := rs_add cap m4 (rX 11) (rY 84) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 84 (by decide), h11]; omega)
  obtain ⟨τ6, e6, m6⟩ := rs_add cap m5 (rX 12) (rY 89) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 89 (by decide), h12]; omega)
  obtain ⟨τ7, e7, m7⟩ := rs_add cap m6 (rX 41) (rY 106) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 106 (by decide), h41]; omega)
  obtain ⟨τ8, e8, m8⟩ := rs_add cap m7 (rX 12) (rX 36) (rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h7]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h36, h12]; omega)
  obtain ⟨τ9, e9, m9⟩ := halfL_spec cap (rX 36) (by polyTabNe) (by polyTabNe) _ τ8 m8 s
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, h36, h12]) (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 107 (by decide)])
    (by simp [Function.update_apply, Fin.ext_iff, rX_val, rY_val, y0 105 (by decide)]) (by omega)
  refine ⟨τ9, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 e9)))))))).mono ?_, fun x => m9.s x, m9.c, fun q hq => ?_, ?_⟩
  · simp only [Function.update_apply, Fin.ext_iff, rX_val, rY_val, Fin.isValue, h12, h45, h11, h41, y0 13 (by decide), y0 32 (by decide), y0 41 (by decide),
      y0 66 (by decide), y0 84 (by decide), y0 89 (by decide), y0 106 (by decide)]
    unfold phD2Cost; first | omega | (simp; done) | (simp; omega)
  · simp only [RD2, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [m9.v]; simp [hG, Function.update_apply, Fin.ext_iff, rX_val, rY_val, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1,
      hq.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.2.2]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [m9.v]; simp [hG, Function.update_apply, Fin.ext_iff, rX_val, rY_val, h12, h45, h11, h41, y0 13 (by decide),
          y0 32 (by decide), y0 41 (by decide), y0 66 (by decide), y0 84 (by decide), y0 89 (by decide),
          y0 106 (by decide), h36]; done)
      | (rw [m9.v]; simp [hG, Function.update_apply, Fin.ext_iff, rX_val, rY_val, h12, h45, h11, h41, y0 13 (by decide),
          y0 32 (by decide), y0 41 (by decide), y0 66 (by decide), y0 84 (by decide), y0 89 (by decide),
          y0 106 (by decide), h36]; omega)
      | (rw [m9.v]; simp [hG, Function.update_apply, Fin.ext_iff, rX_val, rY_val]
         rcases Nat.mod_two_eq_zero_or_one s with h | h <;> simp [h])

end NearCubicGates.Close.Expand.PolyTab
