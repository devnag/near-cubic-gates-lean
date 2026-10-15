import Proof.Wire_3_5.SeedFixRows

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

/-! ## The bank (tapes 0 the power counter, 1 the column counter, 2 the power, 3 the column, 4 the table, 5 the modulus,
6 the label, 7 and 8 the product's scratch, 9 the flag cell, 10 the capacity tape, 11 and 12 rewind logs, 13 the target
word, 14 the prefix word, 15 the mask, 16 the register, 17 the bit cell, 18 the accumulator cell, 19 the rows tape,
20 the word `1`, 21 a rewind log) -/

def k22Acc : Fin 4 → Fin 22 := ![2, 20, 9, 10]

theorem install_k22Acc (A : Fin 22 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install k22Acc A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, v 2, v 3, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, v 1, A 21] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k22Acc (H : Fin 22 → ℕ) (v : Fin 4 → ℕ) :
    dockH k22Acc H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8, v 2, v 3, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, v 1, H 21] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def k22MC : Fin 4 → Fin 22 := ![15, 20, 9, 10]

theorem install_k22MC (A : Fin 22 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install k22MC A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 2, v 3, A 11, A 12, A 13, A 14, v 0, A 16, A 17, A 18, A 19, v 1, A 21] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k22MC (H : Fin 22 → ℕ) (v : Fin 4 → ℕ) :
    dockH k22MC H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 2, v 3, H 11, H 12, H 13, H 14, v 0, H 16, H 17, H 18, H 19, v 1, H 21] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def k22Tab : Fin 13 → Fin 22 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem install_k22Tab (A : Fin 22 → List Bool) (v : Fin 13 → List Bool) :
    RecoveryRootRound.install k22Tab A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 10
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 11
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 12
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k22Tab (H : Fin 22 → ℕ) (v : Fin 13 → ℕ) :
    dockH k22Tab H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_slot _ (by decide) _ _ 8
    | exact dockH_slot _ (by decide) _ _ 9
    | exact dockH_slot _ (by decide) _ _ 10
    | exact dockH_slot _ (by decide) _ _ 11
    | exact dockH_slot _ (by decide) _ _ 12
    | exact dockH_other _ _ _ _ (by decide)

def k22Rows : Fin 14 → Fin 22 := ![13, 4, 14, 15, 16, 17, 18, 19, 5, 9, 10, 11, 12, 21]

theorem install_k22Rows (A : Fin 22 → List Bool) (v : Fin 14 → List Bool) :
    RecoveryRootRound.install k22Rows A v = ![A 0, A 1, A 2, A 3, v 1, v 8, A 6, A 7, A 8, v 9, v 10, v 11, v 12, v 0, v 2, v 3, v 4, v 5, v 6, v 7, A 20, v 13] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 10
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 11
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 12
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 13
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k22Rows (H : Fin 22 → ℕ) (v : Fin 14 → ℕ) :
    dockH k22Rows H v = ![H 0, H 1, H 2, H 3, v 1, v 8, H 6, H 7, H 8, v 9, v 10, v 11, v 12, v 0, v 2, v 3, v 4, v 5, v 6, v 7, H 20, v 13] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_slot _ (by decide) _ _ 8
    | exact dockH_slot _ (by decide) _ _ 9
    | exact dockH_slot _ (by decide) _ _ 10
    | exact dockH_slot _ (by decide) _ _ 11
    | exact dockH_slot _ (by decide) _ _ 12
    | exact dockH_slot _ (by decide) _ _ 13
    | exact dockH_other _ _ _ _ (by decide)
def selTable : Fin 12 → Bool := ![true, false, false, false, true, false, false, false, false, false, false, false]
def selV : Fin 13 → Bool := ![true, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def consRowsM :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine k22Acc (MaskedReset.machine (ZipFlag.machine copyG) sel3))
    (RecoveryFocus.machine k22MC (MaskedReset.machine (ZipFlag.machine copyG) sel3)))
    (RecoveryFocus.machine k22Tab (MaskedReset.machine tableM selTable)))
    (RecoveryFocus.machine k22Rows (MaskedReset.machine rowsM selV))

/-- A masked in-place zip docked on four tapes of the 22-tape bank whose heads are at zero. -/
theorem zipStage22 (g : Bool → Bool → Bool → Bool) (slots : Fin 4 → Fin 22) (hi : Function.Injective slots)
    (H : Fin 22 → ℕ) (A : Fin 22 → List Bool) (u v : List Bool) (f : Bool) (cap : ℕ) (hl : u.length = v.length)
    (hH : ∀ j, H (slots j) = 0) (h0 : A (slots 0) = frame u) (h1 : A (slots 1) = frame v) (h2 : A (slots 2) = [f])
    (h3 : A (slots 3) = List.replicate cap false) (hcap : 2 * u.length + 2 ≤ cap) :
    Step (RecoveryFocus.machine slots (MaskedReset.machine (ZipFlag.machine g) sel3)) (2 * (2 * u.length + 2) + 2)
      H A H (RecoveryRootRound.install slots A
        ![frame (List.zipWith (g f) u v), frame v, [f], List.replicate cap false]) := by
  have hz := ZipFlag.run g u v [f] 0 hl
  rw [read_single] at hz
  have hz' : Step (ZipFlag.machine g) (2 * u.length + 2) (fun _ => 0) ![frame u, frame v, [f]]
      ![2 * u.length, 2 * u.length, 0] ![frame (List.zipWith (g f) u v), frame v, [f]] :=
    hz.congr_in (by funext i; fin_cases i <;> rfl) rfl
  have hm := maskZero hz' sel3 (by intro j hj; fin_cases j <;> first | rfl | simp [sel3] at hj) hcap
  have hm' : Step (MaskedReset.machine (ZipFlag.machine g) sel3) (2 * (2 * u.length + 2) + 2) (fun _ => 0)
      ![frame u, frame v, [f], List.replicate cap false] (fun _ => 0)
      ![frame (List.zipWith (g f) u v), frame v, [f], List.replicate cap false] := by
    refine (hm.congr_in rfl ?_).congr rfl ?_ <;> funext i <;> fin_cases i <;> rfl
  exact dockKeep hm' slots hi H A hH (by intro j; fin_cases j <;> assumption)

theorem overlay_same_len (X T R : List Bool) (h : X.length = T.length) : overlay X (T ++ R) = X ++ R := by
  unfold overlay
  rw [h, List.drop_left]

theorem tabWords_zero (p ℓ lam : ℕ) : tabWords p ℓ lam 0 = [] := rfl

theorem tabWords_eq_stream (p ℓ twoH lam : ℕ) :
    tabWords p ℓ lam twoH ++ [false] = streamOf ((colTable p ℓ twoH lam).map (binary ℓ)) := rfl

def tableCost (ℓ twoH : ℕ) : ℕ := twoH * (outerCost ℓ + 2) + 1

def consCost (ℓ twoH k plen : ℕ) : ℕ :=
  2 * (2 * ℓ + 2) + 2 + 1 + (2 * (2 * ℓ + 2) + 2) + 1 + (2 * tableCost ℓ twoH + 2) + 1 +
    (2 * (k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1) + 2)

theorem consRows_run (p ℓ twoH k lam v plen pfx a0 c0 x0 z0 mc0 cap cap2 cap3 cap4 m : ℕ) (r0 : List Bool) (b0 : Bool)
    (T out backingO : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (hr0 : r0.length ≤ 2 * ℓ + 1)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ)
    (hT : T.length = (tabWords p ℓ lam twoH).length) (hm : 1 ≤ m) :
    Step consRowsM (consCost ℓ twoH k plen)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, out.length, 0, 0]
      ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ a0), frame (binary ℓ c0),
        T ++ List.replicate m false, frame (binary ℓ p), frame (binary ℓ lam), frame (binary ℓ x0), frame (binary ℓ z0),
        [false], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame (binary k v),
        frame (binary plen pfx), frame (binary ℓ mc0), r0, [b0], [false], overlay out backingO, frame (binary ℓ 1),
        List.replicate cap4 false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        out.length + k * (2 * (twoH * ℓ - plen) + 3), 0, 0]
      ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ (accPow p ℓ lam twoH)),
        frame (binary ℓ (curG p ℓ lam c0 twoH)), tabWords p ℓ lam twoH ++ List.replicate m false, frame (binary ℓ p),
        frame (binary ℓ lam), frame (binary ℓ (xG p ℓ lam x0 twoH)), frame (binary ℓ (zG p ℓ lam z0 twoH)), [false],
        List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame (binary k v),
        frame (binary plen pfx), frame (binary ℓ ((lfsr p ℓ)^[k] 1)), recRow ℓ (colTable p ℓ twoH lam) plen r0 k,
        [bitRow (colTable p ℓ twoH lam) plen b0 k], [false],
        overlay (out ++ rowsOut (colTable p ℓ twoH lam) plen pfx v k) backingO, frame (binary ℓ 1),
        List.replicate cap4 false] := by
  set tab := colTable p ℓ twoH lam with htab
  have htl : tab.length = twoH * ℓ := colTable_length p ℓ twoH lam
  set U := List.replicate twoH true ++ [false]
  set UB := List.replicate ℓ true ++ [false]
  set FP := frame (binary ℓ p)
  set FL := frame (binary ℓ lam)
  set PR := frame (binary plen pfx)
  set ONE := frame (binary ℓ 1)
  set Cp := List.replicate cap false
  set Cp2 := List.replicate cap2 false
  set Cp3 := List.replicate cap3 false
  set Cp4 := List.replicate cap4 false
  set B := T ++ List.replicate m false
  set H0 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, out.length, 0, 0]
  -- 1: the power := 1
  have s1 := zipStage22 copyG k22Acc (by decide) H0
    ![U, UB, frame (binary ℓ a0), frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp,
      Cp2, Cp3, frame (binary k v), PR, frame (binary ℓ mc0), r0, [b0], [false], overlay out backingO, ONE, Cp4]
    (binary ℓ a0) (binary ℓ 1) false cap (by simp) (by intro j; fin_cases j <;> rfl) rfl rfl rfl rfl (by simp; omega)
  rw [zipWith_copy _ _ (by simp), binary_length, install_k22Acc] at s1
  -- 2: the mask := 1
  have s2 := zipStage22 copyG k22MC (by decide) H0
    ![U, UB, ONE, frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp,
      Cp2, Cp3, frame (binary k v), PR, frame (binary ℓ mc0), r0, [b0], [false], overlay out backingO, ONE, Cp4]
    (binary ℓ mc0) (binary ℓ 1) false cap (by simp) (by intro j; fin_cases j <;> rfl) rfl rfl rfl rfl (by simp; omega)
  rw [zipWith_copy _ _ (by simp), binary_length, install_k22MC] at s2
  -- 3: the column table, the counter and the table rewound
  have hT0 := table_run p ℓ lam twoH c0 x0 z0 cap cap2 [] B hℓ hcap hcap2 hcap2'
  have eB : overlay ([] ++ tabWords p ℓ lam 0) B = B := by rw [tabWords_zero]; simp [overlay]
  have eTab : overlay ([] ++ tabWords p ℓ lam twoH) B = tabWords p ℓ lam twoH ++ List.replicate m false := by
    rw [List.nil_append, overlay_same_len _ _ _ hT.symm]
  have hTb : Step tableM (tableCost ℓ twoH) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![U, UB, ONE, frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp, Cp2]
      ![twoH, 0, 0, 0, twoH * (ℓ * (2 * ℓ + 1)), 0, 0, 0, 0, 0, 0, 0]
      ![U, UB, frame (binary ℓ (accPow p ℓ lam twoH)), frame (binary ℓ (curG p ℓ lam c0 twoH)),
        tabWords p ℓ lam twoH ++ List.replicate m false, FP, FL, frame (binary ℓ (xG p ℓ lam x0 twoH)),
        frame (binary ℓ (zG p ℓ lam z0 twoH)), [false], Cp, Cp2] := by
    have e0 : outerH ℓ ([] : List Bool).length 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
      funext j; fin_cases j <;> simp [outerH]
    have e1 : outerH ℓ ([] : List Bool).length twoH = ![twoH, 0, 0, 0, twoH * (ℓ * (2 * ℓ + 1)), 0, 0, 0, 0, 0, 0, 0] := by
      funext j; fin_cases j <;> simp [outerH]
    unfold tableCost
    rw [e0, e1] at hT0
    unfold outerA at hT0
    rw [eB, eTab] at hT0
    exact hT0
  have hTm := hTb.mask (cap := cap3) selTable (by intro i _; fin_cases i <;> rfl)
    hcap3
  have hTm' : Step (MaskedReset.machine tableM selTable) (2 * tableCost ℓ twoH + 2) (fun _ => 0)
      ![U, UB, ONE, frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp, Cp2, Cp3]
      (fun _ => 0)
      ![U, UB, frame (binary ℓ (accPow p ℓ lam twoH)), frame (binary ℓ (curG p ℓ lam c0 twoH)),
        tabWords p ℓ lam twoH ++ List.replicate m false, FP, FL, frame (binary ℓ (xG p ℓ lam x0 twoH)),
        frame (binary ℓ (zG p ℓ lam z0 twoH)), [false], Cp, Cp2, Cp3] := by
    refine (hTm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s3 := dockKeep hTm' k22Tab (by decide) H0
    ![U, UB, ONE, frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp,
      Cp2, Cp3, frame (binary k v), PR, ONE, r0, [b0], [false], overlay out backingO, ONE, Cp4]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_k22Tab] at s3
  -- 4: the rows, the target word rewound
  set tail := List.replicate (m - 1) false
  have eS : tabWords p ℓ lam twoH ++ List.replicate m false = streamOf (tab.map (binary ℓ)) ++ tail := by
    rw [← tabWords_eq_stream, List.append_assoc]
    congr 1
    rw [show m = 1 + (m - 1) by omega, List.replicate_add]
    rfl
  set R := 2 * (twoH * ℓ - plen) + 3
  have hR0 := rows_run p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backingO hℓ hkl hr0 hcap hcap2''
    (by rw [htl]; exact hcap3') (by rw [htl]; exact hplen)
  have eh0 : rowsH tab plen out.length 0 = ![0, 0, 0, 0, 0, 0, 0, out.length, 0, 0, 0, 0, 0] := by
    funext j; fin_cases j <;> simp [rowsH]
  have ehk : rowsH tab plen out.length k = ![2 * k, 0, 0, 0, 0, 0, 0, out.length + k * R, 0, 0, 0, 0, 0] := by
    funext j; fin_cases j <;> simp [rowsH, htl, R]
  have ea0 : rowsA p ℓ k v plen pfx cap cap2 cap3 tab tail r0 b0 out backingO 0 =
      ![frame (binary k v), streamOf (tab.map (binary ℓ)) ++ tail, PR, ONE, r0, [b0], [false], overlay out backingO, FP,
        [false], Cp, Cp2, Cp3] := by
    funext j; fin_cases j <;> simp [rowsA, rowsOut, recRow, bitRow, PR, ONE, FP, Cp, Cp2, Cp3]
  rw [eh0, ehk, ea0, htl] at hR0
  unfold rowsA at hR0
  have hRm := hR0.mask (cap := cap4) selV (by intro i hi; fin_cases i <;> first | rfl | simp [selV] at hi) hcap4
  have hRm' : Step (MaskedReset.machine rowsM selV) (2 * (k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1) + 2)
      ![0, 0, 0, 0, 0, 0, 0, out.length, 0, 0, 0, 0, 0, 0]
      ![frame (binary k v), streamOf (tab.map (binary ℓ)) ++ tail, PR, ONE, r0, [b0], [false], overlay out backingO,
        FP, [false], Cp, Cp2, Cp3, Cp4]
      ![0, 0, 0, 0, 0, 0, 0, out.length + k * R, 0, 0, 0, 0, 0, 0]
      ![frame (binary k v), streamOf (tab.map (binary ℓ)) ++ tail, frame (binary plen pfx),
        frame (binary ℓ ((lfsr p ℓ)^[k] 1)), recRow ℓ tab plen r0 k, [bitRow tab plen b0 k], [false],
        overlay (out ++ rowsOut tab plen pfx v k) backingO, frame (binary ℓ p), [false], List.replicate cap false,
        List.replicate cap2 false, List.replicate cap3 false, Cp4] := by
    refine (hRm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s4 := dockRun hRm' k22Rows (by decide) H0
    ![U, UB, frame (binary ℓ (accPow p ℓ lam twoH)), frame (binary ℓ (curG p ℓ lam c0 twoH)),
      streamOf (tab.map (binary ℓ)) ++ tail, FP, FL, frame (binary ℓ (xG p ℓ lam x0 twoH)),
      frame (binary ℓ (zG p ℓ lam z0 twoH)), [false], Cp, Cp2, Cp3, frame (binary k v), PR, ONE, r0, [b0], [false],
      overlay out backingO, ONE, Cp4]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_k22Rows, install_k22Rows] at s4
  rw [eS] at s3
  have s1' := s1.congr (hout' := H0)
    (tout' := ![U, UB, ONE, frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp,
      Cp2, Cp3, frame (binary k v), PR, frame (binary ℓ mc0), r0, [b0], [false], overlay out backingO, ONE, Cp4])
    rfl (by funext j; fin_cases j <;> rfl)
  have s2' := s2.congr (hout' := H0)
    (tout' := ![U, UB, ONE, frame (binary ℓ c0), B, FP, FL, frame (binary ℓ x0), frame (binary ℓ z0), [false], Cp,
      Cp2, Cp3, frame (binary k v), PR, ONE, r0, [b0], [false], overlay out backingO, ONE, Cp4])
    rfl (by funext j; fin_cases j <;> rfl)
  have s3' := s3.congr (hout' := H0)
    (tout' := ![U, UB, frame (binary ℓ (accPow p ℓ lam twoH)), frame (binary ℓ (curG p ℓ lam c0 twoH)),
      streamOf (tab.map (binary ℓ)) ++ tail, FP, FL, frame (binary ℓ (xG p ℓ lam x0 twoH)),
      frame (binary ℓ (zG p ℓ lam z0 twoH)), [false], Cp, Cp2, Cp3, frame (binary k v), PR, ONE, r0, [b0], [false],
      overlay out backingO, ONE, Cp4])
    rfl (by funext j; fin_cases j <;> rfl)
  have hall := ((s1'.seq s2').seq s3').seq s4
  rw [eS]
  exact hall.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)

/-! ## The block's cost in the preprocessing class (polynomial: `≤ 1000·q⁴` for `ℓ, 2h, k ≤ q`) -/

theorem innerCost_eq (ℓ : ℕ) : innerCost ℓ = 12 * ℓ + 20 := by unfold innerCost lfsrCost; omega

theorem outerCost_le (ℓ q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) : outerCost ℓ ≤ 200 * q ^ 2 := by
  unfold outerCost
  rw [innerCost_eq]
  unfold mulIterCost lfsrCost
  have h1 : ℓ * ℓ ≤ q * q := Nat.mul_le_mul hl hl
  have h2 : ℓ ≤ q * q := hl.trans (Nat.le_mul_of_pos_left q hq)
  have h3 : 1 ≤ q * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [sq]
  nlinarith

theorem tableCost_le (ℓ twoH q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) (ht : twoH ≤ q) : tableCost ℓ twoH ≤ 203 * q ^ 3 := by
  unfold tableCost
  have ho := outerCost_le ℓ q hq hl
  have h1 : twoH * (outerCost ℓ + 2) ≤ q * (200 * q ^ 2 + 2) := Nat.mul_le_mul ht (by omega)
  have h2 : q * (200 * q ^ 2 + 2) + 1 ≤ 203 * q ^ 3 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have : q ≤ q ^ 3 := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
    nlinarith
  omega

theorem passesCost_le (ℓ plen n q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) (hn : n ≤ q ^ 2) (hp : plen ≤ n) :
    passesCost ℓ plen n ≤ 80 * q ^ 3 := by
  unfold passesCost phACost phBCost
  have h1 : plen * (2 * (2 * ℓ + 1) + 2 + 1 + 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + 2 + 2) ≤ q ^ 2 * (24 * q) :=
    Nat.mul_le_mul (hp.trans hn) (by omega)
  have h2 : (n - plen) * (2 * (2 * ℓ + 1) + 2 + 1 + 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + 2 + 2) ≤ q ^ 2 * (24 * q) :=
    Nat.mul_le_mul ((Nat.sub_le n plen).trans hn) (by omega)
  have h3 : q ^ 2 * (24 * q) = 24 * q ^ 3 := by ring
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  omega

theorem rowCost_le (ℓ plen n q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) (hn : n ≤ q ^ 2) (hp : plen ≤ n) :
    rowCost ℓ plen n ≤ 200 * q ^ 3 := by
  unfold rowCost
  have h1 := passesCost_le ℓ plen n q hq hl hn hp
  have h2 : lfsrCost ℓ ≤ 25 * q := lfsrCost_le ℓ q hq hl
  have h3 : q ≤ q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  omega

theorem consCost_le (ℓ twoH k plen q : ℕ) (hq : 1 ≤ q) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q)
    (hp : plen ≤ twoH * ℓ) : consCost ℓ twoH k plen ≤ 1000 * q ^ 4 := by
  unfold consCost
  have hn : twoH * ℓ ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul ht hl
  have h1 := tableCost_le ℓ twoH q hq hl ht
  have h2 := rowCost_le ℓ plen (twoH * ℓ) q hq hl hn hp
  have h3 : k * (rowCost ℓ plen (twoH * ℓ) + 2) ≤ q * (200 * q ^ 3 + 2) := Nat.mul_le_mul hk (by omega)
  have e1 : q * (200 * q ^ 3 + 2) = 200 * q ^ 4 + 2 * q := by ring
  have h4 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h5 : q ≤ q ^ 4 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h6 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  omega

/-- **The block in the preprocessing class** (any class of degree `≥ 4`). -/
theorem consRows_within {E : Envelope} {cls : BudgetClass} {q kk psi ℓ twoH k plen : ℕ} (hq : 1 ≤ q) (hl : ℓ ≤ q)
    (ht : twoH ≤ q) (hk : k ≤ q) (hp : plen ≤ twoH * ℓ) (hd : 4 ≤ classDeg E cls) :
    Within E cls 1000 q kk psi (consCost ℓ twoH k plen) :=
  Within.of_poly hq (consCost_le ℓ twoH k plen q hq hl ht hk hp) hd

end NearCubicWires.WireExponent3_5.SeedFix
