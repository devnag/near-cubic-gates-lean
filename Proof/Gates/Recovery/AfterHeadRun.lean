import Proof.Gates.Recovery.AfterHeadPieces

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g)

section Entry

variable {n ν : ℕ} (point : BitInput n) (z : BitInput (2 ^ ν)) (post : List Bool)

theorem entry_sh0 : entry K point z post (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post := by
  simp [entry, afterBank]

theorem entry_sh1 : entry K point z post (sh K 1) = RepairOrdinary.frame (List.ofFn point) := by
  simp [entry, afterBank]

theorem entry_blank (i : Fin 32) (h0 : i ≠ 0) (h1 : i ≠ 1) : entry K point z post (sh K i) = [] := by
  simp [entry, afterBank, h0, h1]

theorem entry_blank_from : BlankFrom K 0 (entry K point z post) := by
  intro x hx
  have h32 : off K 0 = 32 := rfl
  rw [h32] at hx
  have hx0 : x ≠ sh K 0 := by intro he; rw [he, sh_val] at hx; simp at hx
  have hx1 : x ≠ sh K 1 := by intro he; rw [he, sh_val] at hx; simp at hx
  simp [entry, afterBank, hx0, hx1]

end Entry

/-- The cost coefficient of pieces 0–10. -/
noncomputable def headOneD : ℕ := 30 + 4 * (2 * (OuterM.widthDonor s.mw (g.sv s)).K + 3) + nuDonor.K + 1

/-- The arithmetic of `headOne`'s cost. -/
theorem headOne_arith (X Kw Kn n2 n4 n6 n8 n10 : ℕ) (h2 : n2 ≤ 2 * (Kw * (X + 1)) + 2)
    (h4 : n4 ≤ 2 * (Kw * (X + 1)) + 2) (h6 : n6 ≤ 2 * (Kw * (X + 1)) + 2) (h8 : n8 ≤ 2 * (Kw * (X + 1)) + 2)
    (h10 : n10 ≤ Kn * (X + 1)) :
    6 * (4 * X + 5) + (n2 + 1) + (n4 + 1) + (n6 + 1) + (n8 + 1) + (n10 + 1) ≤
      (30 + 4 * (2 * Kw + 3) + Kn + 1) * (X + 1) := by
  have e : (30 + 4 * (2 * Kw + 3) + Kn + 1) * (X + 1) = 43 * X + 43 + 8 * (Kw * (X + 1)) + Kn * (X + 1) := by ring
  rw [e]
  omega

/-- **Pieces 0–10.** -/
theorem headOne (c : Cfg) {n ν : ℕ} (point : BitInput n) (z : BitInput (2 ^ ν)) (post : List Bool) :
    ∃ cost, cost ≤ headOneD (s := s) (g := g) * (2 ^ ν + 1) ∧ ∃ A11 : Fin (T K) → List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 0 (entry K point z post))
        (start K c 11 A11) ∧
      A11 (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post ∧
      A11 (sh K 1) = RepairOrdinary.frame (List.ofFn point) ∧
      A11 (sh K 4) = RepairOrdinary.frame (List.ofFn z) ∧
      A11 (sh K 5) = List.replicate (g.width s ν) true ∧
      A11 (sh K 7) = List.replicate (g.width s ν) true ∧
      A11 (sh K 9) = List.replicate ν true ∧
      A11 (sh K 10) = List.replicate (g.width s ν) true ∧
      A11 (sh K 12) = List.replicate (g.width s ν) true ∧
      (∀ i : Fin 32, i ∈ ([2, 3, 6, 8, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 31] : List (Fin 32)) →
        A11 (sh K i) = []) ∧
      BlankFrom K 11 A11 := by
  set A0 := entry K point z post with hA0
  have hB0 : BlankFrom K 0 A0 := entry_blank_from K point z post
  obtain ⟨A1, hR0, hB1, hU0, hW0⟩ := copy_piece K 0 (by decide) le_rfl 0 4 (by decide) A0 (List.ofFn z) post
    ((entry_sh0 K point z post)) ((entry_blank K point z post 4 (by decide) (by decide))) hB0
  have hR0' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨0, by decide⟩)) (4 * (List.ofFn z).length + 4) A0 A1 := by
    rw [pieces_0]; exact hR0
  have t0 := step_call K c (k := ⟨0, by decide⟩) (l := ⟨1, by decide⟩) hR0'
    (fun q => next_plain K c 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨A2, hR1, hB2, hU1, hW1⟩ := copy_piece K 1 (by decide) le_rfl 0 25 (by decide) A1 (List.ofFn z) post
    (((hU0 0 (by decide)).trans (entry_sh0 K point z post))) (((hU0 25 (by decide)).trans (entry_blank K point z post 25 (by decide) (by decide)))) hB1
  have hR1' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨1, by decide⟩)) (4 * (List.ofFn z).length + 4) A1 A2 := by
    rw [pieces_1]; exact hR1
  have t1 := step_call K c (k := ⟨1, by decide⟩) (l := ⟨2, by decide⟩) hR1'
    (fun q => next_plain K c 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨n2, hn2, A3, hR2, hB3, hU2, hW2⟩ := width_piece K 2 (by decide) rfl 25 5 (by decide) A2 ν z
    (hW1) (((hU1 5 (by decide)).trans ((hU0 5 (by decide)).trans (entry_blank K point z post 5 (by decide) (by decide))))) hB2
  have hR2' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨2, by decide⟩)) n2 A2 A3 := by
    rw [pieces_2]; exact hR2
  have t2 := step_call K c (k := ⟨2, by decide⟩) (l := ⟨3, by decide⟩) hR2'
    (fun q => next_plain K c 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨A4, hR3, hB4, hU3, hW3⟩ := copy_piece K 3 (by decide) le_rfl 0 26 (by decide) A3 (List.ofFn z) post
    (((hU2 0 (by decide) (by decide)).trans ((hU1 0 (by decide)).trans ((hU0 0 (by decide)).trans (entry_sh0 K point z post))))) (((hU2 26 (by decide) (by decide)).trans ((hU1 26 (by decide)).trans ((hU0 26 (by decide)).trans (entry_blank K point z post 26 (by decide) (by decide)))))) hB3
  have hR3' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨3, by decide⟩)) (4 * (List.ofFn z).length + 4) A3 A4 := by
    rw [pieces_3]; exact hR3
  have t3 := step_call K c (k := ⟨3, by decide⟩) (l := ⟨4, by decide⟩) hR3'
    (fun q => next_plain K c 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨n4, hn4, A5, hR4, hB5, hU4, hW4⟩ := width_piece K 4 (by decide) rfl 26 7 (by decide) A4 ν z
    (hW3) (((hU3 7 (by decide)).trans ((hU2 7 (by decide) (by decide)).trans ((hU1 7 (by decide)).trans ((hU0 7 (by decide)).trans (entry_blank K point z post 7 (by decide) (by decide))))))) hB4
  have hR4' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨4, by decide⟩)) n4 A4 A5 := by
    rw [pieces_4]; exact hR4
  have t4 := step_call K c (k := ⟨4, by decide⟩) (l := ⟨5, by decide⟩) hR4'
    (fun q => next_plain K c 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨A6, hR5, hB6, hU5, hW5⟩ := copy_piece K 5 (by decide) le_rfl 0 27 (by decide) A5 (List.ofFn z) post
    (((hU4 0 (by decide) (by decide)).trans ((hU3 0 (by decide)).trans ((hU2 0 (by decide) (by decide)).trans ((hU1 0 (by decide)).trans ((hU0 0 (by decide)).trans (entry_sh0 K point z post))))))) (((hU4 27 (by decide) (by decide)).trans ((hU3 27 (by decide)).trans ((hU2 27 (by decide) (by decide)).trans ((hU1 27 (by decide)).trans ((hU0 27 (by decide)).trans (entry_blank K point z post 27 (by decide) (by decide)))))))) hB5
  have hR5' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨5, by decide⟩)) (4 * (List.ofFn z).length + 4) A5 A6 := by
    rw [pieces_5]; exact hR5
  have t5 := step_call K c (k := ⟨5, by decide⟩) (l := ⟨6, by decide⟩) hR5'
    (fun q => next_plain K c 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨n6, hn6, A7, hR6, hB7, hU6, hW6⟩ := width_piece K 6 (by decide) rfl 27 10 (by decide) A6 ν z
    (hW5) (((hU5 10 (by decide)).trans ((hU4 10 (by decide) (by decide)).trans ((hU3 10 (by decide)).trans ((hU2 10 (by decide) (by decide)).trans ((hU1 10 (by decide)).trans ((hU0 10 (by decide)).trans (entry_blank K point z post 10 (by decide) (by decide))))))))) hB6
  have hR6' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨6, by decide⟩)) n6 A6 A7 := by
    rw [pieces_6]; exact hR6
  have t6 := step_call K c (k := ⟨6, by decide⟩) (l := ⟨7, by decide⟩) hR6'
    (fun q => next_plain K c 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨A8, hR7, hB8, hU7, hW7⟩ := copy_piece K 7 (by decide) le_rfl 0 28 (by decide) A7 (List.ofFn z) post
    (((hU6 0 (by decide) (by decide)).trans ((hU5 0 (by decide)).trans ((hU4 0 (by decide) (by decide)).trans ((hU3 0 (by decide)).trans ((hU2 0 (by decide) (by decide)).trans ((hU1 0 (by decide)).trans ((hU0 0 (by decide)).trans (entry_sh0 K point z post))))))))) (((hU6 28 (by decide) (by decide)).trans ((hU5 28 (by decide)).trans ((hU4 28 (by decide) (by decide)).trans ((hU3 28 (by decide)).trans ((hU2 28 (by decide) (by decide)).trans ((hU1 28 (by decide)).trans ((hU0 28 (by decide)).trans (entry_blank K point z post 28 (by decide) (by decide)))))))))) hB7
  have hR7' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨7, by decide⟩)) (4 * (List.ofFn z).length + 4) A7 A8 := by
    rw [pieces_7]; exact hR7
  have t7 := step_call K c (k := ⟨7, by decide⟩) (l := ⟨8, by decide⟩) hR7'
    (fun q => next_plain K c 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨n8, hn8, A9, hR8, hB9, hU8, hW8⟩ := width_piece K 8 (by decide) rfl 28 12 (by decide) A8 ν z
    (hW7) (((hU7 12 (by decide)).trans ((hU6 12 (by decide) (by decide)).trans ((hU5 12 (by decide)).trans ((hU4 12 (by decide) (by decide)).trans ((hU3 12 (by decide)).trans ((hU2 12 (by decide) (by decide)).trans ((hU1 12 (by decide)).trans ((hU0 12 (by decide)).trans (entry_blank K point z post 12 (by decide) (by decide))))))))))) hB8
  have hR8' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨8, by decide⟩)) n8 A8 A9 := by
    rw [pieces_8]; exact hR8
  have t8 := step_call K c (k := ⟨8, by decide⟩) (l := ⟨9, by decide⟩) hR8'
    (fun q => next_plain K c 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨A10, hR9, hB10, hU9, hW9⟩ := copy_piece K 9 (by decide) le_rfl 0 29 (by decide) A9 (List.ofFn z) post
    (((hU8 0 (by decide) (by decide)).trans ((hU7 0 (by decide)).trans ((hU6 0 (by decide) (by decide)).trans ((hU5 0 (by decide)).trans ((hU4 0 (by decide) (by decide)).trans ((hU3 0 (by decide)).trans ((hU2 0 (by decide) (by decide)).trans ((hU1 0 (by decide)).trans ((hU0 0 (by decide)).trans (entry_sh0 K point z post))))))))))) (((hU8 29 (by decide) (by decide)).trans ((hU7 29 (by decide)).trans ((hU6 29 (by decide) (by decide)).trans ((hU5 29 (by decide)).trans ((hU4 29 (by decide) (by decide)).trans ((hU3 29 (by decide)).trans ((hU2 29 (by decide) (by decide)).trans ((hU1 29 (by decide)).trans ((hU0 29 (by decide)).trans (entry_blank K point z post 29 (by decide) (by decide)))))))))))) hB9
  have hR9' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨9, by decide⟩)) (4 * (List.ofFn z).length + 4) A9 A10 := by
    rw [pieces_9]; exact hR9
  have t9 := step_call K c (k := ⟨9, by decide⟩) (l := ⟨10, by decide⟩) hR9'
    (fun q => next_plain K c 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  obtain ⟨n10, hn10, A11, hR10, hB11, hU10, hW10⟩ := nu_piece K A10 ν z
    (hW9) (((hU9 9 (by decide)).trans ((hU8 9 (by decide) (by decide)).trans ((hU7 9 (by decide)).trans ((hU6 9 (by decide) (by decide)).trans ((hU5 9 (by decide)).trans ((hU4 9 (by decide) (by decide)).trans ((hU3 9 (by decide)).trans ((hU2 9 (by decide) (by decide)).trans ((hU1 9 (by decide)).trans ((hU0 9 (by decide)).trans (entry_blank K point z post 9 (by decide) (by decide))))))))))))) hB10
  have hR10' : Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c ⟨10, by decide⟩)) n10 A10 A11 := by
    rw [pieces_10]; exact hR10
  have t10 := step_call K c (k := ⟨10, by decide⟩) (l := ⟨11, by decide⟩) hR10'
    (fun q => next_plain K c 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  have hF0 : A11 (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post := ((hU10 0 (by decide) (by decide)).trans ((hU9 0 (by decide)).trans ((hU8 0 (by decide) (by decide)).trans ((hU7 0 (by decide)).trans ((hU6 0 (by decide) (by decide)).trans ((hU5 0 (by decide)).trans ((hU4 0 (by decide) (by decide)).trans ((hU3 0 (by decide)).trans ((hU2 0 (by decide) (by decide)).trans ((hU1 0 (by decide)).trans ((hU0 0 (by decide)).trans (entry_sh0 K point z post))))))))))))
  have hF1 : A11 (sh K 1) = RepairOrdinary.frame (List.ofFn point) := ((hU10 1 (by decide) (by decide)).trans ((hU9 1 (by decide)).trans ((hU8 1 (by decide) (by decide)).trans ((hU7 1 (by decide)).trans ((hU6 1 (by decide) (by decide)).trans ((hU5 1 (by decide)).trans ((hU4 1 (by decide) (by decide)).trans ((hU3 1 (by decide)).trans ((hU2 1 (by decide) (by decide)).trans ((hU1 1 (by decide)).trans ((hU0 1 (by decide)).trans (entry_sh1 K point z post))))))))))))
  have hF4 : A11 (sh K 4) = RepairOrdinary.frame (List.ofFn z) := ((hU10 4 (by decide) (by decide)).trans ((hU9 4 (by decide)).trans ((hU8 4 (by decide) (by decide)).trans ((hU7 4 (by decide)).trans ((hU6 4 (by decide) (by decide)).trans ((hU5 4 (by decide)).trans ((hU4 4 (by decide) (by decide)).trans ((hU3 4 (by decide)).trans ((hU2 4 (by decide) (by decide)).trans ((hU1 4 (by decide)).trans hW0))))))))))
  have hF5 : A11 (sh K 5) = List.replicate (g.width s ν) true := ((hU10 5 (by decide) (by decide)).trans ((hU9 5 (by decide)).trans ((hU8 5 (by decide) (by decide)).trans ((hU7 5 (by decide)).trans ((hU6 5 (by decide) (by decide)).trans ((hU5 5 (by decide)).trans ((hU4 5 (by decide) (by decide)).trans ((hU3 5 (by decide)).trans hW2))))))))
  have hF7 : A11 (sh K 7) = List.replicate (g.width s ν) true := ((hU10 7 (by decide) (by decide)).trans ((hU9 7 (by decide)).trans ((hU8 7 (by decide) (by decide)).trans ((hU7 7 (by decide)).trans ((hU6 7 (by decide) (by decide)).trans ((hU5 7 (by decide)).trans hW4))))))
  have hF9 : A11 (sh K 9) = List.replicate ν true := hW10
  have hF10 : A11 (sh K 10) = List.replicate (g.width s ν) true := ((hU10 10 (by decide) (by decide)).trans ((hU9 10 (by decide)).trans ((hU8 10 (by decide) (by decide)).trans ((hU7 10 (by decide)).trans hW6))))
  have hF12 : A11 (sh K 12) = List.replicate (g.width s ν) true := ((hU10 12 (by decide) (by decide)).trans ((hU9 12 (by decide)).trans hW8))
  have hBl : ∀ i : Fin 32, i ∈ ([2, 3, 6, 8, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 31] : List (Fin 32)) → A11 (sh K i) = [] := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((hU10 2 (by decide) (by decide)).trans ((hU9 2 (by decide)).trans ((hU8 2 (by decide) (by decide)).trans ((hU7 2 (by decide)).trans ((hU6 2 (by decide) (by decide)).trans ((hU5 2 (by decide)).trans ((hU4 2 (by decide) (by decide)).trans ((hU3 2 (by decide)).trans ((hU2 2 (by decide) (by decide)).trans ((hU1 2 (by decide)).trans ((hU0 2 (by decide)).trans (entry_blank K point z post 2 (by decide) (by decide)))))))))))))
    · exact ((hU10 3 (by decide) (by decide)).trans ((hU9 3 (by decide)).trans ((hU8 3 (by decide) (by decide)).trans ((hU7 3 (by decide)).trans ((hU6 3 (by decide) (by decide)).trans ((hU5 3 (by decide)).trans ((hU4 3 (by decide) (by decide)).trans ((hU3 3 (by decide)).trans ((hU2 3 (by decide) (by decide)).trans ((hU1 3 (by decide)).trans ((hU0 3 (by decide)).trans (entry_blank K point z post 3 (by decide) (by decide)))))))))))))
    · exact ((hU10 6 (by decide) (by decide)).trans ((hU9 6 (by decide)).trans ((hU8 6 (by decide) (by decide)).trans ((hU7 6 (by decide)).trans ((hU6 6 (by decide) (by decide)).trans ((hU5 6 (by decide)).trans ((hU4 6 (by decide) (by decide)).trans ((hU3 6 (by decide)).trans ((hU2 6 (by decide) (by decide)).trans ((hU1 6 (by decide)).trans ((hU0 6 (by decide)).trans (entry_blank K point z post 6 (by decide) (by decide)))))))))))))
    · exact ((hU10 8 (by decide) (by decide)).trans ((hU9 8 (by decide)).trans ((hU8 8 (by decide) (by decide)).trans ((hU7 8 (by decide)).trans ((hU6 8 (by decide) (by decide)).trans ((hU5 8 (by decide)).trans ((hU4 8 (by decide) (by decide)).trans ((hU3 8 (by decide)).trans ((hU2 8 (by decide) (by decide)).trans ((hU1 8 (by decide)).trans ((hU0 8 (by decide)).trans (entry_blank K point z post 8 (by decide) (by decide)))))))))))))
    · exact ((hU10 11 (by decide) (by decide)).trans ((hU9 11 (by decide)).trans ((hU8 11 (by decide) (by decide)).trans ((hU7 11 (by decide)).trans ((hU6 11 (by decide) (by decide)).trans ((hU5 11 (by decide)).trans ((hU4 11 (by decide) (by decide)).trans ((hU3 11 (by decide)).trans ((hU2 11 (by decide) (by decide)).trans ((hU1 11 (by decide)).trans ((hU0 11 (by decide)).trans (entry_blank K point z post 11 (by decide) (by decide)))))))))))))
    · exact ((hU10 13 (by decide) (by decide)).trans ((hU9 13 (by decide)).trans ((hU8 13 (by decide) (by decide)).trans ((hU7 13 (by decide)).trans ((hU6 13 (by decide) (by decide)).trans ((hU5 13 (by decide)).trans ((hU4 13 (by decide) (by decide)).trans ((hU3 13 (by decide)).trans ((hU2 13 (by decide) (by decide)).trans ((hU1 13 (by decide)).trans ((hU0 13 (by decide)).trans (entry_blank K point z post 13 (by decide) (by decide)))))))))))))
    · exact ((hU10 14 (by decide) (by decide)).trans ((hU9 14 (by decide)).trans ((hU8 14 (by decide) (by decide)).trans ((hU7 14 (by decide)).trans ((hU6 14 (by decide) (by decide)).trans ((hU5 14 (by decide)).trans ((hU4 14 (by decide) (by decide)).trans ((hU3 14 (by decide)).trans ((hU2 14 (by decide) (by decide)).trans ((hU1 14 (by decide)).trans ((hU0 14 (by decide)).trans (entry_blank K point z post 14 (by decide) (by decide)))))))))))))
    · exact ((hU10 15 (by decide) (by decide)).trans ((hU9 15 (by decide)).trans ((hU8 15 (by decide) (by decide)).trans ((hU7 15 (by decide)).trans ((hU6 15 (by decide) (by decide)).trans ((hU5 15 (by decide)).trans ((hU4 15 (by decide) (by decide)).trans ((hU3 15 (by decide)).trans ((hU2 15 (by decide) (by decide)).trans ((hU1 15 (by decide)).trans ((hU0 15 (by decide)).trans (entry_blank K point z post 15 (by decide) (by decide)))))))))))))
    · exact ((hU10 16 (by decide) (by decide)).trans ((hU9 16 (by decide)).trans ((hU8 16 (by decide) (by decide)).trans ((hU7 16 (by decide)).trans ((hU6 16 (by decide) (by decide)).trans ((hU5 16 (by decide)).trans ((hU4 16 (by decide) (by decide)).trans ((hU3 16 (by decide)).trans ((hU2 16 (by decide) (by decide)).trans ((hU1 16 (by decide)).trans ((hU0 16 (by decide)).trans (entry_blank K point z post 16 (by decide) (by decide)))))))))))))
    · exact ((hU10 17 (by decide) (by decide)).trans ((hU9 17 (by decide)).trans ((hU8 17 (by decide) (by decide)).trans ((hU7 17 (by decide)).trans ((hU6 17 (by decide) (by decide)).trans ((hU5 17 (by decide)).trans ((hU4 17 (by decide) (by decide)).trans ((hU3 17 (by decide)).trans ((hU2 17 (by decide) (by decide)).trans ((hU1 17 (by decide)).trans ((hU0 17 (by decide)).trans (entry_blank K point z post 17 (by decide) (by decide)))))))))))))
    · exact ((hU10 18 (by decide) (by decide)).trans ((hU9 18 (by decide)).trans ((hU8 18 (by decide) (by decide)).trans ((hU7 18 (by decide)).trans ((hU6 18 (by decide) (by decide)).trans ((hU5 18 (by decide)).trans ((hU4 18 (by decide) (by decide)).trans ((hU3 18 (by decide)).trans ((hU2 18 (by decide) (by decide)).trans ((hU1 18 (by decide)).trans ((hU0 18 (by decide)).trans (entry_blank K point z post 18 (by decide) (by decide)))))))))))))
    · exact ((hU10 19 (by decide) (by decide)).trans ((hU9 19 (by decide)).trans ((hU8 19 (by decide) (by decide)).trans ((hU7 19 (by decide)).trans ((hU6 19 (by decide) (by decide)).trans ((hU5 19 (by decide)).trans ((hU4 19 (by decide) (by decide)).trans ((hU3 19 (by decide)).trans ((hU2 19 (by decide) (by decide)).trans ((hU1 19 (by decide)).trans ((hU0 19 (by decide)).trans (entry_blank K point z post 19 (by decide) (by decide)))))))))))))
    · exact ((hU10 21 (by decide) (by decide)).trans ((hU9 21 (by decide)).trans ((hU8 21 (by decide) (by decide)).trans ((hU7 21 (by decide)).trans ((hU6 21 (by decide) (by decide)).trans ((hU5 21 (by decide)).trans ((hU4 21 (by decide) (by decide)).trans ((hU3 21 (by decide)).trans ((hU2 21 (by decide) (by decide)).trans ((hU1 21 (by decide)).trans ((hU0 21 (by decide)).trans (entry_blank K point z post 21 (by decide) (by decide)))))))))))))
    · exact ((hU10 22 (by decide) (by decide)).trans ((hU9 22 (by decide)).trans ((hU8 22 (by decide) (by decide)).trans ((hU7 22 (by decide)).trans ((hU6 22 (by decide) (by decide)).trans ((hU5 22 (by decide)).trans ((hU4 22 (by decide) (by decide)).trans ((hU3 22 (by decide)).trans ((hU2 22 (by decide) (by decide)).trans ((hU1 22 (by decide)).trans ((hU0 22 (by decide)).trans (entry_blank K point z post 22 (by decide) (by decide)))))))))))))
    · exact ((hU10 23 (by decide) (by decide)).trans ((hU9 23 (by decide)).trans ((hU8 23 (by decide) (by decide)).trans ((hU7 23 (by decide)).trans ((hU6 23 (by decide) (by decide)).trans ((hU5 23 (by decide)).trans ((hU4 23 (by decide) (by decide)).trans ((hU3 23 (by decide)).trans ((hU2 23 (by decide) (by decide)).trans ((hU1 23 (by decide)).trans ((hU0 23 (by decide)).trans (entry_blank K point z post 23 (by decide) (by decide)))))))))))))
    · exact ((hU10 24 (by decide) (by decide)).trans ((hU9 24 (by decide)).trans ((hU8 24 (by decide) (by decide)).trans ((hU7 24 (by decide)).trans ((hU6 24 (by decide) (by decide)).trans ((hU5 24 (by decide)).trans ((hU4 24 (by decide) (by decide)).trans ((hU3 24 (by decide)).trans ((hU2 24 (by decide) (by decide)).trans ((hU1 24 (by decide)).trans ((hU0 24 (by decide)).trans (entry_blank K point z post 24 (by decide) (by decide)))))))))))))
    · exact ((hU10 31 (by decide) (by decide)).trans ((hU9 31 (by decide)).trans ((hU8 31 (by decide) (by decide)).trans ((hU7 31 (by decide)).trans ((hU6 31 (by decide) (by decide)).trans ((hU5 31 (by decide)).trans ((hU4 31 (by decide) (by decide)).trans ((hU3 31 (by decide)).trans ((hU2 31 (by decide) (by decide)).trans ((hU1 31 (by decide)).trans ((hU0 31 (by decide)).trans (entry_blank K point z post 31 (by decide) (by decide)))))))))))))
  have u1 := trans t0 t1
  have u2 := trans u1 t2
  have u3 := trans u2 t3
  have u4 := trans u3 t4
  have u5 := trans u4 t5
  have u6 := trans u5 t6
  have u7 := trans u6 t7
  have u8 := trans u7 t8
  have u9 := trans u8 t9
  have u10 := trans u9 t10
  refine ⟨_, ?_, A11, u10, hF0, hF1, hF4, hF5, hF7, hF9, hF10, hF12, hBl, hB11⟩
  have hl : (List.ofFn z).length = 2 ^ ν := List.length_ofFn
  rw [hl]
  rw [pow_one] at hn2 hn4 hn6 hn8
  have := headOne_arith (2 ^ ν) (OuterM.widthDonor s.mw (g.sv s)).K nuDonor.K n2 n4 n6 n8 n10 hn2 hn4 hn6 hn8 hn10
  unfold headOneD
  linarith

/-- **The head segment** (`sec:all-lengths`, the preparation and stage 1), from pieces 0–10 and `HeadTwoRuns`
(pieces 11–16). -/
theorem headRuns_of (c : Cfg) (h2 : HeadTwoRuns K c) : HeadRuns K c := by
  intro C0 E0 hSB
  obtain ⟨C2, E2, H2⟩ := h2 C0 E0 hSB
  refine ⟨headOneD (s := s) (g := g) + C2, E2 + 1, ?_⟩
  intro n point ν z post hlive
  obtain ⟨cost1, hc1, A11, t1, h0, h1, h4, h5, h7, h9, h10, h12, hbl, hB⟩ := headOne K c point z post
  obtain ⟨cost2, hc2, A', f0, f1, f2, f3, f7, f8, f9, f10, f11, f12, f13, f15, f16, f17, f18, f21, f22, f23, f24,
    f31, fbl, fyes, fno⟩ := H2 n point ν z post A11 hlive h0 h1 h4 h5 h7 h9 h10 h12 hbl hB
  have hνn : ν ≤ n := by
    have := hlive.width_le
    omega
  have hx : 2 ^ ν + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) hνn) 1
  have hp1 : 1 ≤ (2 ^ n + 1) ^ E2 := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
  have hp2 : (2 ^ n + 1) ^ E2 ≤ (2 ^ n + 1) ^ (E2 + 1) := Nat.pow_le_pow_right (Nat.le_add_left 1 _) (by omega)
  have hp3 : (2 ^ n + 1) ^ (E2 + 1) = (2 ^ n + 1) ^ E2 * (2 ^ n + 1) := pow_succ _ _
  refine ⟨cost1 + cost2, ?_, A', f0, f1, f2, f3, f7, f8, f9, f10, f11, f12, f13, f15, f16, f17, f18, f21, f22, f23,
    f24, f31, fbl, fun h => ⟨trans t1 (fyes h).1, (fyes h).2⟩, fun h => trans t1 (fno h)⟩
  have hA : cost1 ≤ headOneD (s := s) (g := g) * (2 ^ n + 1) ^ (E2 + 1) := by
    calc cost1 ≤ headOneD (s := s) (g := g) * (2 ^ ν + 1) := hc1
      _ ≤ headOneD (s := s) (g := g) * ((2 ^ n + 1) ^ E2 * (2 ^ n + 1)) := by
          apply Nat.mul_le_mul_left
          calc 2 ^ ν + 1 ≤ 2 ^ n + 1 := hx
            _ = 1 * (2 ^ n + 1) := (one_mul _).symm
            _ ≤ (2 ^ n + 1) ^ E2 * (2 ^ n + 1) := Nat.mul_le_mul_right _ hp1
      _ = headOneD (s := s) (g := g) * (2 ^ n + 1) ^ (E2 + 1) := by rw [hp3]
  have hB2 : cost2 ≤ C2 * (2 ^ n + 1) ^ (E2 + 1) := hc2.trans (Nat.mul_le_mul_left _ hp2)
  rw [Nat.add_mul]
  omega

end NearCubicGates.Close.Recovery.After
