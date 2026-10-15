import Proof.Wire_3_5.CompilerMachineEmitCuts

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- Negate a one-cell tape. -/
def notM : Machine 1 2 := gateM 1 0 fun sc => !(sc 0)

theorem notStep (b : Bool) : Step notM 1 ![0] ![[b]] ![0] ![[!b]] := by
  have h := gateStep (0 : Fin 1) (fun sc => !(sc 0)) ![0] ![[b]]
  refine h.congr rfl ?_
  funext i; fin_cases i; rfl

/-- Copy the bit under tape 0's head into the cell tape 1. -/
def cpbM : Machine 2 2 := gateM 2 1 fun sc => sc 0

theorem cpbStep (T : List Bool) (h : ℕ) (c : Bool) :
    Step cpbM 1 ![h, 0] ![T, [c]] ![h, 0] ![T, [readTapeBit T h]] := by
  have e := gateStep (1 : Fin 2) (fun sc => sc 0) ![h, 0] ![T, [c]]
  refine e.congr rfl ?_
  funext i; fin_cases i <;> rfl

def cRE : Fin 1 → Fin 12 := ![0]
def cCQ : Fin 1 → Fin 12 := ![1]
def cPK : Fin 1 → Fin 12 := ![6]
def cRC : Fin 1 → Fin 12 := ![4]

theorem cRE_inj : Function.Injective cRE := by decide

theorem install_cRE (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install cRE A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_slot cRE cRE_inj A v 0
  · exact install_other cRE A v 1 (by decide)
  · exact install_other cRE A v 2 (by decide)
  · exact install_other cRE A v 3 (by decide)
  · exact install_other cRE A v 4 (by decide)
  · exact install_other cRE A v 5 (by decide)
  · exact install_other cRE A v 6 (by decide)
  · exact install_other cRE A v 7 (by decide)
  · exact install_other cRE A v 8 (by decide)
  · exact install_other cRE A v 9 (by decide)
  · exact install_other cRE A v 10 (by decide)
  · exact install_other cRE A v 11 (by decide)

theorem dockH_cRE (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH cRE H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_slot cRE cRE_inj H v 0
  · exact dockH_other cRE H v 1 (by decide)
  · exact dockH_other cRE H v 2 (by decide)
  · exact dockH_other cRE H v 3 (by decide)
  · exact dockH_other cRE H v 4 (by decide)
  · exact dockH_other cRE H v 5 (by decide)
  · exact dockH_other cRE H v 6 (by decide)
  · exact dockH_other cRE H v 7 (by decide)
  · exact dockH_other cRE H v 8 (by decide)
  · exact dockH_other cRE H v 9 (by decide)
  · exact dockH_other cRE H v 10 (by decide)
  · exact dockH_other cRE H v 11 (by decide)

theorem cCQ_inj : Function.Injective cCQ := by decide

theorem install_cCQ (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install cCQ A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other cCQ A v 0 (by decide)
  · exact install_slot cCQ cCQ_inj A v 0
  · exact install_other cCQ A v 2 (by decide)
  · exact install_other cCQ A v 3 (by decide)
  · exact install_other cCQ A v 4 (by decide)
  · exact install_other cCQ A v 5 (by decide)
  · exact install_other cCQ A v 6 (by decide)
  · exact install_other cCQ A v 7 (by decide)
  · exact install_other cCQ A v 8 (by decide)
  · exact install_other cCQ A v 9 (by decide)
  · exact install_other cCQ A v 10 (by decide)
  · exact install_other cCQ A v 11 (by decide)

theorem dockH_cCQ (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH cCQ H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other cCQ H v 0 (by decide)
  · exact dockH_slot cCQ cCQ_inj H v 0
  · exact dockH_other cCQ H v 2 (by decide)
  · exact dockH_other cCQ H v 3 (by decide)
  · exact dockH_other cCQ H v 4 (by decide)
  · exact dockH_other cCQ H v 5 (by decide)
  · exact dockH_other cCQ H v 6 (by decide)
  · exact dockH_other cCQ H v 7 (by decide)
  · exact dockH_other cCQ H v 8 (by decide)
  · exact dockH_other cCQ H v 9 (by decide)
  · exact dockH_other cCQ H v 10 (by decide)
  · exact dockH_other cCQ H v 11 (by decide)

theorem cPK_inj : Function.Injective cPK := by decide

theorem install_cPK (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install cPK A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other cPK A v 0 (by decide)
  · exact install_other cPK A v 1 (by decide)
  · exact install_other cPK A v 2 (by decide)
  · exact install_other cPK A v 3 (by decide)
  · exact install_other cPK A v 4 (by decide)
  · exact install_other cPK A v 5 (by decide)
  · exact install_slot cPK cPK_inj A v 0
  · exact install_other cPK A v 7 (by decide)
  · exact install_other cPK A v 8 (by decide)
  · exact install_other cPK A v 9 (by decide)
  · exact install_other cPK A v 10 (by decide)
  · exact install_other cPK A v 11 (by decide)

theorem dockH_cPK (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH cPK H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other cPK H v 0 (by decide)
  · exact dockH_other cPK H v 1 (by decide)
  · exact dockH_other cPK H v 2 (by decide)
  · exact dockH_other cPK H v 3 (by decide)
  · exact dockH_other cPK H v 4 (by decide)
  · exact dockH_other cPK H v 5 (by decide)
  · exact dockH_slot cPK cPK_inj H v 0
  · exact dockH_other cPK H v 7 (by decide)
  · exact dockH_other cPK H v 8 (by decide)
  · exact dockH_other cPK H v 9 (by decide)
  · exact dockH_other cPK H v 10 (by decide)
  · exact dockH_other cPK H v 11 (by decide)

theorem cRC_inj : Function.Injective cRC := by decide

theorem install_cRC (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install cRC A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other cRC A v 0 (by decide)
  · exact install_other cRC A v 1 (by decide)
  · exact install_other cRC A v 2 (by decide)
  · exact install_other cRC A v 3 (by decide)
  · exact install_slot cRC cRC_inj A v 0
  · exact install_other cRC A v 5 (by decide)
  · exact install_other cRC A v 6 (by decide)
  · exact install_other cRC A v 7 (by decide)
  · exact install_other cRC A v 8 (by decide)
  · exact install_other cRC A v 9 (by decide)
  · exact install_other cRC A v 10 (by decide)
  · exact install_other cRC A v 11 (by decide)

theorem dockH_cRC (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH cRC H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other cRC H v 0 (by decide)
  · exact dockH_other cRC H v 1 (by decide)
  · exact dockH_other cRC H v 2 (by decide)
  · exact dockH_other cRC H v 3 (by decide)
  · exact dockH_slot cRC cRC_inj H v 0
  · exact dockH_other cRC H v 5 (by decide)
  · exact dockH_other cRC H v 6 (by decide)
  · exact dockH_other cRC H v 7 (by decide)
  · exact dockH_other cRC H v 8 (by decide)
  · exact dockH_other cRC H v 9 (by decide)
  · exact dockH_other cRC H v 10 (by decide)
  · exact dockH_other cRC H v 11 (by decide)

noncomputable def cMvRE := RecoveryFocus.machine cRE moveM
noncomputable def cMvCQ := RecoveryFocus.machine cCQ moveM
noncomputable def cNotPK := RecoveryFocus.machine cPK notM
noncomputable def cMvRC := RecoveryFocus.machine cRC moveM
/-- A `1` of the size field: toggle the parity, move the coefficient cursor two cells. -/
noncomputable def thermoOneM := Composition.machine cNotPK (Composition.machine cMvRC cMvRC)
/-- One cell of the size field. -/
noncomputable def thermoBodyM :=
  Composition.machine cMvRE (Composition.machine (branchM 0 thermoOneM (idle 12)) (Composition.machine cMvRE cMvCQ))

/-- The coefficient layout's heads: the entry register, the driver, the coefficient register. -/
def coH (re cq rc : ℕ) : Fin 12 → ℕ := ![re, cq, 0, 0, rc, 0, 0, 0, 0, 0, 0, 0]

/-- The coefficient layout's tapes. -/
def coA (RE CQ RCB RPAR RC TZ PK SC NZ SV SNV LG : List Bool) : Fin 12 → List Bool :=
  ![RE, CQ, RCB, RPAR, RC, TZ, PK, SC, NZ, SV, SNV, LG]

def thermoOneCost : ℕ := 1 + 1 + (1 + 1 + 1)
def thermoCost : ℕ := 1 + 1 + ((thermoOneCost + 2) + 1 + (1 + 1 + 1))

theorem not_decide_odd (j : ℕ) : (!decide (j % 2 = 1)) = decide ((j + 1) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have : (j + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (j + 1) % 2 = 0 := by omega
    simp [h, this]

/-- **The size field's walk**: the coefficient cursor ends at `2k`, the parity cell holds `k mod 2`, the entry
register's head is on the marker behind the size field. -/
theorem thermo_loop (Q Wm k U : ℕ) (hk : k ≤ Q) (tlRE postQ RCB RPAR RC TZ SC NZ SV SNV LG : List Bool)
    (hpost : readTapeBit postQ 0 = false) :
    Step (StreamController.machine thermoBodyM 1) (Q * (thermoCost + 2) + 1)
      (coH 0 0 0) (coA (frame (entryWord Q Wm k U) ++ tlRE) (List.replicate Q true ++ postQ) RCB RPAR RC TZ [false]
        SC NZ SV SNV LG)
      (coH (2 * Q) Q (2 * k)) (coA (frame (entryWord Q Wm k U) ++ tlRE) (List.replicate Q true ++ postQ) RCB RPAR RC TZ
        [decide (k % 2 = 1)] SC NZ SV SNV LG) := by
  set RE := frame (entryWord Q Wm k U) ++ tlRE
  set CQ := List.replicate Q true ++ postQ
  obtain ⟨pkv, hpkv⟩ : ∃ f : ℕ → Bool, f = fun j => decide (min j k % 2 = 1) := ⟨_, rfl⟩
  obtain ⟨rcv, hrcv⟩ : ∃ f : ℕ → ℕ, f = fun j => 2 * min j k := ⟨_, rfl⟩
  let bH : ℕ → Fin 12 → ℕ := fun j => coH (2 * j) j (rcv j)
  let bA : ℕ → Fin 12 → List Bool := fun j => coA RE CQ RCB RPAR RC TZ [pkv j] SC NZ SV SNV LG
  have hl := onesRun thermoBodyM 1 [] postQ Q hpost bH bA (fun _ => by simp [bA, coA, CQ]) (fun _ => by simp [bH, coH])
    thermoCost (by
      intro j hj
      have m1 := dockRun (moveStep RE (2 * j)) cRE cRE_inj (bH j) (bA j) (by intro k; fin_cases k; rfl)
        (by intro k; fin_cases k; rfl)
      rw [install_cRE, dockH_cRE] at m1
      have m1' : Step cMvRE 1 (bH j) (bA j) (coH (2 * j + 1) j (rcv j)) (bA j) :=
        m1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
      have hlen : j < (entryWord Q Wm k U).length := by rw [entryWord_length Q Wm k U hk]; omega
      have hbit : readTapeBit RE (2 * j + 1) = decide (j < k) := by
        show readTapeBit (frame (entryWord Q Wm k U) ++ tlRE) (2 * j + 1) = _
        rw [read_frame_bit' _ _ j hlen, entryWord_getElem Q Wm k U j hk hlen, if_pos hj]
      have m2 := dockRun (moveStep RE (2 * j + 1)) cRE cRE_inj (coH (2 * j + 1) j (rcv (j + 1))) (bA (j + 1))
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_cRE, dockH_cRE] at m2
      have m3 := dockRun (moveStep CQ j) cCQ cCQ_inj (coH (2 * j + 1 + 1) j (rcv (j + 1))) (bA (j + 1))
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_cCQ, dockH_cCQ] at m3
      have m2' : Step cMvRE 1 (coH (2 * j + 1) j (rcv (j + 1))) (bA (j + 1))
          (coH (2 * j + 1 + 1) j (rcv (j + 1))) (bA (j + 1)) :=
        m2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
      have m3' : Step cMvCQ 1 (coH (2 * j + 1 + 1) j (rcv (j + 1))) (bA (j + 1)) (bH (j + 1)) (bA (j + 1)) := by
        refine m3.congr ?_ (by funext i; fin_cases i <;> rfl)
        funext i; fin_cases i
        · show 2 * j + 1 + 1 = 2 * (j + 1); ring
        all_goals rfl
      have tail := m2'.seq m3'
      by_cases hjk : j < k
      · have e1 : pkv (j + 1) = !pkv j := by
          rw [hpkv]; simp only [show min j k = j by omega, show min (j + 1) k = j + 1 by omega, not_decide_odd]
        have e2 : rcv (j + 1) = rcv j + 1 + 1 := by rw [hrcv]; simp only; omega
        have n1 := dockRun (notStep (pkv j)) cPK cPK_inj (coH (2 * j + 1) j (rcv j)) (bA j)
          (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
        rw [install_cPK, dockH_cPK] at n1
        have n1' : Step cNotPK 1 (coH (2 * j + 1) j (rcv j)) (bA j) (coH (2 * j + 1) j (rcv j)) (bA (j + 1)) := by
          refine n1.congr (by funext i; fin_cases i <;> rfl) ?_
          show _ = coA RE CQ RCB RPAR RC TZ [pkv (j + 1)] SC NZ SV SNV LG
          rw [e1]
          funext i; fin_cases i <;> rfl
        have r1 := dockRun (moveStep RC (rcv j)) cRC cRC_inj (coH (2 * j + 1) j (rcv j)) (bA (j + 1))
          (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
        rw [install_cRC, dockH_cRC] at r1
        have r1' : Step cMvRC 1 (coH (2 * j + 1) j (rcv j)) (bA (j + 1)) (coH (2 * j + 1) j (rcv j + 1))
            (bA (j + 1)) := r1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
        have r2 := dockRun (moveStep RC (rcv j + 1)) cRC cRC_inj (coH (2 * j + 1) j (rcv j + 1)) (bA (j + 1))
          (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
        rw [install_cRC, dockH_cRC] at r2
        have r2' : Step cMvRC 1 (coH (2 * j + 1) j (rcv j + 1)) (bA (j + 1))
            (coH (2 * j + 1) j (rcv (j + 1))) (bA (j + 1)) := by
          refine r2.congr ?_ (by funext i; fin_cases i <;> rfl)
          rw [e2]
          funext i; fin_cases i <;> rfl
        have one := n1'.seq (r1'.seq r2')
        have br := branch_true (0 : Fin 12) (idle 12) one (by
          show readTapeBit RE (2 * j + 1) = true; rw [hbit]; simp [hjk])
        exact m1'.seq (br.seq tail)
      · have e1 : pkv (j + 1) = pkv j := by
          rw [hpkv]; simp only [show min j k = k by omega, show min (j + 1) k = k by omega]
        have e2 : rcv (j + 1) = rcv j := by rw [hrcv]; simp only; omega
        have id := idleStep (coH (2 * j + 1) j (rcv j)) (bA j)
        have id' : Step (idle 12) thermoOneCost (coH (2 * j + 1) j (rcv j)) (bA j)
            (coH (2 * j + 1) j (rcv (j + 1))) (bA (j + 1)) := by
          refine (id.congr ?_ ?_).enlarge (Nat.zero_le _)
          · rw [e2]
          · show coA RE CQ RCB RPAR RC TZ [pkv j] SC NZ SV SNV LG = coA RE CQ RCB RPAR RC TZ [pkv (j + 1)] SC NZ SV SNV LG
            rw [e1]
        have br := branch_false (0 : Fin 12) thermoOneM id' (by
          show readTapeBit RE (2 * j + 1) = false; rw [hbit]; simp [hjk])
        exact m1'.seq (br.seq tail))
  have e0 : bH 0 = coH 0 0 0 := by simp [bH, hrcv]
  have a0 : bA 0 = coA RE CQ RCB RPAR RC TZ [false] SC NZ SV SNV LG := by simp [bA, hpkv]
  have eQ : bH Q = coH (2 * Q) Q (2 * k) := by simp [bH, hrcv, min_eq_right hk]
  have aQ : bA Q = coA RE CQ RCB RPAR RC TZ [decide (k % 2 = 1)] SC NZ SV SNV LG := by simp [bA, hpkv, min_eq_right hk]
  rw [e0, a0, eQ, aQ] at hl
  exact hl

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
