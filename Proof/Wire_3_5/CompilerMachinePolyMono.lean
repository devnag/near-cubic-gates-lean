import Proof.Wire_3_5.CompilerMachineCosts

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The layout: 0-11 `monoM`'s tapes (0 the expression `VT`, 1 the table, 2 `Ea`, 3 `LA`, 4 `LB`, 5-7 registers,
8-10 logs, 11 the empty-mask entry), 12 `G`, 13 `O`, 14 `X`, 15 `Y`, 16 `E`, 17 `F` -/

def pNudge : Fin 1 → Fin 18 := ![0]
def pMono : Fin 12 → Fin 18 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def pIns : Fin 10 → Fin 18 := ![12, 13, 14, 15, 16, 17, 8, 9, 3, 10]

noncomputable def pNudgeD := RecoveryFocus.machine pNudge nudgeM
noncomputable def pMonoD := RecoveryFocus.machine pMono monoM
noncomputable def pInsD := RecoveryFocus.machine pIns insertAllM

/-- One monomial: step past its marker, write its masks, step past its frame, insert the masks. -/
noncomputable def monoInsM := Composition.machine (Composition.machine (Composition.machine pNudgeD pMonoD) pNudgeD) pInsD

theorem pNudge_inj : Function.Injective pNudge := by decide

theorem install_pNudge (A : Fin 18 → List Bool) (v : Fin 1 → List Bool) :
    install pNudge A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17] := by
  funext i
  fin_cases i
  · exact install_slot pNudge pNudge_inj A v 0
  · exact install_other pNudge A v 1 (by decide)
  · exact install_other pNudge A v 2 (by decide)
  · exact install_other pNudge A v 3 (by decide)
  · exact install_other pNudge A v 4 (by decide)
  · exact install_other pNudge A v 5 (by decide)
  · exact install_other pNudge A v 6 (by decide)
  · exact install_other pNudge A v 7 (by decide)
  · exact install_other pNudge A v 8 (by decide)
  · exact install_other pNudge A v 9 (by decide)
  · exact install_other pNudge A v 10 (by decide)
  · exact install_other pNudge A v 11 (by decide)
  · exact install_other pNudge A v 12 (by decide)
  · exact install_other pNudge A v 13 (by decide)
  · exact install_other pNudge A v 14 (by decide)
  · exact install_other pNudge A v 15 (by decide)
  · exact install_other pNudge A v 16 (by decide)
  · exact install_other pNudge A v 17 (by decide)

theorem dockH_pNudge (H : Fin 18 → ℕ) (v : Fin 1 → ℕ) :
    dockH pNudge H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17] := by
  funext i
  fin_cases i
  · exact dockH_slot pNudge pNudge_inj H v 0
  · exact dockH_other pNudge H v 1 (by decide)
  · exact dockH_other pNudge H v 2 (by decide)
  · exact dockH_other pNudge H v 3 (by decide)
  · exact dockH_other pNudge H v 4 (by decide)
  · exact dockH_other pNudge H v 5 (by decide)
  · exact dockH_other pNudge H v 6 (by decide)
  · exact dockH_other pNudge H v 7 (by decide)
  · exact dockH_other pNudge H v 8 (by decide)
  · exact dockH_other pNudge H v 9 (by decide)
  · exact dockH_other pNudge H v 10 (by decide)
  · exact dockH_other pNudge H v 11 (by decide)
  · exact dockH_other pNudge H v 12 (by decide)
  · exact dockH_other pNudge H v 13 (by decide)
  · exact dockH_other pNudge H v 14 (by decide)
  · exact dockH_other pNudge H v 15 (by decide)
  · exact dockH_other pNudge H v 16 (by decide)
  · exact dockH_other pNudge H v 17 (by decide)

theorem pMono_inj : Function.Injective pMono := by decide

theorem install_pMono (A : Fin 18 → List Bool) (v : Fin 12 → List Bool) :
    install pMono A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, A 12, A 13, A 14, A 15, A 16, A 17] := by
  funext i
  fin_cases i
  · exact install_slot pMono pMono_inj A v 0
  · exact install_slot pMono pMono_inj A v 1
  · exact install_slot pMono pMono_inj A v 2
  · exact install_slot pMono pMono_inj A v 3
  · exact install_slot pMono pMono_inj A v 4
  · exact install_slot pMono pMono_inj A v 5
  · exact install_slot pMono pMono_inj A v 6
  · exact install_slot pMono pMono_inj A v 7
  · exact install_slot pMono pMono_inj A v 8
  · exact install_slot pMono pMono_inj A v 9
  · exact install_slot pMono pMono_inj A v 10
  · exact install_slot pMono pMono_inj A v 11
  · exact install_other pMono A v 12 (by decide)
  · exact install_other pMono A v 13 (by decide)
  · exact install_other pMono A v 14 (by decide)
  · exact install_other pMono A v 15 (by decide)
  · exact install_other pMono A v 16 (by decide)
  · exact install_other pMono A v 17 (by decide)

theorem dockH_pMono (H : Fin 18 → ℕ) (v : Fin 12 → ℕ) :
    dockH pMono H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, H 12, H 13, H 14, H 15, H 16, H 17] := by
  funext i
  fin_cases i
  · exact dockH_slot pMono pMono_inj H v 0
  · exact dockH_slot pMono pMono_inj H v 1
  · exact dockH_slot pMono pMono_inj H v 2
  · exact dockH_slot pMono pMono_inj H v 3
  · exact dockH_slot pMono pMono_inj H v 4
  · exact dockH_slot pMono pMono_inj H v 5
  · exact dockH_slot pMono pMono_inj H v 6
  · exact dockH_slot pMono pMono_inj H v 7
  · exact dockH_slot pMono pMono_inj H v 8
  · exact dockH_slot pMono pMono_inj H v 9
  · exact dockH_slot pMono pMono_inj H v 10
  · exact dockH_slot pMono pMono_inj H v 11
  · exact dockH_other pMono H v 12 (by decide)
  · exact dockH_other pMono H v 13 (by decide)
  · exact dockH_other pMono H v 14 (by decide)
  · exact dockH_other pMono H v 15 (by decide)
  · exact dockH_other pMono H v 16 (by decide)
  · exact dockH_other pMono H v 17 (by decide)

theorem pIns_inj : Function.Injective pIns := by decide

theorem install_pIns (A : Fin 18 → List Bool) (v : Fin 10 → List Bool) :
    install pIns A v = ![A 0, A 1, A 2, v 8, A 4, A 5, A 6, A 7, v 6, v 7, v 9, A 11, v 0, v 1, v 2, v 3, v 4, v 5] := by
  funext i
  fin_cases i
  · exact install_other pIns A v 0 (by decide)
  · exact install_other pIns A v 1 (by decide)
  · exact install_other pIns A v 2 (by decide)
  · exact install_slot pIns pIns_inj A v 8
  · exact install_other pIns A v 4 (by decide)
  · exact install_other pIns A v 5 (by decide)
  · exact install_other pIns A v 6 (by decide)
  · exact install_other pIns A v 7 (by decide)
  · exact install_slot pIns pIns_inj A v 6
  · exact install_slot pIns pIns_inj A v 7
  · exact install_slot pIns pIns_inj A v 9
  · exact install_other pIns A v 11 (by decide)
  · exact install_slot pIns pIns_inj A v 0
  · exact install_slot pIns pIns_inj A v 1
  · exact install_slot pIns pIns_inj A v 2
  · exact install_slot pIns pIns_inj A v 3
  · exact install_slot pIns pIns_inj A v 4
  · exact install_slot pIns pIns_inj A v 5

theorem dockH_pIns (H : Fin 18 → ℕ) (v : Fin 10 → ℕ) :
    dockH pIns H v = ![H 0, H 1, H 2, v 8, H 4, H 5, H 6, H 7, v 6, v 7, v 9, H 11, v 0, v 1, v 2, v 3, v 4, v 5] := by
  funext i
  fin_cases i
  · exact dockH_other pIns H v 0 (by decide)
  · exact dockH_other pIns H v 1 (by decide)
  · exact dockH_other pIns H v 2 (by decide)
  · exact dockH_slot pIns pIns_inj H v 8
  · exact dockH_other pIns H v 4 (by decide)
  · exact dockH_other pIns H v 5 (by decide)
  · exact dockH_other pIns H v 6 (by decide)
  · exact dockH_other pIns H v 7 (by decide)
  · exact dockH_slot pIns pIns_inj H v 6
  · exact dockH_slot pIns pIns_inj H v 7
  · exact dockH_slot pIns pIns_inj H v 9
  · exact dockH_other pIns H v 11 (by decide)
  · exact dockH_slot pIns pIns_inj H v 0
  · exact dockH_slot pIns pIns_inj H v 1
  · exact dockH_slot pIns pIns_inj H v 2
  · exact dockH_slot pIns pIns_inj H v 3
  · exact dockH_slot pIns pIns_inj H v 4
  · exact dockH_slot pIns pIns_inj H v 5

/-! ## The pipeline state -/

/-- The contents of the pipeline's scratch tapes and the running cancelled list. -/
structure PS where
  Ea : List Bool
  LA : List Bool
  LB : List Bool
  R : List Bool
  R2 : List Bool
  R3 : List Bool
  G : List (List Bool)
  staleG : List Bool
  O : List Bool
  X : List Bool
  Y : List Bool
  Ec : Bool

/-- The entry of the empty mask. -/
def z0 (Q W : ℕ) : List Bool := ew Q W (0, 0)

/-- The masks stage's state at the start of a monomial. -/
def ms0 (Q W : ℕ) (ps : PS) : MState :=
  ⟨[z0 Q W], ps.LA.drop ((frame (z0 Q W)).length + 1), ps.LB, ps.Ea, ps.R, ps.R2, ps.R3⟩

/-- The masks stage's state after a monomial. -/
def msOf (Q : ℕ) (pool : List (List SynEq)) (mono : List ℕ) (ps : PS) : MState :=
  mono.foldl (mstep (childTable Q pool)) (ms0 Q pool.flatten.length ps)

/-- The insert-all stage's state at the start of a monomial. -/
def as0 (ps : PS) : AllState := ⟨ps.G, ps.staleG, ps.O, ps.X, ps.Y, ps.Ec⟩

/-- **One monomial of the pipeline**: its masks written, then inserted into the running list. -/
def f1 (Q : ℕ) (pool : List (List SynEq)) (ps : PS) (mono : List ℕ) : PS :=
  ⟨(msOf Q pool mono ps).Ea, streamTape (msOf Q pool mono ps).L (msOf Q pool mono ps).staleA,
    (msOf Q pool mono ps).LB, (msOf Q pool mono ps).R, (msOf Q pool mono ps).R2, (msOf Q pool mono ps).R3,
    ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).G, ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).staleS,
    ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).O, ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).xp,
    ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).y, ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).e⟩

theorem msOf_L (Q : ℕ) (pool : List (List SynEq)) (mono : List ℕ) (ps : PS) (hmono : ∀ a ∈ mono, a < pool.length) :
    (msOf Q pool mono ps).L = (monoMasks pool mono).map (fun U => ew Q pool.flatten.length (0, U)) := by
  unfold msOf
  rw [foldl_mstep_L]
  show mono.foldl (fun L a => expandW L ((childTable Q pool).getD a []))
    ([0].map fun U => ew Q pool.flatten.length (0, U)) = _
  rw [foldl_expandW_map Q pool mono [0] hmono, monoMasks_foldl]

/-- **The running list after a monomial**: its mask entries inserted by symmetric difference. -/
theorem f1_G (Q : ℕ) (pool : List (List SynEq)) (ps : PS) (mono : List ℕ) (hmono : ∀ a ∈ mono, a < pool.length) :
    (f1 Q pool ps mono).G =
      ((monoMasks pool mono).map (fun U => ew Q pool.flatten.length (0, U))).foldl symInsertW ps.G := by
  show ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).G = _
  rw [foldl_allStep_G, msOf_L Q pool mono ps hmono]
  rfl

theorem msOf_inv (Q : ℕ) (pool : List (List SynEq)) (mono : List ℕ) (ps : PS) (hmono : ∀ a ∈ mono, a < pool.length)
    (h1 : ps.R.length = Q + pool.flatten.length + 1) (h2 : ps.R2.length = Q + pool.flatten.length + 1)
    (h3 : ps.R3.length = Q + pool.flatten.length + 1) : MInv (Q + pool.flatten.length + 1) (msOf Q pool mono ps) := by
  have hz : (z0 Q pool.flatten.length).length = Q + pool.flatten.length + 1 := entryWord_length Q _ 0 0 (by omega)
  have hTab : (childTable Q pool).length = pool.length := by simp [childTable]
  exact (foldl_mstep (childTable Q pool) (Q + pool.flatten.length + 1) (pool.flatten.length + 1)
    (childTable_props Q pool) mono (ms0 Q pool.flatten.length ps) (by intro a ha; rw [hTab]; exact hmono a ha)
    ⟨by intro U hU; simp only [ms0, List.mem_singleton] at hU; rw [hU, hz], h1, h2, h3⟩).1

/-- **The masks machine with an explicit exit** (the proof of `Masks.monomial_run`, with the final state named). -/
theorem monomial_x (Q : ℕ) (pool : List (List SynEq)) (mono : List ℕ) (P post staleT : List Bool) (ps : PS)
    (cap cap2 cap3 : ℕ) (hmono : ∀ a ∈ mono, a < pool.length)
    (h1 : ps.R.length = Q + pool.flatten.length + 1) (h2 : ps.R2.length = Q + pool.flatten.length + 1)
    (h3 : ps.R3.length = Q + pool.flatten.length + 1) (hcap : 2 * (Q + pool.flatten.length + 1) + 1 ≤ cap)
    (hcap2 : (pool.flatten.length + 1) * (innerCost (Q + pool.flatten.length + 1) + 2) + 1 ≤ cap2)
    (hcap3 : max (lookupCost pool.length (pool.flatten.length + 1) (Q + pool.flatten.length + 1))
      (max (expandLoopCost ((pool.flatten.length + 1) ^ mono.length) (pool.flatten.length + 1) (Q + pool.flatten.length + 1))
        (copyLoopCost ((pool.flatten.length + 1) ^ mono.length) (Q + pool.flatten.length + 1))) ≤ cap3)
    (hcap3' : 2 * (2 * (Q + pool.flatten.length + 1) + 1) + 2 + 1 + 1 ≤ cap3) :
    Step monoM (monoCost mono.length pool.length Q pool.flatten.length) ![P.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, ps.Ea, ps.LA, ps.LB, frame ps.R,
        frame ps.R2, frame ps.R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false,
        frame (z0 Q pool.flatten.length)]
      ![P.length + (mono.flatMap pairsTape).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, (msOf Q pool mono ps).Ea,
        streamTape (msOf Q pool mono ps).L (msOf Q pool mono ps).staleA, (msOf Q pool mono ps).LB,
        frame (msOf Q pool mono ps).R, frame (msOf Q pool mono ps).R2, frame (msOf Q pool mono ps).R3,
        List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false,
        frame (z0 Q pool.flatten.length)] := by
  set W := pool.flatten.length
  set L := Q + W + 1
  set z := z0 Q W
  have hz : z.length = L := entryWord_length Q W 0 0 (by omega)
  have hM : P ++ frame (codeBits mono) ++ post = P ++ mono.flatMap pairsTape ++ false :: post := by
    rw [frame_codeBits]; simp [List.append_assoc]
  have e1 := init_run ps.LA z cap cap3 (by rw [hz]; exact hcap) (by rw [hz]; exact hcap3')
  have s1 := dockKeep e1 nInit nInit_inj ![P.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, ps.Ea, ps.LA, ps.LB, frame ps.R,
      frame ps.R2, frame ps.R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame z]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_nInit] at s1
  have h0 : MInv L (ms0 Q W ps) := ⟨by intro U hU; simp only [ms0, List.mem_singleton] at hU; rw [hU, hz], h1, h2, h3⟩
  have hTab : (childTable Q pool).length = pool.length := by simp [childTable]
  have e2 := atoms_run P post mono (childTable Q pool) staleT cap cap2 cap3 (W + 1) L (ms0 Q W ps)
    (by intro a ha; rw [hTab]; exact hmono a ha) (childTable_props Q pool) (by omega) (by omega) h0 rfl hcap hcap2
    (by rw [hTab]; exact hcap3)
  rw [← hM] at e2
  have s2 := dockRun e2 nAtoms nAtoms_inj ![P.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![P ++ frame (codeBits mono) ++ post, tableTape (childTable Q pool) staleT, ps.Ea,
      streamTape [z] (ps.LA.drop ((frame z).length + 1)), ps.LB, frame ps.R, frame ps.R2, frame ps.R3,
      List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame z]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_nAtoms, dockH_nAtoms] at s2
  have hall := s1.seq s2
  refine (hall.enlarge (by unfold monoCost; rw [hTab, hz])).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ## One monomial record -/

def recW (mono : List ℕ) : List Bool := true :: frame (codeBits mono)

def head1 (p : ℕ) : Fin 18 → ℕ := ![p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def bank1 (VT TT : List Bool) (cap cap2 cap3 : ℕ) (z : List Bool) (ps : PS) : Fin 18 → List Bool :=
  ![VT, TT, ps.Ea, ps.LA, ps.LB, frame ps.R, frame ps.R2, frame ps.R3, List.replicate cap false,
    List.replicate cap2 false, List.replicate cap3 false, frame z, streamTape ps.G ps.staleG, ps.O, frame ps.X,
    frame ps.Y, [ps.Ec], [false]]

/-- The widths of the pipeline's registers and running list. -/
def PInv (L : ℕ) (ps : PS) : Prop :=
  ps.R.length = L ∧ ps.R2.length = L ∧ ps.R3.length = L ∧ ps.X.length = L ∧ ps.Y.length = L ∧ ∀ g ∈ ps.G, g.length = L

/-- The uniform cost of one monomial: at most `d` atoms, running lists and mask lists at most `B`. -/
def monoInsCost (d P Q W B : ℕ) : ℕ := 1 + 1 + monoCost d P Q W + 1 + 1 + 1 + insertAllCost B B (Q + W + 1)

/-- The capacities one monomial needs. -/
structure Caps (d P Q W B cap cap2 cap3 : ℕ) : Prop where
  c1 : 2 * (Q + W + 1) + 1 ≤ cap
  c2m : (W + 1) * (innerCost (Q + W + 1) + 2) + 1 ≤ cap2
  c2i : filterLoopCost B (Q + W + 1) ≤ cap2 ∧ copyLoopCost (B + 1) (Q + W + 1) ≤ cap2
  c3m : max (lookupCost P (W + 1) (Q + W + 1))
      (max (expandLoopCost ((W + 1) ^ d) (W + 1) (Q + W + 1)) (copyLoopCost ((W + 1) ^ d) (Q + W + 1))) ≤ cap3
  c3' : 2 * (2 * (Q + W + 1) + 1) + 2 + 1 + 1 ≤ cap3
  c3i : B * (allCost B (Q + W + 1) + 2) + 1 ≤ cap3

theorem mono_ins_step (Q : ℕ) (pool : List (List SynEq)) (mono : List ℕ) (P post staleT : List Bool) (ps : PS)
    (cap cap2 cap3 d n0 B : ℕ) (hmono : ∀ a ∈ mono, a < pool.length) (hd : mono.length ≤ d)
    (hinv : PInv (Q + pool.flatten.length + 1) ps) (hn0 : ps.G.length ≤ n0)
    (hB : n0 + (monoMasks pool mono).length ≤ B) (hc : Caps d pool.length Q pool.flatten.length B cap cap2 cap3) :
    Step monoInsM (monoInsCost d pool.length Q pool.flatten.length B) (head1 P.length)
      (bank1 (P ++ recW mono ++ post) (tableTape (childTable Q pool) staleT) cap cap2 cap3 (z0 Q pool.flatten.length) ps)
      (head1 (P.length + (recW mono).length))
      (bank1 (P ++ recW mono ++ post) (tableTape (childTable Q pool) staleT) cap cap2 cap3 (z0 Q pool.flatten.length)
        (f1 Q pool ps mono)) := by
  obtain ⟨hR, hR2, hR3, hX, hY, hG⟩ := hinv
  set VT := P ++ recW mono ++ post
  set TT := tableTape (childTable Q pool) staleT
  have hVT : VT = (P ++ [true]) ++ frame (codeBits mono) ++ post := by simp [VT, recW, List.append_assoc]
  -- step past the marker
  have s1 := dockRun (nudge_run VT P.length) pNudge pNudge_inj (head1 P.length)
    (bank1 VT TT cap cap2 cap3 (z0 Q pool.flatten.length) ps) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_pNudge, dockH_pNudge] at s1
  have s1' := s1.congr (hout' := ![(P ++ [true]).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    (tout' := bank1 VT TT cap cap2 cap3 (z0 Q pool.flatten.length) ps) (by funext i; fin_cases i <;> simp [head1])
    (by funext i; fin_cases i <;> rfl)
  -- the masks
  have hpow : (pool.flatten.length + 1) ^ mono.length ≤ (pool.flatten.length + 1) ^ d := Nat.pow_le_pow_right (by omega) hd
  have e2 := monomial_x Q pool mono (P ++ [true]) post staleT ps cap cap2 cap3 hmono hR hR2 hR3 hc.c1 hc.c2m
    ((max_le_max (le_refl _) (max_le_max (expandLoopCost_mono2 hpow) (copyLoopCost_mono2 hpow (le_refl _)))).trans hc.c3m)
    hc.c3'
  rw [← hVT] at e2
  have s2 := dockRun e2 pMono pMono_inj ![(P ++ [true]).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    (bank1 VT TT cap cap2 cap3 (z0 Q pool.flatten.length) ps) (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_pMono, dockH_pMono] at s2
  -- step past the frame's terminator
  set ms := msOf Q pool mono ps
  have s3 := dockRun (nudge_run VT ((P ++ [true]).length + (mono.flatMap pairsTape).length)) pNudge pNudge_inj
    ![(P ++ [true]).length + (mono.flatMap pairsTape).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![VT, TT, ms.Ea, streamTape ms.L ms.staleA, ms.LB, frame ms.R, frame ms.R2, frame ms.R3, List.replicate cap false,
      List.replicate cap2 false, List.replicate cap3 false, frame (z0 Q pool.flatten.length), streamTape ps.G ps.staleG, ps.O,
      frame ps.X, frame ps.Y, [ps.Ec], [false]] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_pNudge, dockH_pNudge] at s3
  -- insert the masks
  have hLs := msOf_L Q pool mono ps hmono
  have hLw : ∀ x ∈ ms.L, x.length = (Q + pool.flatten.length + 1) := by
    rw [hLs]; intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact entryWord_length Q pool.flatten.length 0 u (by omega)
  have hLlen : ms.L.length = (monoMasks pool mono).length := by rw [hLs, List.length_map]
  have hnb : n0 + ms.L.length ≤ B := by rw [hLlen]; exact hB
  have e4 := insertAll_run ms.L ms.staleA cap cap2 cap3 (Q + pool.flatten.length + 1) n0 (as0 ps) hLw (by omega) ⟨hG, hX, hY, hn0⟩ hc.c1
    ⟨(filterLoopCost_mono2 hnb (le_refl _)).trans hc.c2i.1,
      (copyLoopCost_mono2 (Nat.add_le_add_right hnb 1) (le_refl _)).trans hc.c2i.2⟩
    (le_trans (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (Nat.add_le_add_right (allCost_mono2 hnb (le_refl _)) 2)) 1)
      hc.c3i)
  have s4 := dockKeep e4 pIns pIns_inj
    ![(P ++ [true]).length + (mono.flatMap pairsTape).length + 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![VT, TT, ms.Ea, streamTape ms.L ms.staleA, ms.LB, frame ms.R, frame ms.R2, frame ms.R3, List.replicate cap false,
      List.replicate cap2 false, List.replicate cap3 false, frame (z0 Q pool.flatten.length), streamTape ps.G ps.staleG, ps.O,
      frame ps.X, frame ps.Y, [ps.Ec], [false]] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_pIns] at s4
  have hall := ((s1'.seq s2).seq s3).seq s4
  have hcost := insertAllCost_mono (m := ms.L.length) (m' := B) (n := n0) (n' := B) (W := Q + pool.flatten.length + 1) (W' := Q + pool.flatten.length + 1) (by omega)
    (by omega) (le_refl _)
  have hmc := monoCost_mono (P := pool.length) (Q := Q) (W := pool.flatten.length) hd
  refine (hall.enlarge (by unfold monoInsCost; omega)).congr ?_ ?_
  · funext i; fin_cases i <;> simp [head1, recW, frame_codeBits]
    all_goals omega
  · funext i; fin_cases i <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
