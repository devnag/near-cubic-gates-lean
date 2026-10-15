import Proof.Wire_3_5.CompilerMachinePolyLoop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

/-! ## The layout: 0-17 the polynomial layout, 18 the counter `J`, 19 the parity cell -/

def fV : Fin 1 → Fin 20 := ![0]
def fJ : Fin 1 → Fin 20 := ![18]
def fPJ : Fin 1 → Fin 20 := ![19]
def fPoly : Fin 18 → Fin 20 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

noncomputable def fNudgeVD := RecoveryFocus.machine fV nudgeM
noncomputable def fNudgeJD := RecoveryFocus.machine fJ nudgeM
noncomputable def fSkipD := RecoveryFocus.machine fV skipM
noncomputable def fPJ0D := RecoveryFocus.machine fPJ (cellM false)
noncomputable def fPJ1D := RecoveryFocus.machine fPJ (cellM true)
/-- Flip the parity cell. -/
noncomputable def fFlipM := branchM 19 fPJ0D fPJ1D
noncomputable def fPolyD := RecoveryFocus.machine fPoly polyLoopM
noncomputable def fSelM := Composition.machine fFlipM fPolyD
noncomputable def fSkipRecM := Composition.machine fNudgeVD fSkipD
noncomputable def fSkipLoopM := StreamController.machine fSkipRecM 0
/-- **One factor**: step past its marker; if the counter bit is set, flip the parity and substitute the factor, else skip
it; step past its terminator; move the counter head to the next bit. -/
noncomputable def factorM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine fNudgeVD
    (branchM 18 fSelM fSkipLoopM)) fNudgeVD) fNudgeJD) fNudgeJD

theorem fV_inj : Function.Injective fV := by decide

theorem install_fV (A : Fin 20 → List Bool) (v : Fin 1 → List Bool) :
    install fV A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19] := by
  funext i
  fin_cases i
  · exact install_slot fV fV_inj A v 0
  · exact install_other fV A v 1 (by decide)
  · exact install_other fV A v 2 (by decide)
  · exact install_other fV A v 3 (by decide)
  · exact install_other fV A v 4 (by decide)
  · exact install_other fV A v 5 (by decide)
  · exact install_other fV A v 6 (by decide)
  · exact install_other fV A v 7 (by decide)
  · exact install_other fV A v 8 (by decide)
  · exact install_other fV A v 9 (by decide)
  · exact install_other fV A v 10 (by decide)
  · exact install_other fV A v 11 (by decide)
  · exact install_other fV A v 12 (by decide)
  · exact install_other fV A v 13 (by decide)
  · exact install_other fV A v 14 (by decide)
  · exact install_other fV A v 15 (by decide)
  · exact install_other fV A v 16 (by decide)
  · exact install_other fV A v 17 (by decide)
  · exact install_other fV A v 18 (by decide)
  · exact install_other fV A v 19 (by decide)

theorem dockH_fV (H : Fin 20 → ℕ) (v : Fin 1 → ℕ) :
    dockH fV H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19] := by
  funext i
  fin_cases i
  · exact dockH_slot fV fV_inj H v 0
  · exact dockH_other fV H v 1 (by decide)
  · exact dockH_other fV H v 2 (by decide)
  · exact dockH_other fV H v 3 (by decide)
  · exact dockH_other fV H v 4 (by decide)
  · exact dockH_other fV H v 5 (by decide)
  · exact dockH_other fV H v 6 (by decide)
  · exact dockH_other fV H v 7 (by decide)
  · exact dockH_other fV H v 8 (by decide)
  · exact dockH_other fV H v 9 (by decide)
  · exact dockH_other fV H v 10 (by decide)
  · exact dockH_other fV H v 11 (by decide)
  · exact dockH_other fV H v 12 (by decide)
  · exact dockH_other fV H v 13 (by decide)
  · exact dockH_other fV H v 14 (by decide)
  · exact dockH_other fV H v 15 (by decide)
  · exact dockH_other fV H v 16 (by decide)
  · exact dockH_other fV H v 17 (by decide)
  · exact dockH_other fV H v 18 (by decide)
  · exact dockH_other fV H v 19 (by decide)

theorem fJ_inj : Function.Injective fJ := by decide

theorem install_fJ (A : Fin 20 → List Bool) (v : Fin 1 → List Bool) :
    install fJ A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 0, A 19] := by
  funext i
  fin_cases i
  · exact install_other fJ A v 0 (by decide)
  · exact install_other fJ A v 1 (by decide)
  · exact install_other fJ A v 2 (by decide)
  · exact install_other fJ A v 3 (by decide)
  · exact install_other fJ A v 4 (by decide)
  · exact install_other fJ A v 5 (by decide)
  · exact install_other fJ A v 6 (by decide)
  · exact install_other fJ A v 7 (by decide)
  · exact install_other fJ A v 8 (by decide)
  · exact install_other fJ A v 9 (by decide)
  · exact install_other fJ A v 10 (by decide)
  · exact install_other fJ A v 11 (by decide)
  · exact install_other fJ A v 12 (by decide)
  · exact install_other fJ A v 13 (by decide)
  · exact install_other fJ A v 14 (by decide)
  · exact install_other fJ A v 15 (by decide)
  · exact install_other fJ A v 16 (by decide)
  · exact install_other fJ A v 17 (by decide)
  · exact install_slot fJ fJ_inj A v 0
  · exact install_other fJ A v 19 (by decide)

theorem dockH_fJ (H : Fin 20 → ℕ) (v : Fin 1 → ℕ) :
    dockH fJ H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 0, H 19] := by
  funext i
  fin_cases i
  · exact dockH_other fJ H v 0 (by decide)
  · exact dockH_other fJ H v 1 (by decide)
  · exact dockH_other fJ H v 2 (by decide)
  · exact dockH_other fJ H v 3 (by decide)
  · exact dockH_other fJ H v 4 (by decide)
  · exact dockH_other fJ H v 5 (by decide)
  · exact dockH_other fJ H v 6 (by decide)
  · exact dockH_other fJ H v 7 (by decide)
  · exact dockH_other fJ H v 8 (by decide)
  · exact dockH_other fJ H v 9 (by decide)
  · exact dockH_other fJ H v 10 (by decide)
  · exact dockH_other fJ H v 11 (by decide)
  · exact dockH_other fJ H v 12 (by decide)
  · exact dockH_other fJ H v 13 (by decide)
  · exact dockH_other fJ H v 14 (by decide)
  · exact dockH_other fJ H v 15 (by decide)
  · exact dockH_other fJ H v 16 (by decide)
  · exact dockH_other fJ H v 17 (by decide)
  · exact dockH_slot fJ fJ_inj H v 0
  · exact dockH_other fJ H v 19 (by decide)

theorem fPJ_inj : Function.Injective fPJ := by decide

theorem install_fPJ (A : Fin 20 → List Bool) (v : Fin 1 → List Bool) :
    install fPJ A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 0] := by
  funext i
  fin_cases i
  · exact install_other fPJ A v 0 (by decide)
  · exact install_other fPJ A v 1 (by decide)
  · exact install_other fPJ A v 2 (by decide)
  · exact install_other fPJ A v 3 (by decide)
  · exact install_other fPJ A v 4 (by decide)
  · exact install_other fPJ A v 5 (by decide)
  · exact install_other fPJ A v 6 (by decide)
  · exact install_other fPJ A v 7 (by decide)
  · exact install_other fPJ A v 8 (by decide)
  · exact install_other fPJ A v 9 (by decide)
  · exact install_other fPJ A v 10 (by decide)
  · exact install_other fPJ A v 11 (by decide)
  · exact install_other fPJ A v 12 (by decide)
  · exact install_other fPJ A v 13 (by decide)
  · exact install_other fPJ A v 14 (by decide)
  · exact install_other fPJ A v 15 (by decide)
  · exact install_other fPJ A v 16 (by decide)
  · exact install_other fPJ A v 17 (by decide)
  · exact install_other fPJ A v 18 (by decide)
  · exact install_slot fPJ fPJ_inj A v 0

theorem dockH_fPJ (H : Fin 20 → ℕ) (v : Fin 1 → ℕ) :
    dockH fPJ H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other fPJ H v 0 (by decide)
  · exact dockH_other fPJ H v 1 (by decide)
  · exact dockH_other fPJ H v 2 (by decide)
  · exact dockH_other fPJ H v 3 (by decide)
  · exact dockH_other fPJ H v 4 (by decide)
  · exact dockH_other fPJ H v 5 (by decide)
  · exact dockH_other fPJ H v 6 (by decide)
  · exact dockH_other fPJ H v 7 (by decide)
  · exact dockH_other fPJ H v 8 (by decide)
  · exact dockH_other fPJ H v 9 (by decide)
  · exact dockH_other fPJ H v 10 (by decide)
  · exact dockH_other fPJ H v 11 (by decide)
  · exact dockH_other fPJ H v 12 (by decide)
  · exact dockH_other fPJ H v 13 (by decide)
  · exact dockH_other fPJ H v 14 (by decide)
  · exact dockH_other fPJ H v 15 (by decide)
  · exact dockH_other fPJ H v 16 (by decide)
  · exact dockH_other fPJ H v 17 (by decide)
  · exact dockH_other fPJ H v 18 (by decide)
  · exact dockH_slot fPJ fPJ_inj H v 0

theorem fPoly_inj : Function.Injective fPoly := by decide

theorem install_fPoly (A : Fin 20 → List Bool) (v : Fin 18 → List Bool) :
    install fPoly A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, A 18, A 19] := by
  funext i
  fin_cases i
  · exact install_slot fPoly fPoly_inj A v 0
  · exact install_slot fPoly fPoly_inj A v 1
  · exact install_slot fPoly fPoly_inj A v 2
  · exact install_slot fPoly fPoly_inj A v 3
  · exact install_slot fPoly fPoly_inj A v 4
  · exact install_slot fPoly fPoly_inj A v 5
  · exact install_slot fPoly fPoly_inj A v 6
  · exact install_slot fPoly fPoly_inj A v 7
  · exact install_slot fPoly fPoly_inj A v 8
  · exact install_slot fPoly fPoly_inj A v 9
  · exact install_slot fPoly fPoly_inj A v 10
  · exact install_slot fPoly fPoly_inj A v 11
  · exact install_slot fPoly fPoly_inj A v 12
  · exact install_slot fPoly fPoly_inj A v 13
  · exact install_slot fPoly fPoly_inj A v 14
  · exact install_slot fPoly fPoly_inj A v 15
  · exact install_slot fPoly fPoly_inj A v 16
  · exact install_slot fPoly fPoly_inj A v 17
  · exact install_other fPoly A v 18 (by decide)
  · exact install_other fPoly A v 19 (by decide)

theorem dockH_fPoly (H : Fin 20 → ℕ) (v : Fin 18 → ℕ) :
    dockH fPoly H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, H 18, H 19] := by
  funext i
  fin_cases i
  · exact dockH_slot fPoly fPoly_inj H v 0
  · exact dockH_slot fPoly fPoly_inj H v 1
  · exact dockH_slot fPoly fPoly_inj H v 2
  · exact dockH_slot fPoly fPoly_inj H v 3
  · exact dockH_slot fPoly fPoly_inj H v 4
  · exact dockH_slot fPoly fPoly_inj H v 5
  · exact dockH_slot fPoly fPoly_inj H v 6
  · exact dockH_slot fPoly fPoly_inj H v 7
  · exact dockH_slot fPoly fPoly_inj H v 8
  · exact dockH_slot fPoly fPoly_inj H v 9
  · exact dockH_slot fPoly fPoly_inj H v 10
  · exact dockH_slot fPoly fPoly_inj H v 11
  · exact dockH_slot fPoly fPoly_inj H v 12
  · exact dockH_slot fPoly fPoly_inj H v 13
  · exact dockH_slot fPoly fPoly_inj H v 14
  · exact dockH_slot fPoly fPoly_inj H v 15
  · exact dockH_slot fPoly fPoly_inj H v 16
  · exact dockH_slot fPoly fPoly_inj H v 17
  · exact dockH_other fPoly H v 18 (by decide)
  · exact dockH_other fPoly H v 19 (by decide)

/-! ## Banks -/

def head2 (p jh : ℕ) : Fin 20 → ℕ := ![p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jh, 0]

def bank2 (VT TT : List Bool) (cap cap2 cap3 : ℕ) (z Jt : List Bool) (ps : PS) (PJ : Bool) : Fin 20 → List Bool :=
  ![VT, TT, ps.Ea, ps.LA, ps.LB, frame ps.R, frame ps.R2, frame ps.R3, List.replicate cap false,
    List.replicate cap2 false, List.replicate cap3 false, frame z, streamTape ps.G ps.staleG, ps.O, frame ps.X,
    frame ps.Y, [ps.Ec], [false], Jt, [PJ]]

/-- A factor's record: a marker, its monomials' records, a terminator. -/
def factorRec (f : F2Poly ℕ) : List Bool := true :: (f.flatMap recW ++ [false])

/-! ## Skipping a factor -/

theorem skipRec_step (VT TT Jt : List Bool) (cap cap2 cap3 : ℕ) (z : List Bool) (ps : PS) (PJ : Bool)
    (P mono post : List Bool) (jh : ℕ) (hVT : VT = P ++ true :: frame mono ++ post) :
    Step fSkipRecM (1 + 1 + (2 * mono.length + 1)) (head2 P.length jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ)
      (head2 (P.length + (1 + (2 * mono.length + 1))) jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ) := by
  have s1 := dockRun (nudge_run VT P.length) fV fV_inj (head2 P.length jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_fV, dockH_fV] at s1
  have e2 := skipStep (P ++ [true]) mono post
  rw [show P ++ [true] ++ frame mono ++ post = VT by rw [hVT]; simp [List.append_assoc]] at e2
  have s2 := dockRun e2 fV fV_inj ![(P ++ [true]).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jh, 0]
    (bank2 VT TT cap cap2 cap3 z Jt ps PJ) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_fV, dockH_fV] at s2
  have s1' := s1.congr (hout' := ![(P ++ [true]).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jh, 0])
    (tout' := bank2 VT TT cap cap2 cap3 z Jt ps PJ) (by funext i; fin_cases i <;> simp [head2]) (by funext i; fin_cases i <;> rfl)
  refine (s1'.seq s2).congr ?_ ?_
  · funext i; fin_cases i <;> simp [head2]
    all_goals omega
  · funext i; fin_cases i <;> rfl

theorem codeBits_frame_length (mono : List ℕ) : (recW mono).length = 1 + (2 * (codeBits mono).length + 1) := by
  simp [recW, frame_length]; omega

/-- **Skip a factor's monomials**, codes at most `CB` bits long. -/
theorem skipPoly_run (TT Jt : List Bool) (cap cap2 cap3 : ℕ) (z : List Bool) (ps : PS) (PJ : Bool)
    (P : List Bool) (f : F2Poly ℕ) (post : List Bool) (jh CB : ℕ) (hCB : ∀ mono ∈ f, (codeBits mono).length ≤ CB) :
    Step fSkipLoopM (f.length * (1 + 1 + (2 * CB + 1) + 2) + 1) (head2 P.length jh)
      (bank2 (P ++ f.flatMap recW ++ false :: post) TT cap cap2 cap3 z Jt ps PJ)
      (head2 (P.length + (f.flatMap recW).length) jh)
      (bank2 (P ++ f.flatMap recW ++ false :: post) TT cap cap2 cap3 z Jt ps PJ) := by
  have h := encRun recW recW_head fSkipRecM 0 P f post (fun (u : Unit) _ => u) () (fun _ p => head2 p jh)
    (fun _ => bank2 (P ++ f.flatMap recW ++ false :: post) TT cap cap2 cap3 z Jt ps PJ) (fun _ => rfl) (fun _ _ => rfl)
    (1 + 1 + (2 * CB + 1)) (by
      intro j hj
      have hs := skipRec_step (P ++ f.flatMap recW ++ false :: post) TT Jt cap cap2 cap3 z ps PJ
        (P ++ (f.take j).flatMap recW) (codeBits f[j]) ((f.drop (j + 1)).flatMap recW ++ false :: post) jh
        (by rw [enc_split recW f j hj]; simp [recW, List.append_assoc])
      rw [enc_succ_length recW f j hj, codeBits_frame_length]
      have hb := hCB _ (List.getElem_mem hj)
      refine ((hs.enlarge (m := 1 + 1 + (2 * CB + 1)) (by omega)).congr_in ?_ rfl).congr ?_ rfl
      · funext i; fin_cases i <;> simp [head2]
      · funext i; fin_cases i <;> simp [head2]
        all_goals omega)
  exact h

/-! ## Flipping the parity cell -/

theorem flip_step (VT TT Jt : List Bool) (cap cap2 cap3 : ℕ) (z : List Bool) (ps : PS) (PJ : Bool) (p jh : ℕ) :
    Step fFlipM (1 + 2) (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ) (head2 p jh)
      (bank2 VT TT cap cap2 cap3 z Jt ps (!PJ)) := by
  cases PJ with
  | true =>
    have e := dockRun (cellStep false true) fPJ fPJ_inj (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps true)
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [install_fPJ, dockH_fPJ] at e
    refine (branch_true (19 : Fin 20) fPJ1D e (by rfl)).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  | false =>
    have e := dockRun (cellStep true false) fPJ fPJ_inj (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps false)
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [install_fPJ, dockH_fPJ] at e
    refine (branch_false (19 : Fin 20) fPJ0D e (by rfl)).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

/-! ## Substituting a selected factor -/

theorem polyD_run (Q : ℕ) (pool : List (List SynEq)) (f : F2Poly ℕ) (P post staleT Jt : List Bool) (ps : PS)
    (PJ : Bool) (cap cap2 cap3 d B jh : ℕ) (hp : ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length)
    (hd : ∀ mono ∈ f, mono.length ≤ d) (hinv : PInv (Q + pool.flatten.length + 1) ps)
    (hB : ps.G.length + (f.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B cap cap2 cap3) :
    Step fPolyD (f.length * (monoInsCost d pool.length Q pool.flatten.length B + 2) + 1) (head2 P.length jh)
      (bank2 (P ++ f.flatMap recW ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) Jt ps PJ)
      (head2 (P.length + (f.flatMap recW).length) jh)
      (bank2 (P ++ f.flatMap recW ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) Jt (f.foldl (f1 Q pool) ps) PJ) := by
  have e := poly_run Q pool f P post staleT ps cap cap2 cap3 d B hp hd hinv hB hc
  have h := dockRun e fPoly fPoly_inj (head2 P.length jh)
    (bank2 (P ++ f.flatMap recW ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
      (z0 Q pool.flatten.length) Jt ps PJ) (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_fPoly, dockH_fPoly] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- The uniform cost of one factor: at most `NF` monomials, codes at most `CB` bits. -/
def factorCost (NF CB d P Q W B : ℕ) : ℕ :=
  1 + 1 + ((1 + 2 + 1 + (NF * (monoInsCost d P Q W B + 2) + 1)) + (NF * (1 + 1 + (2 * CB + 1) + 2) + 1) + 2) + 1 + 1 +
    1 + 1 + 1

theorem nudgeJ_step (VT TT Jt : List Bool) (cap cap2 cap3 : ℕ) (z : List Bool) (ps : PS) (PJ : Bool) (p jh : ℕ) :
    Step fNudgeJD 1 (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ) (head2 p (jh + 1))
      (bank2 VT TT cap cap2 cap3 z Jt ps PJ) := by
  have e := dockRun (nudge_run Jt jh) fJ fJ_inj (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_fJ, dockH_fJ] at e
  refine e.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem nudgeV_step (VT TT Jt : List Bool) (cap cap2 cap3 : ℕ) (z : List Bool) (ps : PS) (PJ : Bool) (p jh : ℕ) :
    Step fNudgeVD 1 (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ) (head2 (p + 1) jh)
      (bank2 VT TT cap cap2 cap3 z Jt ps PJ) := by
  have e := dockRun (nudge_run VT p) fV fV_inj (head2 p jh) (bank2 VT TT cap cap2 cap3 z Jt ps PJ)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_fV, dockH_fV] at e
  refine e.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- The factor loop's state: the pipeline state, the parity cell. -/
def f2 (Q : ℕ) (pool : List (List SynEq)) (b : Bool) (st : PS × Bool) (f : F2Poly ℕ) : PS × Bool :=
  if b then (f.foldl (f1 Q pool) st.1, !st.2) else st

theorem factor_step (Q : ℕ) (pool : List (List SynEq)) (f : F2Poly ℕ) (P post staleT Jt : List Bool) (ps : PS)
    (PJ b : Bool) (cap cap2 cap3 d B NF CB jh : ℕ) (hb : readTapeBit Jt jh = b)
    (hp : ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (hd : ∀ mono ∈ f, mono.length ≤ d)
    (hNF : f.length ≤ NF) (hCB : ∀ mono ∈ f, (codeBits mono).length ≤ CB) (hinv : PInv (Q + pool.flatten.length + 1) ps)
    (hB : ps.G.length + (f.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B cap cap2 cap3) :
    Step factorM (factorCost NF CB d pool.length Q pool.flatten.length B) (head2 P.length jh)
      (bank2 (P ++ factorRec f ++ post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) Jt ps PJ)
      (head2 (P.length + (factorRec f).length) (jh + 2))
      (bank2 (P ++ factorRec f ++ post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) Jt (f2 Q pool b (ps, PJ) f).1 (f2 Q pool b (ps, PJ) f).2) := by
  set TT := tableTape (childTable Q pool) staleT
  set z := z0 Q pool.flatten.length
  have hVT : P ++ factorRec f ++ post = (P ++ [true]) ++ f.flatMap recW ++ false :: post := by
    simp [factorRec, List.append_assoc]
  rw [hVT]
  set VT := (P ++ [true]) ++ f.flatMap recW ++ false :: post
  have s1 := nudgeV_step VT TT Jt cap cap2 cap3 z ps PJ P.length jh
  have s1' := s1.congr (hout' := head2 (P ++ [true]).length jh) (tout' := bank2 VT TT cap cap2 cap3 z Jt ps PJ)
    (by funext i; fin_cases i <;> simp [head2]) rfl
  have hpoly : f.length * (monoInsCost d pool.length Q pool.flatten.length B + 2) + 1 ≤
      NF * (monoInsCost d pool.length Q pool.flatten.length B + 2) + 1 := by
    have := Nat.mul_le_mul_right (monoInsCost d pool.length Q pool.flatten.length B + 2) hNF; omega
  have hskip : f.length * (1 + 1 + (2 * CB + 1) + 2) + 1 ≤ NF * (1 + 1 + (2 * CB + 1) + 2) + 1 := by
    have := Nat.mul_le_mul_right (1 + 1 + (2 * CB + 1) + 2) hNF; omega
  cases b with
  | true =>
    have e1 := flip_step VT TT Jt cap cap2 cap3 z ps PJ (P ++ [true]).length jh
    have e2 := polyD_run Q pool f (P ++ [true]) post staleT Jt ps (!PJ) cap cap2 cap3 d B jh hp hd hinv hB hc
    have eS := branch_true (18 : Fin 20) fSkipLoopM (e1.seq e2) (by rw [← hb]; rfl)
    have s3 := nudgeV_step VT TT Jt cap cap2 cap3 z (f.foldl (f1 Q pool) ps) (!PJ)
      ((P ++ [true]).length + (f.flatMap recW).length) jh
    have s4 := nudgeJ_step VT TT Jt cap cap2 cap3 z (f.foldl (f1 Q pool) ps) (!PJ)
      ((P ++ [true]).length + (f.flatMap recW).length + 1) jh
    have s5 := nudgeJ_step VT TT Jt cap cap2 cap3 z (f.foldl (f1 Q pool) ps) (!PJ)
      ((P ++ [true]).length + (f.flatMap recW).length + 1) (jh + 1)
    have hall := (((s1'.seq eS).seq s3).seq s4).seq s5
    refine (hall.enlarge (by unfold factorCost; omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp [head2, factorRec]
      all_goals omega
    · funext i; fin_cases i <;> rfl
  | false =>
    have e2 := skipPoly_run TT Jt cap cap2 cap3 z ps PJ (P ++ [true]) f post jh CB hCB
    have eS := branch_false (18 : Fin 20) fSelM e2 (by rw [← hb]; rfl)
    have s3 := nudgeV_step VT TT Jt cap cap2 cap3 z ps PJ ((P ++ [true]).length + (f.flatMap recW).length) jh
    have s4 := nudgeJ_step VT TT Jt cap cap2 cap3 z ps PJ ((P ++ [true]).length + (f.flatMap recW).length + 1) jh
    have s5 := nudgeJ_step VT TT Jt cap cap2 cap3 z ps PJ ((P ++ [true]).length + (f.flatMap recW).length + 1) (jh + 1)
    have hall := (((s1'.seq eS).seq s3).seq s4).seq s5
    refine (hall.enlarge (by unfold factorCost; omega)).congr ?_ ?_
    · funext i; fin_cases i <;> simp [head2, factorRec]
      all_goals omega
    · funext i; fin_cases i <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
