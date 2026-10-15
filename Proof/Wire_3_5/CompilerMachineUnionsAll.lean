import Proof.Wire_3_5.CompilerMachineUnionsRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The state of the loop over the monomials -/

/-- The entries with the scratch contents of the lift machine's tapes. -/
structure UState where
  E : List (List Bool)
  staleS : List Bool
  O : List Bool
  g : List Bool
  R : List Bool
  Z : List Bool
  Z2 : List Bool
  C : Bool

/-- Pass 1's final state for the monomial `gn`. -/
def ufin (Q W : ℕ) (st : UState) (gn : List Bool) : U1 := st.E.foldl (u1step Q W gn) ⟨[], st.R, st.Z, st.Z2, st.C⟩

/-- One monomial lifted. -/
def ustep (Q W : ℕ) (st : UState) (gn : List Bool) : UState :=
  ⟨liftStepW Q W st.E gn, (streamTape st.E st.staleS).drop (((liftStepW Q W st.E gn).flatMap frame).length + 1),
    streamTape (liftN Q W gn st.E) (st.O.drop (((liftN Q W gn st.E).flatMap frame).length + 1)), gn,
    (ufin Q W st gn).R, incrW Q W gn, (ufin Q W st gn).Z2, (ufin Q W st gn).C⟩

theorem foldl_ustep_E (Q W : ℕ) : ∀ (Gs : List (List Bool)) (st : UState),
    (Gs.foldl (ustep Q W) st).E = Gs.foldl (liftStepW Q W) st.E
  | [], _ => rfl
  | g :: Gs, st => by rw [List.foldl_cons, foldl_ustep_E Q W Gs, List.foldl_cons]; rfl

/-- The widths: every entry and every register has the entries' width. -/
def UInv (L : ℕ) (st : UState) : Prop :=
  (∀ r ∈ st.E, r.length = L) ∧ st.g.length = L ∧ U1Inv L ⟨[], st.R, st.Z, st.Z2, st.C⟩

theorem ustep_inv (Q W : ℕ) (hQ : 1 ≤ Q) (st : UState) (gn : List Bool) (hgn : gn.length = Q + W + 1)
    (h : UInv (Q + W + 1) st) : UInv (Q + W + 1) (ustep Q W st gn) := by
  obtain ⟨hE, _, h1⟩ := h
  have hf := foldl_u1step_inv Q W gn hgn hQ st.E ⟨[], st.R, st.Z, st.Z2, st.C⟩ hE h1
  obtain ⟨hR, _, hZ2⟩ := hf
  refine ⟨?_, hgn, hR, ?_, hZ2⟩
  · show ∀ r ∈ liftStepW Q W st.E gn, r.length = Q + W + 1
    rw [liftStepW_eq]
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hE r h
    · exact liftN_widths Q W gn hgn st.E hE r h
  · show (incrW Q W gn).length = Q + W + 1
    unfold incrW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hgn, levelT_length]), hgn]

theorem foldl_ustep_inv (Q W : ℕ) (hQ : 1 ≤ Q) : ∀ (Gs : List (List Bool)) (st : UState),
    (∀ g ∈ Gs, g.length = Q + W + 1) → UInv (Q + W + 1) st → UInv (Q + W + 1) (Gs.foldl (ustep Q W) st)
  | [], _, _, h => h
  | g :: Gs, st, hG, h => by
    rw [List.foldl_cons]
    exact foldl_ustep_inv Q W hQ Gs _ (fun g' hg' => hG g' (List.mem_cons_of_mem g hg'))
      (ustep_inv Q W hQ st g (hG g List.mem_cons_self) h)

theorem length_le_foldl_liftStepW (Q W : ℕ) : ∀ (Gs : List (List Bool)) (E : List (List Bool)),
    E.length ≤ (Gs.foldl (liftStepW Q W) E).length
  | [], _ => le_refl _
  | g :: Gs, E => by
    rw [List.foldl_cons]
    refine le_trans ?_ (length_le_foldl_liftStepW Q W Gs _)
    rw [liftStepW_eq, List.length_append]
    omega

theorem take_foldl_le (Q W : ℕ) (Gs E : List (List Bool)) (j : ℕ) :
    ((Gs.take j).foldl (liftStepW Q W) E).length ≤ (Gs.foldl (liftStepW Q W) E).length := by
  conv_rhs => rw [← List.take_append_drop j Gs, List.foldl_append]
  exact length_le_foldl_liftStepW Q W _ _

/-! ## The machines -/

def aLoadG : Fin 3 → Fin 13 := ![12, 2, 10]
def aNudgeG : Fin 1 → Fin 13 := ![12]
def aLift : Fin 12 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def aSel : Fin 13 → Bool := ![false, false, false, false, false, false, false, false, false, false, false, false, true]

noncomputable def aLoadGD := RecoveryFocus.machine aLoadG loadM
noncomputable def aNudgeGD := RecoveryFocus.machine aNudgeG nudgeM
noncomputable def aLiftD := RecoveryFocus.machine aLift uLiftM

/-- The loop body: load the next monomial's entry, step past it, lift it. -/
noncomputable def aBodyM := Composition.machine (Composition.machine aLoadGD aNudgeGD) aLiftD
noncomputable def aLoopM := StreamController.machine aBodyM 12

/-- **The unions machine**: the loop over the monomials, then their head back at cell 0. -/
noncomputable def unionsAllM := MaskedReset.machine aLoopM aSel

theorem aLoadG_inj : Function.Injective aLoadG := by decide

theorem install_aLoadG (A : Fin 13 → List Bool) (v : Fin 3 → List Bool) :
    install aLoadG A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 2, A 11, v 0] := by
  funext i
  fin_cases i
  · exact install_other aLoadG A v 0 (by decide)
  · exact install_other aLoadG A v 1 (by decide)
  · exact install_slot aLoadG aLoadG_inj A v 1
  · exact install_other aLoadG A v 3 (by decide)
  · exact install_other aLoadG A v 4 (by decide)
  · exact install_other aLoadG A v 5 (by decide)
  · exact install_other aLoadG A v 6 (by decide)
  · exact install_other aLoadG A v 7 (by decide)
  · exact install_other aLoadG A v 8 (by decide)
  · exact install_other aLoadG A v 9 (by decide)
  · exact install_slot aLoadG aLoadG_inj A v 2
  · exact install_other aLoadG A v 11 (by decide)
  · exact install_slot aLoadG aLoadG_inj A v 0

theorem dockH_aLoadG (H : Fin 13 → ℕ) (v : Fin 3 → ℕ) :
    dockH aLoadG H v = ![H 0, H 1, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 2, H 11, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other aLoadG H v 0 (by decide)
  · exact dockH_other aLoadG H v 1 (by decide)
  · exact dockH_slot aLoadG aLoadG_inj H v 1
  · exact dockH_other aLoadG H v 3 (by decide)
  · exact dockH_other aLoadG H v 4 (by decide)
  · exact dockH_other aLoadG H v 5 (by decide)
  · exact dockH_other aLoadG H v 6 (by decide)
  · exact dockH_other aLoadG H v 7 (by decide)
  · exact dockH_other aLoadG H v 8 (by decide)
  · exact dockH_other aLoadG H v 9 (by decide)
  · exact dockH_slot aLoadG aLoadG_inj H v 2
  · exact dockH_other aLoadG H v 11 (by decide)
  · exact dockH_slot aLoadG aLoadG_inj H v 0

theorem aNudgeG_inj : Function.Injective aNudgeG := by decide

theorem install_aNudgeG (A : Fin 13 → List Bool) (v : Fin 1 → List Bool) :
    install aNudgeG A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 0] := by
  funext i
  fin_cases i
  · exact install_other aNudgeG A v 0 (by decide)
  · exact install_other aNudgeG A v 1 (by decide)
  · exact install_other aNudgeG A v 2 (by decide)
  · exact install_other aNudgeG A v 3 (by decide)
  · exact install_other aNudgeG A v 4 (by decide)
  · exact install_other aNudgeG A v 5 (by decide)
  · exact install_other aNudgeG A v 6 (by decide)
  · exact install_other aNudgeG A v 7 (by decide)
  · exact install_other aNudgeG A v 8 (by decide)
  · exact install_other aNudgeG A v 9 (by decide)
  · exact install_other aNudgeG A v 10 (by decide)
  · exact install_other aNudgeG A v 11 (by decide)
  · exact install_slot aNudgeG aNudgeG_inj A v 0

theorem dockH_aNudgeG (H : Fin 13 → ℕ) (v : Fin 1 → ℕ) :
    dockH aNudgeG H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other aNudgeG H v 0 (by decide)
  · exact dockH_other aNudgeG H v 1 (by decide)
  · exact dockH_other aNudgeG H v 2 (by decide)
  · exact dockH_other aNudgeG H v 3 (by decide)
  · exact dockH_other aNudgeG H v 4 (by decide)
  · exact dockH_other aNudgeG H v 5 (by decide)
  · exact dockH_other aNudgeG H v 6 (by decide)
  · exact dockH_other aNudgeG H v 7 (by decide)
  · exact dockH_other aNudgeG H v 8 (by decide)
  · exact dockH_other aNudgeG H v 9 (by decide)
  · exact dockH_other aNudgeG H v 10 (by decide)
  · exact dockH_other aNudgeG H v 11 (by decide)
  · exact dockH_slot aNudgeG aNudgeG_inj H v 0

theorem aLift_inj : Function.Injective aLift := by decide

theorem install_aLift (A : Fin 13 → List Bool) (v : Fin 12 → List Bool) :
    install aLift A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, A 12] := by
  funext i
  fin_cases i
  · exact install_slot aLift aLift_inj A v 0
  · exact install_slot aLift aLift_inj A v 1
  · exact install_slot aLift aLift_inj A v 2
  · exact install_slot aLift aLift_inj A v 3
  · exact install_slot aLift aLift_inj A v 4
  · exact install_slot aLift aLift_inj A v 5
  · exact install_slot aLift aLift_inj A v 6
  · exact install_slot aLift aLift_inj A v 7
  · exact install_slot aLift aLift_inj A v 8
  · exact install_slot aLift aLift_inj A v 9
  · exact install_slot aLift aLift_inj A v 10
  · exact install_slot aLift aLift_inj A v 11
  · exact install_other aLift A v 12 (by decide)

theorem dockH_aLift (H : Fin 13 → ℕ) (v : Fin 12 → ℕ) :
    dockH aLift H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_slot aLift aLift_inj H v 0
  · exact dockH_slot aLift aLift_inj H v 1
  · exact dockH_slot aLift aLift_inj H v 2
  · exact dockH_slot aLift aLift_inj H v 3
  · exact dockH_slot aLift aLift_inj H v 4
  · exact dockH_slot aLift aLift_inj H v 5
  · exact dockH_slot aLift aLift_inj H v 6
  · exact dockH_slot aLift aLift_inj H v 7
  · exact dockH_slot aLift aLift_inj H v 8
  · exact dockH_slot aLift aLift_inj H v 9
  · exact dockH_slot aLift aLift_inj H v 10
  · exact dockH_slot aLift aLift_inj H v 11
  · exact dockH_other aLift H v 12 (by decide)

/-! ## One monomial -/

def aH (p : ℕ) : Fin 13 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p]

def aA (Gt : List Bool) (Q W cap cap2 : ℕ) (st : UState) : Fin 13 → List Bool :=
  ![streamTape st.E st.staleS, st.O, frame st.g, frame st.R, frame st.Z, frame st.Z2, frame (lastT Q W),
    frame (levelT Q W), frame (zeroT Q W), [st.C], List.replicate cap false, List.replicate cap2 false, Gt]

/-- The per-monomial cost bound, for entry lists of at most `n` entries of width `L`. -/
def aCost (n L : ℕ) : ℕ := 2 * (2 * L + 1) + 2 + 1 + 1 + 1 + liftCost n L

theorem pass1Cost_mono {n m : ℕ} (L : ℕ) (h : n ≤ m) : pass1Cost n L ≤ pass1Cost m L := by
  unfold pass1Cost
  have := Nat.mul_le_mul_right (uBodyCost L + 2) h
  omega

theorem appendCost_mono_left {n m : ℕ} (k L : ℕ) (h : n ≤ m) : appendCost n k L ≤ appendCost m k L := by
  unfold appendCost
  have := Nat.mul_le_mul_right (2 * L + 1 + 2) h
  omega

theorem liftCost_mono {n m : ℕ} (L : ℕ) (h : n ≤ m) : liftCost n L ≤ liftCost m L := by
  unfold liftCost
  have h1 := pass1Cost_mono L h
  have h2 := appendCost_mono_left (n + 1) L h
  have h3 := appendCost_mono m L (Nat.add_le_add_right h 1)
  omega

theorem a_body (pre gn post : List Bool) (Q W cap cap2 n : ℕ) (st : UState) (hQ : 1 ≤ Q)
    (hgn : gn.length = Q + W + 1) (h : UInv (Q + W + 1) st) (hn : st.E.length ≤ n)
    (hcap : 2 * (Q + W + 1) + 1 ≤ cap)
    (hcap2 : pass1Cost n (Q + W + 1) ≤ cap2 ∧ appendCost n (n + 1) (Q + W + 1) ≤ cap2) :
    Step aBodyM (aCost n (Q + W + 1)) (aH pre.length) (aA (pre ++ frame gn ++ post) Q W cap cap2 st)
      (aH (pre.length + (2 * gn.length + 1))) (aA (pre ++ frame gn ++ post) Q W cap cap2 (ustep Q W st gn)) := by
  obtain ⟨hE, hg, h1⟩ := h
  have e0 := loadStep pre gn post (frame st.g) cap (by omega)
  rw [overlay_exact _ _ (by simp [frame_length, hg, hgn])] at e0
  have s1 := dockRun e0 aLoadG aLoadG_inj (aH pre.length) (aA (pre ++ frame gn ++ post) Q W cap cap2 st)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_aLoadG, dockH_aLoadG] at s1
  have s2 := dockRun (nudge_run (pre ++ frame gn ++ post) (pre.length + 2 * gn.length)) aNudgeG aNudgeG_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pre.length + 2 * gn.length]
    ![streamTape st.E st.staleS, st.O, frame gn, frame st.R, frame st.Z, frame st.Z2, frame (lastT Q W),
      frame (levelT Q W), frame (zeroT Q W), [st.C], List.replicate cap false, List.replicate cap2 false,
      pre ++ frame gn ++ post] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_aNudgeG, dockH_aNudgeG] at s2
  have hl := lift_run st.E st.staleS st.O gn st.R st.Z st.Z2 st.C Q W cap cap2 hQ hE hgn h1 hcap
    ⟨(pass1Cost_mono (Q + W + 1) hn).trans hcap2.1,
      ((appendCost_mono_left (st.E.length + 1) (Q + W + 1) hn).trans
        (appendCost_mono n (Q + W + 1) (Nat.add_le_add_right hn 1))).trans hcap2.2⟩
  have s3 := dockKeep hl aLift aLift_inj ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pre.length + 2 * gn.length + 1]
    ![streamTape st.E st.staleS, st.O, frame gn, frame st.R, frame st.Z, frame st.Z2, frame (lastT Q W),
      frame (levelT Q W), frame (zeroT Q W), [st.C], List.replicate cap false, List.replicate cap2 false,
      pre ++ frame gn ++ post] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_aLift] at s3
  have hall := (s1.seq s2).seq s3
  refine (hall.enlarge ?_).congr ?_ rfl
  · unfold aCost
    have := liftCost_mono (Q + W + 1) hn
    rw [hgn] at *
    omega
  · funext i; fin_cases i <;> simp [aH]
    all_goals omega

/-! ## The loop over the monomials, and its reset -/

theorem a_loop (Gs : List (List Bool)) (staleG : List Bool) (Q W cap cap2 : ℕ) (s0 : UState) (hQ : 1 ≤ Q)
    (hG : ∀ g ∈ Gs, g.length = Q + W + 1) (h0 : UInv (Q + W + 1) s0) (hcap : 2 * (Q + W + 1) + 1 ≤ cap)
    (hcap2 : pass1Cost (Gs.foldl (liftStepW Q W) s0.E).length (Q + W + 1) ≤ cap2 ∧
      appendCost (Gs.foldl (liftStepW Q W) s0.E).length ((Gs.foldl (liftStepW Q W) s0.E).length + 1) (Q + W + 1)
        ≤ cap2) :
    Step aLoopM (Gs.length * (aCost (Gs.foldl (liftStepW Q W) s0.E).length (Q + W + 1) + 2) + 1) (aH 0)
      (aA (streamTape Gs staleG) Q W cap cap2 s0) (aH (Gs.flatMap frame).length)
      (aA (streamTape Gs staleG) Q W cap cap2 (Gs.foldl (ustep Q W) s0)) := by
  refine streamRun aBodyM 12 Gs staleG (fun r hr h => by have := hG r hr; rw [h] at this; simp at this)
    (ustep Q W) s0 (fun _ p => aH p) (fun st => aA (streamTape Gs staleG) Q W cap cap2 st) (fun _ => rfl)
    (fun _ _ => rfl) (aCost (Gs.foldl (liftStepW Q W) s0.E).length (Q + W + 1)) ?_
  intro j hj
  have hlen := hG _ (List.getElem_mem hj)
  have hst : (Gs.take (j + 1)).foldl (ustep Q W) s0 = ustep Q W ((Gs.take j).foldl (ustep Q W) s0) Gs[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  have hinv := foldl_ustep_inv Q W hQ (Gs.take j) s0 (fun g hg => hG g (List.mem_of_mem_take hg)) h0
  have hn : ((Gs.take j).foldl (ustep Q W) s0).E.length ≤ (Gs.foldl (liftStepW Q W) s0.E).length := by
    rw [foldl_ustep_E]; exact take_foldl_le Q W Gs s0.E j
  have hb := a_body ((Gs.take j).flatMap frame) Gs[j] ((Gs.drop (j + 1)).flatMap frame ++ false :: staleG) Q W cap cap2
    (Gs.foldl (liftStepW Q W) s0.E).length ((Gs.take j).foldl (ustep Q W) s0) hQ hlen hinv hn hcap hcap2
  rw [← streamTape_split Gs staleG j hj] at hb
  rw [hst, off_succ Gs j hj]
  exact hb

/-- The cost of lifting `m` monomials of width `L`, with at most `N` entries at the end. -/
def unionsCost (m N L : ℕ) : ℕ := 2 * (m * (aCost N L + 2) + 1) + 2

/-- **Every monomial lifted**: the entries' stream on tape 0 becomes `Gs.foldl (liftStepW Q W) E`
(`foldl_ustep_E`), every head back at cell 0. -/
theorem unionsAll_run (Gs : List (List Bool)) (staleG : List Bool) (Q W cap cap2 cap3 : ℕ) (s0 : UState) (hQ : 1 ≤ Q)
    (hG : ∀ g ∈ Gs, g.length = Q + W + 1) (h0 : UInv (Q + W + 1) s0) (hcap : 2 * (Q + W + 1) + 1 ≤ cap)
    (hcap2 : pass1Cost (Gs.foldl (liftStepW Q W) s0.E).length (Q + W + 1) ≤ cap2 ∧
      appendCost (Gs.foldl (liftStepW Q W) s0.E).length ((Gs.foldl (liftStepW Q W) s0.E).length + 1) (Q + W + 1)
        ≤ cap2)
    (hcap3 : Gs.length * (aCost (Gs.foldl (liftStepW Q W) s0.E).length (Q + W + 1) + 2) + 1 ≤ cap3) :
    Step unionsAllM (unionsCost Gs.length (Gs.foldl (liftStepW Q W) s0.E).length (Q + W + 1)) (fun _ => 0)
      ![streamTape s0.E s0.staleS, s0.O, frame s0.g, frame s0.R, frame s0.Z, frame s0.Z2, frame (lastT Q W),
        frame (levelT Q W), frame (zeroT Q W), [s0.C], List.replicate cap false, List.replicate cap2 false,
        streamTape Gs staleG, List.replicate cap3 false]
      (fun _ => 0)
      ![streamTape (Gs.foldl (ustep Q W) s0).E (Gs.foldl (ustep Q W) s0).staleS, (Gs.foldl (ustep Q W) s0).O,
        frame (Gs.foldl (ustep Q W) s0).g, frame (Gs.foldl (ustep Q W) s0).R, frame (Gs.foldl (ustep Q W) s0).Z,
        frame (Gs.foldl (ustep Q W) s0).Z2, frame (lastT Q W), frame (levelT Q W), frame (zeroT Q W),
        [(Gs.foldl (ustep Q W) s0).C], List.replicate cap false, List.replicate cap2 false, streamTape Gs staleG,
        List.replicate cap3 false] := by
  have h := a_loop Gs staleG Q W cap cap2 s0 hQ hG h0 hcap hcap2
  have hm := h.mask aSel (by intro i hi; fin_cases i <;> simp_all [aSel, aH]) hcap3
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

theorem unions_run (G : List ℕ) (Q W : ℕ) (staleS O g R Z Z2 staleG : List Bool) (C : Bool) (cap cap2 cap3 : ℕ)
    (hQ : 1 ≤ Q) (hg : g.length = Q + W + 1) (h1 : U1Inv (Q + W + 1) ⟨[], R, Z, Z2, C⟩)
    (hcap : 2 * (Q + W + 1) + 1 ≤ cap)
    (hcap2 : pass1Cost (CompilerMachine.unionsM Q G).length (Q + W + 1) ≤ cap2 ∧
      appendCost (CompilerMachine.unionsM Q G).length ((CompilerMachine.unionsM Q G).length + 1) (Q + W + 1) ≤ cap2)
    (hcap3 : G.length * (aCost (CompilerMachine.unionsM Q G).length (Q + W + 1) + 2) + 1 ≤ cap3) :
    ∃ fin : UState, fin.E = (CompilerMachine.unionsM Q G).map (ew Q W) ∧
      Step unionsAllM (unionsCost G.length (CompilerMachine.unionsM Q G).length (Q + W + 1)) (fun _ => 0)
        ![streamTape [] staleS, O, frame g, frame R, frame Z, frame Z2, frame (lastT Q W), frame (levelT Q W),
          frame (zeroT Q W), [C], List.replicate cap false, List.replicate cap2 false,
          streamTape (G.map fun u => ew Q W (0, u)) staleG, List.replicate cap3 false]
        (fun _ => 0)
        ![streamTape fin.E fin.staleS, fin.O, frame fin.g, frame fin.R, frame fin.Z, frame fin.Z2, frame (lastT Q W),
          frame (levelT Q W), frame (zeroT Q W), [fin.C], List.replicate cap false, List.replicate cap2 false,
          streamTape (G.map fun u => ew Q W (0, u)) staleG, List.replicate cap3 false] := by
  set Gs := G.map fun u => ew Q W (0, u)
  have hw := unionsM_words Q W hQ G
  have hN : (Gs.foldl (liftStepW Q W) []).length = (CompilerMachine.unionsM Q G).length := by
    rw [← hw, List.length_map]
  have hG : ∀ x ∈ Gs, x.length = Q + W + 1 := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact entryWord_length Q W 0 u (by omega)
  let s0 : UState := ⟨[], staleS, O, g, R, Z, Z2, C⟩
  have h0 : UInv (Q + W + 1) s0 := ⟨by simp [s0], hg, h1⟩
  have h := unionsAll_run Gs staleG Q W cap cap2 cap3 s0 hQ hG h0 hcap
    (by show pass1Cost (Gs.foldl (liftStepW Q W) []).length (Q + W + 1) ≤ cap2 ∧ _; rw [hN]; exact hcap2)
    (by show Gs.length * (aCost (Gs.foldl (liftStepW Q W) []).length (Q + W + 1) + 2) + 1 ≤ cap3
        rw [hN, List.length_map]; exact hcap3)
  refine ⟨Gs.foldl (ustep Q W) s0, ?_, ?_⟩
  · rw [foldl_ustep_E]; exact hw.symm
  · have e : (Gs.foldl (liftStepW Q W) s0.E).length = (CompilerMachine.unionsM Q G).length := hN
    rw [e, List.length_map] at h
    exact h

end NearCubicWires.WireExponent3_5.CompilerMachine.Unions
