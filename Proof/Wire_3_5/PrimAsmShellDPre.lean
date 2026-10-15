import Proof.Wire_3_5.PrimAsmShellDData
import Proof.Wire_3_5.PrimAsmReqBridge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.SupplierPipeline

section Pre
variable {x D D1 D2 : ℕ}

/-- **The data stage's size hypotheses at width `V`** (`Data.data_step`'s, with `L = W = V`). -/
structure DataOK {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (V : ℕ) : Prop where
  ha : a' ≤ 4
  hk : carriers.length ≤ 2
  hL : ∀ i, (Cs i).descriptionBits ≤ V
  hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ V
  h2 : 2 ≤ n + V
  hcN : natBitLength n + 1 ≤ 2 * V + 2
  hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2
  hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * V + 2
  hcx : ∀ y ∈ Data.symCodes a' Cs, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2
  hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2
  hcu : 2 * (Data.unaryList (carriers.map (·.length))).length +
    2 * (Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * V + 2

/-- The request word starts with `natWord n`. -/
theorem reqW_natWord (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    Data.reqW n mb codes cc tl = RepairRepresentation.natWord n ++ ([mb] ++ RepairRepresentation.natWord codes.length ++
      codes.flatMap RepairRepresentation.natWord ++ RepairRepresentation.natListWord cc ++ tl) := by
  simp only [Data.reqW, List.append_assoc]

theorem e1T_ne_low (k : Fin (E1 D1)) (i : Fin (STd x D D1 D2)) (h : i.val < (TT x + 1 + Scrub.wk D + 3)) :
    e1T (x := x) (D := D) (D2 := D2) k ≠ i := by
  apply ne_of_val
  rw [e1T_val]
  omega

theorem e2T_ne_low (k : Fin (E2 D2)) (i : Fin (STd x D D1 D2)) (h : i.val < (TT x + 1 + Scrub.wk D + 3)) :
    e2T (x := x) (D := D) (D1 := D1) k ≠ i := by
  apply ne_of_val
  rw [e2T_val]
  omega

theorem e3T_ne_low (k : Fin E3) (i : Fin (STd x D D1 D2)) (h : i.val < (TT x + 1 + Scrub.wk D + 3)) :
    e3T (x := x) (D := D) (D1 := D1) (D2 := D2) k ≠ i := by
  apply ne_of_val
  rw [e3T_val]
  omega

theorem p2Slots_val_ge (k : Fin (UnaryCalc.tapes D2)) : (TT x + 1 + Scrub.wk D + 3) ≤ (p2Slots x D D1 D2 k).val := by
  unfold p2Slots
  split_ifs
  · rw [e1T_val]; omega
  · rw [e2T_val]; omega

theorem cpSlots2_val_ge (j : Fin 4) : (TT x + 1 + Scrub.wk D + 3) + E1 D1 ≤ (cpSlots2 x D D1 D2 j).val := by
  rw [cpSlots2_val]
  omega

theorem p2Slots_ne_low (k : Fin (UnaryCalc.tapes D2)) (i : Fin (STd x D D1 D2)) (h : i.val < (TT x + 1 + Scrub.wk D + 3)) :
    p2Slots x D D1 D2 k ≠ i := by
  apply ne_of_val
  have := p2Slots_val_ge (x := x) (D := D) (D1 := D1) (D2 := D2) k
  omega

theorem cpSlots2_ne_low (j : Fin 4) (i : Fin (STd x D D1 D2)) (h : i.val < (TT x + 1 + Scrub.wk D + 3) + E1 D1) :
    cpSlots2 x D D1 D2 j ≠ i := by
  apply ne_of_val
  have := cpSlots2_val_ge (x := x) (D := D) (D1 := D1) (D2 := D2) j
  omega

theorem dataSlots_ne_low (j : Fin E3) (i : Fin (STd x D D1 D2)) (h : i.val < (TT x + 1 + Scrub.wk D + 3))
    (h0 : i ≠ cs 0) (hd : i ≠ dT) : dataSlots x D D1 D2 j ≠ i := by
  unfold dataSlots
  split_ifs
  · exact fun e => h0 e.symm
  · exact e1T_ne_low _ i h
  · exact e2T_ne_low _ i h
  · exact fun e => hd e.symm
  · exact e3T_ne_low _ i h

theorem kT_val_lt : (kT (x := x) (D := D) (D1 := D1) (D2 := D2)).val < (TT x + 1 + Scrub.wk D + 3) := by
  rw [kT_val]
  omega

theorem dataSlots_ne_kT (j : Fin E3) : dataSlots x D D1 D2 j ≠ kT := by
  have hc0 : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 0).val = 0 := rfl
  have hT : 674 ≤ TT x := by unfold TT LNS LNR; omega
  unfold dataSlots
  split_ifs
  · apply ne_of_val; rw [hc0, kT_val]; omega
  · apply ne_of_val; rw [e1T_val, kT_val]; omega
  · apply ne_of_val; rw [e2T_val, kT_val]; omega
  · apply ne_of_val; rw [dT_val, kT_val]; omega
  · apply ne_of_val; rw [e3T_val, kT_val]; omega

theorem p2_out : p2Slots x D D1 D2 (UnaryCalc.outputTape D2) = e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2)) := by
  unfold p2Slots
  rw [if_neg]
  intro h
  have := congrArg Fin.val h
  rw [outTape_val, inTape_val] at this
  omega

theorem p2_in : p2Slots x D D1 D2 (UnaryCalc.inputTape D2) = e1T (UnaryCalc.inputTape D1) := by
  unfold p2Slots
  rw [if_pos rfl]

theorem data_in : dataSlots x D D1 D2 inPos = cs 0 := by
  unfold dataSlots
  rw [if_pos rfl]

theorem data_out : dataSlots x D D1 D2 outPos = dT := by
  unfold dataSlots
  rw [if_neg (ne_of_val (by rw [outPos_val, inPos_val]; omega)), if_neg (ne_of_val (by rw [outPos_val, ntPos_val]; omega)),
    if_neg (ne_of_val (by rw [outPos_val, ltPos_val]; omega)), if_pos rfl]

/-- The heads during the data phase: the counter's at `1`, all else at `0`. -/
def hK (x D D1 D2 : ℕ) : Fin (STd x D D1 D2) → ℕ := fun i => if i = kT then 1 else 0

theorem hK_low (i : Fin (STd x D D1 D2)) (h : (TT x + 1 + Scrub.wk D + 3) ≤ i.val) : hK x D D1 D2 i = 0 := by
  unfold hK
  rw [if_neg]
  intro e
  subst e
  have := kT_val_lt (x := x) (D := D) (D1 := D1) (D2 := D2)
  omega

/-- The boot and the data phase. -/
noncomputable def preM (x D D1 D2 C1 C2 : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (bootM x D D1 D2 C1) (M6 x D D1 D2 C2))
    (M7 x D D1 D2)) (M8 x D D1 D2)

/-- The boot and data phase's cost (`cc` the data stage's core cost). -/
def preCost (w : List Bool) (n D1 C1 D2 C2 cc : ℕ) : ℕ :=
  bootCost w n D1 C1 + 1 + PCPSerializerCapacity.Power.budget D2 C2 n + 1 + (2 * UnaryCalc.value D2 C2 n + 6) + 1 +
    (2 * cc + 2)

theorem p2Slots_val_lt (k : Fin (UnaryCalc.tapes D2)) :
    (p2Slots x D D1 D2 k).val < TT x + 1 + Scrub.wk D + 3 + E1 D1 + E2 D2 := by
  have hE2 : E2 D2 = UnaryCalc.tapes D2 + 2 := rfl
  have hE1 : E1 D1 = UnaryCalc.tapes D1 := rfl
  unfold p2Slots
  split_ifs
  · rw [e1T_val]
    have := (UnaryCalc.inputTape D1).isLt
    omega
  · rw [e2T_val]
    simp only [Fin.val_castAdd]
    have := k.isLt
    omega

theorem p2Slots_ne_e3T (k : Fin (UnaryCalc.tapes D2)) (j : Fin E3) : p2Slots x D D1 D2 k ≠ e3T j := by
  apply ne_of_val
  have := p2Slots_val_lt (x := x) (D := D) (D1 := D1) (D2 := D2) k
  rw [e3T_val]
  omega

theorem p2Slots_ne_e2n (k : Fin (UnaryCalc.tapes D2)) (b : Fin 2) :
    p2Slots x D D1 D2 k ≠ e2T (Fin.natAdd (UnaryCalc.tapes D2) b) := by
  unfold p2Slots
  split_ifs
  · exact e1T_ne_e2T _ _
  · intro e
    have := congrArg Fin.val (e2T_inj e)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := k.isLt
    omega

theorem cpSlots2_ne_e3T (m : Fin 4) (j : Fin E3) (hj : j ≠ ctPos) : cpSlots2 x D D1 D2 m ≠ e3T j := by
  fin_cases m
  · exact e2T_ne_e3T _ _
  · exact e2T_ne_e3T _ _
  · exact fun e => hj (e3T_inj e).symm
  · exact e2T_ne_e3T _ _

theorem e1T_lt (k : Fin (E1 D1)) :
    (e1T (x := x) (D := D) (D2 := D2) k).val < TT x + 1 + Scrub.wk D + 3 + E1 D1 := by
  rw [e1T_val]
  have := k.isLt
  omega

/-- **The boot and the data phase as one run**: from the writer's entry bank on the call's request word, the loop's
entry data (request kept, `OUT = [false]`, unit counter blank, workspace `Scrub.calcIn D n`, log and driver blank,
counter `word b`) and the DATA TAPE `Data.dataWord (Data.symCounts a' Cs carriers)`; the cell's scratch within the
boot's cost. -/
theorem pre_step {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (C1 C2 : ℕ)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n)) :
    ∃ B8 : Fin (STd x D D1 D2) → List Bool,
      Step (preM x D D1 D2 C1 C2) (preCost w n D1 C1 D2 C2
          (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)))
        (fun _ => 0) (B0 w) (hK x D D1 D2) B8 ∧
      B8 (cs 0) = frame w ∧ B8 (cs 1) = [false] ∧ B8 (cs 2) = [] ∧ (∀ j, B8 (wT j) = Scrub.calcIn D n j) ∧
      B8 lgT = [] ∧ B8 drT = [] ∧
      B8 kT = RepairSource.VerifierDecoding.CompareMachine.word (UnaryCalc.value D1 C1 n) ∧
      B8 dT = Data.dataWord (Data.symCounts a' Cs carriers) ∧
      (∀ c, kept x c = false → (B8 (cT c)).length ≤ bootCost w n D1 C1) := by
  have hT : 674 ≤ TT x := by unfold TT LNS LNR; omega
  obtain ⟨B5, sb, h0, h1, h2, hwk, hl, hd, hkk, hdt, hin, hhi⟩ :=
    boot_step (x := x) (D := D) (D1 := D1) (D2 := D2) w _ n C1 (hw.trans (reqW_natWord _ _ _ _ _))
  set V := UnaryCalc.value D2 C2 n with hV
  -- stage 6: `1^V`
  obtain ⟨out6, s6, o6i, o6o⟩ := st6 (x := x) (D := D) (D1 := D1) (D2 := D2) C2 n (hK x D D1 D2) B5
    (fun k => hK_low _ (p2Slots_val_ge k)) hin
    (fun k _ => hhi _ (by rw [e2T_val]; omega))
  set B6 := install (p2Slots x D D1 D2) B5 out6 with hB6
  have b6other : ∀ i, (∀ k, p2Slots x D D1 D2 k ≠ i) → B6 i = B5 i := fun i hi => install_other _ _ _ _ hi
  have b6o : B6 (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true := by
    have e := install_slot (p2Slots x D D1 D2) p2Slots_inj B5 out6 (UnaryCalc.outputTape D2)
    rw [p2_out] at e
    rw [hB6, e, o6o]
  have b6i : B6 (e1T (UnaryCalc.inputTape D1)) = List.replicate n true := by
    have e := install_slot (p2Slots x D D1 D2) p2Slots_inj B5 out6 (UnaryCalc.inputTape D2)
    rw [p2_in] at e
    rw [hB6, e, o6i]
  -- stage 7: a second `1^V`
  have s7 := st7 (x := x) (D := D) (D1 := D1) (D2 := D2) V (hK x D D1 D2) B6
    (fun k => hK_low _ (by have := cpSlots2_val_ge (x := x) (D := D) (D1 := D1) (D2 := D2) k; omega)) b6o
    (by rw [b6other _ (fun k => p2Slots_ne_e2n k 0)]; exact hhi _ (by rw [e2T_val]; omega))
    (by rw [b6other _ (fun k => p2Slots_ne_e3T k ctPos)]; exact hhi _ (by rw [e3T_val]; omega))
    (by rw [b6other _ (fun k => p2Slots_ne_e2n k 1)]; exact hhi _ (by rw [e2T_val]; omega))
  set B7 := install (cpSlots2 x D D1 D2) B6
    ![List.replicate V true, [], List.replicate V true, List.replicate (V + 2) false] with hB7
  have b7other : ∀ i, (∀ m, cpSlots2 x D D1 D2 m ≠ i) → B7 i = B6 i := fun i hi => install_other _ _ _ _ hi
  have low7 : ∀ i : Fin (STd x D D1 D2), i.val < TT x + 1 + Scrub.wk D + 3 → B7 i = B5 i := by
    intro i hi
    rw [b7other _ (fun m => cpSlots2_ne_low m i (by omega)), b6other _ (fun k => p2Slots_ne_low k i hi)]
  have hc0 : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 0).val = 0 := rfl
  have b7cs0 : B7 (cs 0) = frame (Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) := by
    rw [low7 _ (by rw [hc0]; omega), h0, hw]
  have b7nt : B7 (e1T (UnaryCalc.inputTape D1)) = List.replicate n true := by
    rw [b7other _ (fun m => cpSlots2_ne_low m _ (e1T_lt _)), b6i]
  have b7lt : B7 (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true := by
    have e := install_slot (cpSlots2 x D D1 D2) cpSlots2_inj B6
      ![List.replicate V true, [], List.replicate V true, List.replicate (V + 2) false] 0
    rw [hB7]
    exact e
  have b7out : B7 dT = [] := by
    rw [low7 _ (by rw [dT_val]; omega), hdt]
  have b7ct : B7 (e3T ctPos) = List.replicate V true := by
    have e := install_slot (cpSlots2 x D D1 D2) cpSlots2_inj B6
      ![List.replicate V true, [], List.replicate V true, List.replicate (V + 2) false] 2
    rw [hB7]
    exact e
  have b7rest : ∀ j, j ≠ inPos → j ≠ ntPos → j ≠ ltPos → j ≠ outPos → j ≠ ctPos → B7 (e3T j) = [] := by
    intro j _ _ _ _ hj
    rw [b7other _ (fun m => cpSlots2_ne_e3T m j hj), b6other _ (fun k => p2Slots_ne_e3T k j)]
    exact hhi _ (by rw [e3T_val]; omega)
  -- stage 8: the data stage
  obtain ⟨tout, m8, s8, t8o, t8i⟩ := st8 (x := x) (D := D) (D1 := D1) (D2 := D2) a' Cs carriers tl V (hK x D D1 D2) B7
    (fun j => by unfold hK; rw [if_neg (dataSlots_ne_kT j)]) b7cs0 b7nt b7lt b7out b7ct b7rest
    hD.ha hD.hk hD.hL hD.hLX hD.h2 hD.hcN hD.hcA hD.hcK hD.hcx hD.hcy hD.hcu
  set B8 := install (dataSlots x D D1 D2) B7 (Fin.addCases tout (fun _ : Fin 1 => List.replicate m8 false)) with hB8
  have low8 : ∀ i : Fin (STd x D D1 D2), i.val < TT x + 1 + Scrub.wk D + 3 → i ≠ cs 0 → i ≠ dT → B8 i = B5 i := by
    intro i hi hi0 hid
    rw [hB8, install_other _ _ _ _ (fun j => dataSlots_ne_low j i hi hi0 hid), low7 i hi]
  have ncs0 : ∀ i : Fin (STd x D D1 D2), 0 < i.val → i ≠ cs 0 := fun i h e => by
    rw [e, hc0] at h
    omega
  have ndT : ∀ i : Fin (STd x D D1 D2), i.val ≠ TT x → i ≠ dT := fun i h e => by
    rw [e, dT_val] at h
    exact h rfl
  refine ⟨B8, ((sb.seq s6).seq s7).seq s8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := install_slot (dataSlots x D D1 D2) dataSlots_inj B7 (Fin.addCases tout (fun _ : Fin 1 => List.replicate m8 false))
      inPos
    rw [data_in] at e
    rw [hB8, e, hw]
    exact t8i
  · have h1v : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1).val = 2 := rfl
    rw [low8 _ (by rw [h1v]; omega) (ncs0 _ (by rw [h1v]; omega)) (ndT _ (by rw [h1v]; omega)), h1]
  · have h2v : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 2).val = 3 := rfl
    rw [low8 _ (by rw [h2v]; omega) (ncs0 _ (by rw [h2v]; omega)) (ndT _ (by rw [h2v]; omega)), h2]
  · intro j
    have := j.isLt
    rw [low8 _ (by rw [wT_val]; omega) (ncs0 _ (by rw [wT_val]; omega)) (ndT _ (by rw [wT_val]; omega)), hwk j]
  · rw [low8 _ (by rw [lgT_val]; omega) (ncs0 _ (by rw [lgT_val]; omega)) (ndT _ (by rw [lgT_val]; omega)), hl]
  · rw [low8 _ (by rw [drT_val]; omega) (ncs0 _ (by rw [drT_val]; omega)) (ndT _ (by rw [drT_val]; omega)), hd]
  · rw [low8 _ (by rw [kT_val]; omega) (ncs0 _ (by rw [kT_val]; omega)) (ndT _ (by rw [kT_val]; omega)), hkk]
  · have e := install_slot (dataSlots x D D1 D2) dataSlots_inj B7 (Fin.addCases tout (fun _ : Fin 1 => List.replicate m8 false))
      outPos
    rw [data_out] at e
    rw [hB8, e]
    exact t8o
  · intro c hc
    have hne : cT (x := x) (D := D) (D1 := D1) (D2 := D2) c ≠ cs 0 := by
      intro e
      have e' : c = sTape (sk x 0) := cT_inj e
      subst e'
      simp [kept] at hc
    have hlt := c.isLt
    rw [low8 _ (by rw [cT_val]; omega) hne (ndT _ (by rw [cT_val]; omega))]
    have := Shell.Step.len sb (cT c) 0 (le_refl _) (by simp [B0, hne])
    omega

end Pre

end NearCubicWires.WireExponent3_5.PrimAsm.ShellD
