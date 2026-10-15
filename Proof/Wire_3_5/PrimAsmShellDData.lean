import Proof.Wire_3_5.PrimAsmShellDBoot

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
open NearCubicWires.WireExponent3_5.PrimAsm.Shell (install_eq dockH_eq)

section Data
variable {x D D1 D2 : ℕ}

theorem outTape_val (d : ℕ) : (UnaryCalc.outputTape d).val = 3 + 2 * d := rfl
theorem inTape_val (d : ℕ) : (UnaryCalc.inputTape d).val = 0 := rfl
theorem tapes_ge (d : ℕ) : 14 ≤ UnaryCalc.tapes d := by
  show 14 ≤ 14 + 2 * d
  omega
theorem outTape_lt (d : ℕ) : 3 + 2 * d < UnaryCalc.tapes d := by
  show 3 + 2 * d < 14 + 2 * d
  omega

/-! ## Stage 6: the width `V = C₂(n+1)^{D₂}` -/

/-- The width run's tapes: its input on the bound run's input (`1^n`), the rest in the second region. -/
def p2Slots (x D D1 D2 : ℕ) (k : Fin (UnaryCalc.tapes D2)) : Fin (STd x D D1 D2) :=
  if k = UnaryCalc.inputTape D2 then e1T (UnaryCalc.inputTape D1) else e2T (Fin.castAdd 2 k)

theorem e1T_ne_e2T (a : Fin (E1 D1)) (b : Fin (E2 D2)) : e1T (x := x) (D := D) (D2 := D2) a ≠ e2T (D1 := D1) b := by
  apply ne_of_val
  rw [e1T_val, e2T_val]
  have := a.isLt
  omega

theorem p2Slots_inj : Function.Injective (p2Slots x D D1 D2) := by
  intro a b h
  unfold p2Slots at h
  split_ifs at h with ha hb hb
  · rw [ha, hb]
  · exact absurd h (e1T_ne_e2T _ _)
  · exact absurd h.symm (e1T_ne_e2T _ _)
  · have := e2T_inj h
    exact Fin.castAdd_injective _ _ this

noncomputable def M6 (x D D1 D2 C2 : ℕ) :=
  RecoveryFocus.machine (p2Slots x D D1 D2) (PCPSerializerCapacity.Power.machine D2 C2)

theorem st6 (C2 n : ℕ) (H : Fin (STd x D D1 D2) → ℕ) (Bin : Fin (STd x D D1 D2) → List Bool)
    (hH : ∀ k, H (p2Slots x D D1 D2 k) = 0)
    (hin : Bin (e1T (UnaryCalc.inputTape D1)) = List.replicate n true)
    (hb : ∀ k : Fin (UnaryCalc.tapes D2), k ≠ UnaryCalc.inputTape D2 → Bin (e2T (Fin.castAdd 2 k)) = []) :
    ∃ out : Fin (UnaryCalc.tapes D2) → List Bool,
      Step (M6 x D D1 D2 C2) (PCPSerializerCapacity.Power.budget D2 C2 n) H Bin H
        (install (p2Slots x D D1 D2) Bin out) ∧ out (UnaryCalc.inputTape D2) = List.replicate n true ∧
        out (UnaryCalc.outputTape D2) = List.replicate (UnaryCalc.value D2 C2 n) true := by
  obtain ⟨out, h, hi, ho⟩ := UnaryCalc.poly_step D2 C2 n
  have d := Rec.dockRun h (p2Slots x D D1 D2) p2Slots_inj H Bin (fun k => hH k) (by
    intro k
    unfold p2Slots
    by_cases hk : k = UnaryCalc.inputTape D2
    · rw [if_pos hk, hin, hk]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · rw [if_neg hk, hb k hk]
      have hv : k.val ≠ 0 := fun e => hk (Fin.ext e)
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hv])
  exact ⟨out, d.congr (dockH_eq _ p2Slots_inj _ _ _ (fun k => hH k) (fun _ _ => rfl)) rfl, hi, ho⟩

/-! ## Stage 7: a second copy of `1^V` -/

/-- The data stage's fill-count stream, in its own layout. -/
def ctPos : Fin E3 := Fin.castAdd 1 (sTape (nr := Data.DR) Data.sCT)

/-- The copier's tapes: the width, a scratch, the data stage's fill count, a scratch log. -/
def cpSlots2 (x D D1 D2 : ℕ) : Fin 4 → Fin (STd x D D1 D2) :=
  ![e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2)), e2T (Fin.natAdd (UnaryCalc.tapes D2) 0), e3T ctPos,
    e2T (Fin.natAdd (UnaryCalc.tapes D2) 1)]

theorem e2T_ne_e3T (a : Fin (E2 D2)) (b : Fin E3) : e2T (x := x) (D := D) (D1 := D1) a ≠ e3T b := by
  apply ne_of_val
  rw [e2T_val, e3T_val]
  have := a.isLt
  omega

theorem ctPos_val : ctPos.val = 4 := rfl

/-- The copier's tape values, relative to the second region's start. -/
def cpv (D2 : ℕ) : Fin 4 → ℕ := ![3 + 2 * D2, UnaryCalc.tapes D2, UnaryCalc.tapes D2 + 2 + 4, UnaryCalc.tapes D2 + 1]

theorem cpSlots2_val (j : Fin 4) :
    (cpSlots2 x D D1 D2 j).val = TT x + 1 + Scrub.wk D + 3 + E1 D1 + cpv D2 j := by
  have hE2 : E2 D2 = UnaryCalc.tapes D2 + 2 := rfl
  fin_cases j
  · simp [cpSlots2, e2T_val, cpv, outTape_val]
  · simp [cpSlots2, e2T_val, cpv]
  · simp [cpSlots2, e3T_val, cpv, ctPos_val, hE2]; omega
  · simp [cpSlots2, e2T_val, cpv]

theorem cpSlots2_inj : Function.Injective (cpSlots2 x D D1 D2) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [cpSlots2_val, cpSlots2_val] at hv
  have ho := outTape_lt D2
  have hv' : cpv D2 a = cpv D2 b := by omega
  fin_cases a <;> fin_cases b <;> simp [cpv] at hv' ⊢ <;> omega

noncomputable def M7 (x D D1 D2 : ℕ) := RecoveryFocus.machine (cpSlots2 x D D1 D2) ClockUnarySum.machine

theorem st7 (V : ℕ) (H : Fin (STd x D D1 D2) → ℕ) (Bin : Fin (STd x D D1 D2) → List Bool)
    (hH : ∀ k, H (cpSlots2 x D D1 D2 k) = 0) (hs : Bin (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true)
    (h1 : Bin (e2T (Fin.natAdd (UnaryCalc.tapes D2) 0)) = []) (h2 : Bin (e3T ctPos) = [])
    (h3 : Bin (e2T (Fin.natAdd (UnaryCalc.tapes D2) 1)) = []) :
    Step (M7 x D D1 D2) (2 * V + 6) H Bin H
      (install (cpSlots2 x D D1 D2) Bin ![List.replicate V true, [], List.replicate V true,
        List.replicate (V + 2) false]) := by
  have d := Rec.dockRun (UnaryCalc.copy_step V) (cpSlots2 x D D1 D2) cpSlots2_inj H Bin (fun k => hH k) (by
    intro k
    fin_cases k
    · exact hs
    · exact h1
    · exact h2
    · exact h3)
  exact d.congr (dockH_eq _ cpSlots2_inj _ _ _ (fun k => hH k) (fun _ _ => rfl)) rfl

/-! ## Stage 8: the per-call data stage -/

def inPos : Fin E3 := Fin.castAdd 1 (sTape (nr := Data.DR) Data.sIN)
def ntPos : Fin E3 := Fin.castAdd 1 (sTape (nr := Data.DR) Data.sNT)
def ltPos : Fin E3 := Fin.castAdd 1 (sTape (nr := Data.DR) Data.sLT)
def outPos : Fin E3 := Fin.castAdd 1 (sTape (nr := Data.DR) Data.sOUT)

/-- The data stage's tapes: its request on the cell's request, `1^n` on the bound run's input, `1^L` on the width
run's output, its output on the data tape, the rest in the third region. -/
def dataSlots (x D D1 D2 : ℕ) (j : Fin E3) : Fin (STd x D D1 D2) :=
  if j = inPos then cs 0 else if j = ntPos then e1T (UnaryCalc.inputTape D1)
  else if j = ltPos then e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2)) else if j = outPos then dT else e3T j

theorem inPos_val : inPos.val = 0 := rfl
theorem ntPos_val : ntPos.val = 2 := rfl
theorem ltPos_val : ltPos.val = 3 := rfl
theorem outPos_val : outPos.val = 6 := rfl

theorem dataSlots_inj : Function.Injective (dataSlots x D D1 D2) := by
  have hT : 674 ≤ TT x := by unfold TT LNS LNR; omega
  have ho := outTape_lt D2
  have hE1 : 14 ≤ E1 D1 := tapes_ge D1
  have hE2 : E2 D2 = UnaryCalc.tapes D2 + 2 := rfl
  have hc0 : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 0).val = 0 := rfl
  intro a b h
  unfold dataSlots at h
  split_ifs at h with a1 a2 a3 a4 b1 b2 b3 b4 b1 b2 b3 b4 b1 b2 b3 b4 b1 b2 b3 b4 b1 b2 b3 b4 <;>
    first
    | (subst_vars; rfl)
    | exact e3T_inj h
    | (exfalso
       have hv := congrArg Fin.val h
       simp only [hc0, dT_val, e1T_val, e2T_val, e3T_val, Fin.val_castAdd, Fin.val_natAdd, outTape_val,
         inTape_val, hE2] at hv
       omega)

theorem pos_eq (s s' : Fin (Data.DS + 1)) :
    (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) = Fin.castAdd 1 (sTape s') ↔ s = s' :=
  ⟨fun h => sTape_inj (Fin.castAdd_injective _ _ h), fun h => by rw [h]⟩

noncomputable def M8 (x D D1 D2 : ℕ) := RecoveryFocus.machine (dataSlots x D D1 D2) Data.dataM

theorem st8 {n : ℕ} (a' : ℕ) (Cs : Fin a' → SupplierPipeline.NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (tl : List Bool) (V : ℕ) (H : Fin (STd x D D1 D2) → ℕ)
    (Bin : Fin (STd x D D1 D2) → List Bool) (hH : ∀ j, H (dataSlots x D D1 D2 j) = 0)
    (hIN : Bin (cs 0) = RepairOrdinary.frame (Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl))
    (hNT : Bin (e1T (UnaryCalc.inputTape D1)) = List.replicate n true)
    (hLT : Bin (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true)
    (hOUT : Bin dT = []) (hCT : Bin (e3T ctPos) = List.replicate V true)
    (hrest : ∀ j, j ≠ inPos → j ≠ ntPos → j ≠ ltPos → j ≠ outPos → j ≠ ctPos → Bin (e3T j) = [])
    (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ V) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ V)
    (h2 : 2 ≤ n + V)
    (hcN : natBitLength n + 1 ≤ 2 * V + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * V + 2)
    (hcx : ∀ x ∈ Data.symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + V ≤ 2 * V + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2)
    (hcu : 2 * (Data.unaryList (carriers.map (·.length))).length +
      2 * (Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * V + 2) :
    ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ),
      Step (M8 x D D1 D2) (2 * Data.coreCost a' Cs carriers V V + 2) H Bin H
        (install (dataSlots x D D1 D2) Bin (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))) ∧
      tout (sTape Data.sOUT) = Data.dataWord (Data.symCounts a' Cs carriers) ∧
      tout (sTape Data.sIN) =
        RepairOrdinary.frame (Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) := by
  obtain ⟨tout, m, hs, hO, hI, _, _⟩ := Data.data_step a' Cs carriers tl V V ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  have hne_in : ∀ s, s ≠ Data.sIN → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ inPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_nt : ∀ s, s ≠ Data.sNT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ ntPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_lt : ∀ s, s ≠ Data.sLT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ ltPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_out : ∀ s, s ≠ Data.sOUT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ outPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_ct : ∀ s, s ≠ Data.sCT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ ctPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have gen : ∀ j : Fin E3, j ≠ inPos → j ≠ ntPos → j ≠ ltPos → j ≠ outPos → dataSlots x D D1 D2 j = e3T j := by
    intro j a1 a2 a3 a4
    simp [dataSlots, a1, a2, a3, a4]
  have d := Rec.dockRun hs (dataSlots x D D1 D2) dataSlots_inj H Bin (fun j => hH j) (by
    intro j
    refine Fin.addCases (fun t => ?_) (fun u => ?_) j
    · simp only [Fin.addCases_left]
      rcases tape_cases t with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [Data.rawIn_s]
        by_cases s1 : s = Data.sIN
        · subst s1
          simp only [dataSlots, inPos, if_true, if_pos rfl]
          exact hIN
        · by_cases s2 : s = Data.sNT
          · subst s2
            simp only [dataSlots, if_neg (hne_in _ s1), ntPos, if_true]
            simp [Data.sNT, Data.sIN]
            exact hNT
          · by_cases s3 : s = Data.sLT
            · subst s3
              simp only [dataSlots, if_neg (hne_in _ s1), if_neg (hne_nt _ s2), ltPos, if_true]
              simp [Data.sLT, Data.sIN, Data.sNT]
              exact hLT
            · by_cases s4 : s = Data.sOUT
              · subst s4
                simp only [dataSlots, if_neg (hne_in _ s1), if_neg (hne_nt _ s2), if_neg (hne_lt _ s3), outPos,
                  if_true]
                simp [Data.sOUT, Data.sIN, Data.sNT, Data.sLT, Data.sCT]
                exact hOUT
              · rw [gen _ (hne_in _ s1) (hne_nt _ s2) (hne_lt _ s3) (hne_out _ s4)]
                by_cases s5 : s = Data.sCT
                · subst s5
                  simp [Data.sCT, Data.sIN, Data.sNT, Data.sLT]
                  exact hCT
                · rw [hrest _ (hne_in _ s1) (hne_nt _ s2) (hne_lt _ s3) (hne_out _ s4) (hne_ct _ s5)]
                  simp [s1, s2, s3, s5]
      · have c1 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ inPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c2 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ ntPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c3 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ ltPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c4 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ outPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c5 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ ctPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        rw [gen _ c1 c2 c3 c4, hrest _ c1 c2 c3 c4 c5, Data.rawIn_c]
      · have c1 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ inPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c2 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ ntPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c3 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ ltPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c4 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ outPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c5 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ ctPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        rw [gen _ c1 c2 c3 c4, hrest _ c1 c2 c3 c4 c5, Data.rawIn_r]
    · have lne : ∀ q : Fin (Data.DS + 2 + Data.DR), (Fin.natAdd (Data.DS + 2 + Data.DR) u : Fin E3) ≠ Fin.castAdd 1 q :=
        fun q e => by
          have := congrArg Fin.val e
          simp at this
          have := q.isLt
          omega
      rw [gen _ (lne _) (lne _) (lne _) (lne _), hrest _ (lne _) (lne _) (lne _) (lne _) (lne _)]
      simp)
  exact ⟨tout, m, d.congr (dockH_eq _ dataSlots_inj _ _ _ (fun j => hH j) (fun _ _ => rfl)) rfl, hO, hI⟩

end Data

end NearCubicWires.WireExponent3_5.PrimAsm.ShellD
