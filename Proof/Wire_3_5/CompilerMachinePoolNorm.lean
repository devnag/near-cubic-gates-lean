import Proof.Wire_3_5.CompilerMachinePoolField

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## A loop over a unary run -/

/-- **A uniform body once per `1` of a unary run** `1^a` (the source reads `0` after it); the source head reads cell
`j` of the run before pass `j`. -/
theorem onesRun {t s : ℕ} (body : Machine t s) (src : Fin t) (P post : List Bool) (a : ℕ)
    (hpost : readTapeBit post 0 = false) (bH : ℕ → Fin t → ℕ) (bA : ℕ → Fin t → List Bool)
    (hsrcA : ∀ j, bA j src = P ++ List.replicate a true ++ post) (hsrcH : ∀ j, bH j src = P.length + j) (c : ℕ)
    (hstep : ∀ j, j < a → Step body c (bH j) (bA j) (bH (j + 1)) (bA (j + 1))) :
    Step (StreamController.machine body src) (a * (c + 2) + 1) (bH 0) (bA 0) (bH a) (bA a) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := a
      H := bH
      A := bA
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA j src) (bH j src) = true
        rw [hsrcA, hsrcH, List.append_assoc, read_suffix, read_prefix _ _ _ (by simpa using hj)]
        simp [readTapeBit, List.getD_eq_getElem?_getD, hj]
      halt := by
        show readTapeBit (bA a src) (bH a src) = false
        rw [hsrcA, hsrcH, List.append_assoc, read_suffix]
        have := read_suffix (List.replicate a true) post 0
        rw [List.length_replicate, Nat.add_zero] at this
        rw [this]; exact hpost }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  exact hW

/-- The magnitude register after converting the coefficients `zs` over `Y`. -/
def mrFold (h : ℕ) (Y : List Bool) (zs : List ℤ) : List Bool :=
  zs.foldl (fun M z => overlay (frame (binary h z.natAbs)) M) Y

/-- A uniform bound on one field's cost. -/
def fieldCostH (h : ℕ) : ℕ := (1 + 1 + ((2 * (2 * h + 1) + 2) + 1 + (2 * (3 * h + 2) + 2))) + 1 + emitPairCost h + 2

theorem fieldCost_le (h v : ℕ) (h1 : 1 ≤ h) (hv : v < 2 ^ h) : fieldCost h v ≤ fieldCostH h := by
  have := natBitLength_le v h h1 hv
  unfold fieldCost preCost fieldCostH convCost
  omega

/-! ## The weight loop (tapes: 0 source, 1 counter, 2 magnitude, 3 zero, 4 output, 5 log, 6 weight driver) -/

def iField : Fin 6 → Fin 7 := ![0, 1, 2, 3, 4, 5]
def iMove : Fin 1 → Fin 7 := ![6]

theorem iField_inj : Function.Injective iField := by decide

theorem install_iField (A : Fin 7 → List Bool) (v : Fin 6 → List Bool) :
    install iField A v = ![v 0, v 1, v 2, v 3, v 4, v 5, A 6] := by
  funext i
  fin_cases i
  · exact install_slot iField iField_inj A v 0
  · exact install_slot iField iField_inj A v 1
  · exact install_slot iField iField_inj A v 2
  · exact install_slot iField iField_inj A v 3
  · exact install_slot iField iField_inj A v 4
  · exact install_slot iField iField_inj A v 5
  · exact install_other iField A v 6 (by decide)

theorem dockH_iField (H : Fin 7 → ℕ) (v : Fin 6 → ℕ) :
    dockH iField H v = ![v 0, v 1, v 2, v 3, v 4, v 5, H 6] := by
  funext i
  fin_cases i
  · exact dockH_slot iField iField_inj H v 0
  · exact dockH_slot iField iField_inj H v 1
  · exact dockH_slot iField iField_inj H v 2
  · exact dockH_slot iField iField_inj H v 3
  · exact dockH_slot iField iField_inj H v 4
  · exact dockH_slot iField iField_inj H v 5
  · exact dockH_other iField H v 6 (by decide)

theorem iMove_inj : Function.Injective iMove := by decide

theorem install_iMove (A : Fin 7 → List Bool) (v : Fin 1 → List Bool) :
    install iMove A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0] := by
  funext i
  fin_cases i
  · exact install_other iMove A v 0 (by decide)
  · exact install_other iMove A v 1 (by decide)
  · exact install_other iMove A v 2 (by decide)
  · exact install_other iMove A v 3 (by decide)
  · exact install_other iMove A v 4 (by decide)
  · exact install_other iMove A v 5 (by decide)
  · exact install_slot iMove iMove_inj A v 0

theorem dockH_iMove (H : Fin 7 → ℕ) (v : Fin 1 → ℕ) :
    dockH iMove H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other iMove H v 0 (by decide)
  · exact dockH_other iMove H v 1 (by decide)
  · exact dockH_other iMove H v 2 (by decide)
  · exact dockH_other iMove H v 3 (by decide)
  · exact dockH_other iMove H v 4 (by decide)
  · exact dockH_other iMove H v 5 (by decide)
  · exact dockH_slot iMove iMove_inj H v 0

noncomputable def innerBody := Composition.machine (RecoveryFocus.machine iField fieldM) (RecoveryFocus.machine iMove moveM)
noncomputable def innerM := StreamController.machine innerBody 6
/-- The weight loop with its driver head returned to `0` (log on tape 7). -/
noncomputable def innerR := MaskedReset.machine innerM (fun i => decide (i = 6))

def iH (s o d : ℕ) : Fin 7 → ℕ := ![s, 0, 0, 0, o, 0, d]
def iA (S K M Z O LG D : List Bool) : Fin 7 → List Bool := ![S, K, M, Z, O, LG, D]

theorem inner_body (h : ℕ) (z : ℤ) (h1 : 1 ≤ h) (hz : z.natAbs < 2 ^ h) (pre post Y out BW D : List Bool)
    (capK cap d : ℕ) (hK : natBitLength z.natAbs ≤ capK) (hc1 : 2 * h + 1 ≤ cap) (hc2 : convCost z.natAbs ≤ cap) :
    Step innerBody (fieldCostH h + 1 + 1) (iH pre.length out.length d)
      (iA (pre ++ intWord z ++ post) (false :: List.replicate capK true) Y (frame (binary h 0) ++ [])
        (overlay out BW) (List.replicate cap false) D)
      (iH (pre.length + (intWord z).length) (out ++ pairEnc h (pn z)).length (d + 1))
      (iA (pre ++ intWord z ++ post) (false :: List.replicate capK true) (overlay (frame (binary h z.natAbs)) Y)
        (frame (binary h 0) ++ []) (overlay (out ++ pairEnc h (pn z)) BW) (List.replicate cap false) D) := by
  have f0 := (field_run h z h1 hz pre post Y out BW capK cap hK hc1 hc2).enlarge (fieldCost_le h z.natAbs h1 hz)
  have e1 := dockRun f0 iField iField_inj (iH pre.length out.length d)
    (iA (pre ++ intWord z ++ post) (false :: List.replicate capK true) Y (frame (binary h 0) ++ [])
      (overlay out BW) (List.replicate cap false) D) (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_iField, dockH_iField] at e1
  have e2 := dockRun (moveStep D d) iMove iMove_inj
    (iH (pre.length + (intWord z).length) (out ++ pairEnc h (pn z)).length d)
    (iA (pre ++ intWord z ++ post) (false :: List.replicate capK true) (overlay (frame (binary h z.natAbs)) Y)
      (frame (binary h 0) ++ []) (overlay (out ++ pairEnc h (pn z)) BW) (List.replicate cap false) D)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_iMove, dockH_iMove] at e2
  exact (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    (e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))

/-- The bounds a child's coefficients must meet. -/
def CoefOk (h capK cap : ℕ) (z : ℤ) : Prop :=
  z.natAbs < 2 ^ h ∧ natBitLength z.natAbs ≤ capK ∧ convCost z.natAbs ≤ cap

/-- **The weight loop**: every weight of a child becomes its P/N pair. -/
theorem inner_run (h : ℕ) (h1 : 1 ≤ h) (ws : List ℤ) (pre post Y out BW : List Bool) (capK cap : ℕ)
    (hok : ∀ z ∈ ws, CoefOk h capK cap z) (hc1 : 2 * h + 1 ≤ cap) :
    Step innerM (ws.length * (fieldCostH h + 1 + 1 + 2) + 1) (iH pre.length out.length 0)
      (iA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
        (overlay out BW) (List.replicate cap false) (List.replicate ws.length true))
      (iH (pre.length + (ws.flatMap intWord).length) (out ++ ws.flatMap (fun z => pairEnc h (pn z))).length ws.length)
      (iA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) (mrFold h Y ws)
        (frame (binary h 0)) (overlay (out ++ ws.flatMap (fun z => pairEnc h (pn z))) BW)
        (List.replicate cap false) (List.replicate ws.length true)) := by
  set SRC := pre ++ ws.flatMap intWord ++ post
  have hr := onesRun innerBody 6 [] [] ws.length rfl
    (fun j => iH (pre.length + ((ws.take j).flatMap intWord).length)
      (out ++ (ws.take j).flatMap (fun z => pairEnc h (pn z))).length j)
    (fun j => iA SRC (false :: List.replicate capK true) (mrFold h Y (ws.take j)) (frame (binary h 0))
      (overlay (out ++ (ws.take j).flatMap (fun z => pairEnc h (pn z))) BW) (List.replicate cap false)
      (List.replicate ws.length true))
    (fun j => by simp [iA]) (fun j => by simp [iH]) (fieldCostH h + 1 + 1) (by
      intro j hj
      obtain ⟨hz, hK, hc2⟩ := hok ws[j] (List.getElem_mem hj)
      have hS : SRC = (pre ++ (ws.take j).flatMap intWord) ++ intWord ws[j] ++
          ((ws.drop (j + 1)).flatMap intWord ++ post) := by
        simp only [SRC]
        rw [enc_split intWord ws j hj]
        simp [List.append_assoc]
      have b := inner_body h ws[j] h1 hz (pre ++ (ws.take j).flatMap intWord) ((ws.drop (j + 1)).flatMap intWord ++ post)
        (mrFold h Y (ws.take j)) (out ++ (ws.take j).flatMap (fun z => pairEnc h (pn z))) BW
        (List.replicate ws.length true) capK cap j hK hc1 hc2
      rw [← hS] at b
      have ht : ws.take (j + 1) = ws.take j ++ [ws[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have eS : (pre ++ (ws.take j).flatMap intWord).length + (intWord ws[j]).length =
          pre.length + ((ws.take (j + 1)).flatMap intWord).length := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        simp only [List.length_append]
        omega
      have eO : out ++ (ws.take j).flatMap (fun z => pairEnc h (pn z)) ++ pairEnc h (pn ws[j]) =
          out ++ (ws.take (j + 1)).flatMap (fun z => pairEnc h (pn z)) := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have eM : overlay (frame (binary h ws[j].natAbs)) (mrFold h Y (ws.take j)) = mrFold h Y (ws.take (j + 1)) := by
        rw [ht, mrFold, mrFold, List.foldl_append]
        rfl
      rw [eS, eO, eM, List.append_nil] at b
      refine b.congr_in ?_ rfl
      rw [List.length_append])
  rw [List.take_length, List.take_zero] at hr
  have h0 : mrFold h Y [] = Y := rfl
  simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, List.append_nil, h0] at hr
  exact hr

/-- The weight loop's cost for `n` weights. -/
def innerCost (h n : ℕ) : ℕ := n * (fieldCostH h + 1 + 1 + 2) + 1

def iRH (s o : ℕ) : Fin 8 → ℕ := ![s, 0, 0, 0, o, 0, 0, 0]
def iRA (S K M Z O LG D LG2 : List Bool) : Fin 8 → List Bool := ![S, K, M, Z, O, LG, D, LG2]

theorem innerR_run (h : ℕ) (h1 : 1 ≤ h) (ws : List ℤ) (pre post Y out BW : List Bool) (capK cap cap2 : ℕ)
    (hok : ∀ z ∈ ws, CoefOk h capK cap z) (hc1 : 2 * h + 1 ≤ cap) (hc2 : innerCost h ws.length ≤ cap2) :
    Step innerR (2 * innerCost h ws.length + 2) (iRH pre.length out.length)
      (iRA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
        (overlay out BW) (List.replicate cap false) (List.replicate ws.length true) (List.replicate cap2 false))
      (iRH (pre.length + (ws.flatMap intWord).length) (out ++ ws.flatMap (fun z => pairEnc h (pn z))).length)
      (iRA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) (mrFold h Y ws)
        (frame (binary h 0)) (overlay (out ++ ws.flatMap (fun z => pairEnc h (pn z))) BW) (List.replicate cap false)
        (List.replicate ws.length true) (List.replicate cap2 false)) := by
  have hm := (inner_run h h1 ws pre post Y out BW capK cap hok hc1).mask (fun i => decide (i = 6))
    (by intro i hi; simp at hi; subst hi; rfl) hc2
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## One child (tapes: 0-6 as above, 7 the weight loop's log, 8 the child driver) -/

def cInner : Fin 8 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7]
def cPut : Fin 1 → Fin 9 := ![4]
def cField : Fin 6 → Fin 9 := ![0, 1, 2, 3, 4, 5]
def cMove : Fin 1 → Fin 9 := ![8]

theorem cInner_inj : Function.Injective cInner := by decide

theorem install_cInner (A : Fin 9 → List Bool) (v : Fin 8 → List Bool) :
    install cInner A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, A 8] := by
  funext i
  fin_cases i
  · exact install_slot cInner cInner_inj A v 0
  · exact install_slot cInner cInner_inj A v 1
  · exact install_slot cInner cInner_inj A v 2
  · exact install_slot cInner cInner_inj A v 3
  · exact install_slot cInner cInner_inj A v 4
  · exact install_slot cInner cInner_inj A v 5
  · exact install_slot cInner cInner_inj A v 6
  · exact install_slot cInner cInner_inj A v 7
  · exact install_other cInner A v 8 (by decide)

theorem dockH_cInner (H : Fin 9 → ℕ) (v : Fin 8 → ℕ) :
    dockH cInner H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_slot cInner cInner_inj H v 0
  · exact dockH_slot cInner cInner_inj H v 1
  · exact dockH_slot cInner cInner_inj H v 2
  · exact dockH_slot cInner cInner_inj H v 3
  · exact dockH_slot cInner cInner_inj H v 4
  · exact dockH_slot cInner cInner_inj H v 5
  · exact dockH_slot cInner cInner_inj H v 6
  · exact dockH_slot cInner cInner_inj H v 7
  · exact dockH_other cInner H v 8 (by decide)

theorem cPut_inj : Function.Injective cPut := by decide

theorem install_cPut (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install cPut A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other cPut A v 0 (by decide)
  · exact install_other cPut A v 1 (by decide)
  · exact install_other cPut A v 2 (by decide)
  · exact install_other cPut A v 3 (by decide)
  · exact install_slot cPut cPut_inj A v 0
  · exact install_other cPut A v 5 (by decide)
  · exact install_other cPut A v 6 (by decide)
  · exact install_other cPut A v 7 (by decide)
  · exact install_other cPut A v 8 (by decide)

theorem dockH_cPut (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH cPut H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other cPut H v 0 (by decide)
  · exact dockH_other cPut H v 1 (by decide)
  · exact dockH_other cPut H v 2 (by decide)
  · exact dockH_other cPut H v 3 (by decide)
  · exact dockH_slot cPut cPut_inj H v 0
  · exact dockH_other cPut H v 5 (by decide)
  · exact dockH_other cPut H v 6 (by decide)
  · exact dockH_other cPut H v 7 (by decide)
  · exact dockH_other cPut H v 8 (by decide)

theorem cField_inj : Function.Injective cField := by decide

theorem install_cField (A : Fin 9 → List Bool) (v : Fin 6 → List Bool) :
    install cField A v = ![v 0, v 1, v 2, v 3, v 4, v 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_slot cField cField_inj A v 0
  · exact install_slot cField cField_inj A v 1
  · exact install_slot cField cField_inj A v 2
  · exact install_slot cField cField_inj A v 3
  · exact install_slot cField cField_inj A v 4
  · exact install_slot cField cField_inj A v 5
  · exact install_other cField A v 6 (by decide)
  · exact install_other cField A v 7 (by decide)
  · exact install_other cField A v 8 (by decide)

theorem dockH_cField (H : Fin 9 → ℕ) (v : Fin 6 → ℕ) :
    dockH cField H v = ![v 0, v 1, v 2, v 3, v 4, v 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_slot cField cField_inj H v 0
  · exact dockH_slot cField cField_inj H v 1
  · exact dockH_slot cField cField_inj H v 2
  · exact dockH_slot cField cField_inj H v 3
  · exact dockH_slot cField cField_inj H v 4
  · exact dockH_slot cField cField_inj H v 5
  · exact dockH_other cField H v 6 (by decide)
  · exact dockH_other cField H v 7 (by decide)
  · exact dockH_other cField H v 8 (by decide)

theorem cMove_inj : Function.Injective cMove := by decide

theorem install_cMove (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install cMove A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 0] := by
  funext i
  fin_cases i
  · exact install_other cMove A v 0 (by decide)
  · exact install_other cMove A v 1 (by decide)
  · exact install_other cMove A v 2 (by decide)
  · exact install_other cMove A v 3 (by decide)
  · exact install_other cMove A v 4 (by decide)
  · exact install_other cMove A v 5 (by decide)
  · exact install_other cMove A v 6 (by decide)
  · exact install_other cMove A v 7 (by decide)
  · exact install_slot cMove cMove_inj A v 0

theorem dockH_cMove (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH cMove H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other cMove H v 0 (by decide)
  · exact dockH_other cMove H v 1 (by decide)
  · exact dockH_other cMove H v 2 (by decide)
  · exact dockH_other cMove H v 3 (by decide)
  · exact dockH_other cMove H v 4 (by decide)
  · exact dockH_other cMove H v 5 (by decide)
  · exact dockH_other cMove H v 6 (by decide)
  · exact dockH_other cMove H v 7 (by decide)
  · exact dockH_slot cMove cMove_inj H v 0

noncomputable def childBody := Composition.machine (RecoveryFocus.machine cInner innerR)
  (Composition.machine (RecoveryFocus.machine cPut (putM false))
    (Composition.machine (RecoveryFocus.machine cField fieldM) (RecoveryFocus.machine cMove moveM)))

def cH (s o b : ℕ) : Fin 9 → ℕ := ![s, 0, 0, 0, o, 0, 0, 0, b]
def cA (S K M Z O LG D LG2 DB : List Bool) : Fin 9 → List Bool := ![S, K, M, Z, O, LG, D, LG2, DB]

/-- The cost of one child with `n` weights. -/
def childCost (h n : ℕ) : ℕ := (2 * innerCost h n + 2) + 1 + (1 + 1 + (fieldCostH h + 1 + 1))

theorem cs_inner (h : ℕ) (h1 : 1 ≤ h) (ws : List ℤ) (pre post Y out BW DB : List Bool) (capK cap cap2 b : ℕ)
    (hok : ∀ z ∈ ws, CoefOk h capK cap z) (hc1 : 2 * h + 1 ≤ cap) (hc2 : innerCost h ws.length ≤ cap2) :
    Step (RecoveryFocus.machine cInner innerR) (2 * innerCost h ws.length + 2) (cH pre.length out.length b)
      (cA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
        (overlay out BW) (List.replicate cap false) (List.replicate ws.length true) (List.replicate cap2 false) DB)
      (cH (pre.length + (ws.flatMap intWord).length) (out ++ ws.flatMap (fun z => pairEnc h (pn z))).length b)
      (cA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) (mrFold h Y ws)
        (frame (binary h 0)) (overlay (out ++ ws.flatMap (fun z => pairEnc h (pn z))) BW) (List.replicate cap false)
        (List.replicate ws.length true) (List.replicate cap2 false) DB) := by
  have e := dockRun (innerR_run h h1 ws pre post Y out BW capK cap cap2 hok hc1 hc2) cInner cInner_inj
    (cH pre.length out.length b)
    (cA (pre ++ ws.flatMap intWord ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
      (overlay out BW) (List.replicate cap false) (List.replicate ws.length true) (List.replicate cap2 false) DB)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_cInner, dockH_cInner] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem cs_put (s b : ℕ) (S K M Z LG D LG2 DB O BW : List Bool) :
    Step (RecoveryFocus.machine cPut (putM false)) 1 (cH s O.length b) (cA S K M Z (overlay O BW) LG D LG2 DB)
      (cH s (O ++ [false]).length b) (cA S K M Z (overlay (O ++ [false]) BW) LG D LG2 DB) := by
  have p0 := putStep false (overlay O BW) O.length
  rw [overlay_write] at p0
  have e := dockRun p0 cPut cPut_inj (cH s O.length b) (cA S K M Z (overlay O BW) LG D LG2 DB)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_cPut, dockH_cPut] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [cH]

theorem cs_field (h : ℕ) (z : ℤ) (h1 : 1 ≤ h) (hz : z.natAbs < 2 ^ h) (pre post Y out BW D LG2 DB : List Bool)
    (capK cap b : ℕ) (hK : natBitLength z.natAbs ≤ capK) (hc1 : 2 * h + 1 ≤ cap) (hc2 : convCost z.natAbs ≤ cap) :
    Step (RecoveryFocus.machine cField fieldM) (fieldCostH h) (cH pre.length out.length b)
      (cA (pre ++ intWord z ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
        (overlay out BW) (List.replicate cap false) D LG2 DB)
      (cH (pre.length + (intWord z).length) (out ++ pairEnc h (pn z)).length b)
      (cA (pre ++ intWord z ++ post) (false :: List.replicate capK true) (overlay (frame (binary h z.natAbs)) Y)
        (frame (binary h 0)) (overlay (out ++ pairEnc h (pn z)) BW) (List.replicate cap false) D LG2 DB) := by
  have f0 := (field_run h z h1 hz pre post Y out BW capK cap hK hc1 hc2).enlarge (fieldCost_le h z.natAbs h1 hz)
  rw [List.append_nil] at f0
  have e := dockRun f0 cField cField_inj (cH pre.length out.length b)
    (cA (pre ++ intWord z ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
      (overlay out BW) (List.replicate cap false) D LG2 DB) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_cField, dockH_cField] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem cs_move (s o b : ℕ) (S K M Z O LG D LG2 DB : List Bool) :
    Step (RecoveryFocus.machine cMove moveM) 1 (cH s o b) (cA S K M Z O LG D LG2 DB)
      (cH s o (b + 1)) (cA S K M Z O LG D LG2 DB) := by
  have e := dockRun (moveStep DB b) cMove cMove_inj (cH s o b) (cA S K M Z O LG D LG2 DB)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_cMove, dockH_cMove] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- **One child normalized**: its native word becomes `origRec h e`. -/
theorem child_step (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (e : ExactThresholdGate n) (pre post Y out BW DB : List Bool)
    (capK cap cap2 b : ℕ) (hok : ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk h capK cap z)
    (hc1 : 2 * h + 1 ≤ cap) (hc2 : innerCost h n ≤ cap2) :
    Step childBody (childCost h n) (cH pre.length out.length b)
      (cA (pre ++ exactWord e ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
        (overlay out BW) (List.replicate cap false) (List.replicate n true) (List.replicate cap2 false) DB)
      (cH (pre.length + (exactWord e).length) (out ++ origRec h e).length (b + 1))
      (cA (pre ++ exactWord e ++ post) (false :: List.replicate capK true)
        (mrFold h Y (List.ofFn e.weight ++ [e.target])) (frame (binary h 0))
        (overlay (out ++ origRec h e) BW) (List.replicate cap false) (List.replicate n true)
        (List.replicate cap2 false) DB) := by
  have hwl : (List.ofFn e.weight).length = n := List.length_ofFn
  have hS : pre ++ exactWord e ++ post = pre ++ (List.ofFn e.weight).flatMap intWord ++ (intWord e.target ++ post) := by
    simp [exactWord, List.append_assoc]
  have hS2 : pre ++ exactWord e ++ post = (pre ++ (List.ofFn e.weight).flatMap intWord) ++ intWord e.target ++ post := by
    simp [exactWord, List.append_assoc]
  have e1 := cs_inner h h1 (List.ofFn e.weight) pre (intWord e.target ++ post) Y out BW DB capK cap cap2 b
    (fun z hz => hok z (List.mem_append_left _ hz)) hc1 (by rw [hwl]; exact hc2)
  rw [← hS, hwl] at e1
  have e2 := cs_put (pre.length + ((List.ofFn e.weight).flatMap intWord).length) b (pre ++ exactWord e ++ post)
    (false :: List.replicate capK true) (mrFold h Y (List.ofFn e.weight)) (frame (binary h 0))
    (List.replicate cap false) (List.replicate n true) (List.replicate cap2 false) DB
    (out ++ (List.ofFn e.weight).flatMap (fun z => pairEnc h (pn z))) BW
  obtain ⟨hzt, hKt, hct⟩ := hok e.target (List.mem_append_right _ (List.mem_singleton_self _))
  have e3 := cs_field h e.target h1 hzt (pre ++ (List.ofFn e.weight).flatMap intWord) post
    (mrFold h Y (List.ofFn e.weight)) (out ++ (List.ofFn e.weight).flatMap (fun z => pairEnc h (pn z)) ++ [false]) BW
    (List.replicate n true) (List.replicate cap2 false) DB capK cap b hKt hc1 hct
  rw [← hS2, List.length_append] at e3
  have e4 := cs_move (pre.length + (exactWord e).length) (out ++ origRec h e).length b (pre ++ exactWord e ++ post)
    (false :: List.replicate capK true) (mrFold h Y (List.ofFn e.weight ++ [e.target])) (frame (binary h 0))
    (overlay (out ++ origRec h e) BW) (List.replicate cap false) (List.replicate n true) (List.replicate cap2 false) DB
  have hO : out ++ (List.ofFn e.weight).flatMap (fun z => pairEnc h (pn z)) ++ [false] ++ pairEnc h (pn e.target) =
      out ++ origRec h e := by
    simp [origRec, List.append_assoc]
  have hM : overlay (frame (binary h e.target.natAbs)) (mrFold h Y (List.ofFn e.weight)) =
      mrFold h Y (List.ofFn e.weight ++ [e.target]) := by
    simp [mrFold, List.foldl_append]
  have hL : pre.length + ((List.ofFn e.weight).flatMap intWord).length + (intWord e.target).length =
      pre.length + (exactWord e).length := by
    simp [exactWord, Nat.add_assoc]
  rw [hO, hM, hL] at e3
  exact e1.seq (e2.seq (e3.seq e4))

/-! ## All children -/

/-- The loop over the children, driven by the unary total on tape 8. -/
noncomputable def normLoop := StreamController.machine childBody 8
/-- **The normalization pass**: every child, then the closing `false`. -/
noncomputable def normM := Composition.machine normLoop (RecoveryFocus.machine cPut (putM false))

/-- The magnitude register after all the children. -/
def mrKids (h : ℕ) (Y : List Bool) {n : ℕ} (gs : List (ExactThresholdGate n)) : List Bool :=
  gs.foldl (fun M e => mrFold h M (List.ofFn e.weight ++ [e.target])) Y

/-- The normalization cost. -/
def normCost (h n B : ℕ) : ℕ := B * (childCost h n + 2) + 1 + 1 + 1

/-- **The children normalized**: the decomposition's native children `gs.flatMap exactWord` become
`normTape h gs`, driven by the unary total `1^B` (`B = |gs|`). -/
theorem norm_run (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (gs : List (ExactThresholdGate n)) (pre post Y out BW : List Bool)
    (capK cap cap2 : ℕ) (hok : ∀ e ∈ gs, ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk h capK cap z)
    (hc1 : 2 * h + 1 ≤ cap) (hc2 : innerCost h n ≤ cap2) :
    Step normM (normCost h n gs.length) (cH pre.length out.length 0)
      (cA (pre ++ gs.flatMap exactWord ++ post) (false :: List.replicate capK true) Y (frame (binary h 0))
        (overlay out BW) (List.replicate cap false) (List.replicate n true) (List.replicate cap2 false)
        (List.replicate gs.length true))
      (cH (pre.length + (gs.flatMap exactWord).length) (out ++ normTape h gs).length gs.length)
      (cA (pre ++ gs.flatMap exactWord ++ post) (false :: List.replicate capK true) (mrKids h Y gs)
        (frame (binary h 0)) (overlay (out ++ normTape h gs) BW) (List.replicate cap false) (List.replicate n true)
        (List.replicate cap2 false) (List.replicate gs.length true)) := by
  set SRC := pre ++ gs.flatMap exactWord ++ post
  set DB := List.replicate gs.length true
  have hr := onesRun childBody 8 [] [] gs.length rfl
    (fun j => cH (pre.length + ((gs.take j).flatMap exactWord).length)
      (out ++ (gs.take j).flatMap (origRec h)).length j)
    (fun j => cA SRC (false :: List.replicate capK true) (mrKids h Y (gs.take j)) (frame (binary h 0))
      (overlay (out ++ (gs.take j).flatMap (origRec h)) BW) (List.replicate cap false) (List.replicate n true)
      (List.replicate cap2 false) DB)
    (fun j => by simp [cA, DB]) (fun j => by simp [cH]) (childCost h n) (by
      intro j hj
      have hS : SRC = (pre ++ (gs.take j).flatMap exactWord) ++ exactWord gs[j] ++
          ((gs.drop (j + 1)).flatMap exactWord ++ post) := by
        simp only [SRC]
        rw [enc_split exactWord gs j hj]
        simp [List.append_assoc]
      have b := child_step h h1 gs[j] (pre ++ (gs.take j).flatMap exactWord) ((gs.drop (j + 1)).flatMap exactWord ++ post)
        (mrKids h Y (gs.take j)) (out ++ (gs.take j).flatMap (origRec h)) BW DB capK cap cap2 j
        (hok gs[j] (List.getElem_mem hj)) hc1 hc2
      rw [← hS] at b
      have ht : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have eS : (pre ++ (gs.take j).flatMap exactWord).length + (exactWord gs[j]).length =
          pre.length + ((gs.take (j + 1)).flatMap exactWord).length := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        simp only [List.length_append]
        omega
      have eO : out ++ (gs.take j).flatMap (origRec h) ++ origRec h gs[j] =
          out ++ (gs.take (j + 1)).flatMap (origRec h) := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have eM : mrFold h (mrKids h Y (gs.take j)) (List.ofFn gs[j].weight ++ [gs[j].target]) =
          mrKids h Y (gs.take (j + 1)) := by
        rw [ht, mrKids, mrKids, List.foldl_append]
        rfl
      rw [eS, eO, eM] at b
      refine b.congr_in ?_ rfl
      rw [List.length_append])
  rw [List.take_length, List.take_zero] at hr
  have h0 : mrKids h Y ([] : List (ExactThresholdGate n)) = Y := rfl
  simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, List.append_nil, h0] at hr
  have p := cs_put (pre.length + (gs.flatMap exactWord).length) gs.length SRC (false :: List.replicate capK true)
    (mrKids h Y gs) (frame (binary h 0)) (List.replicate cap false) (List.replicate n true)
    (List.replicate cap2 false) DB (out ++ gs.flatMap (origRec h)) BW
  have hN : out ++ gs.flatMap (origRec h) ++ [false] = out ++ normTape h gs := by simp [normTape]
  rw [hN] at p
  exact hr.seq p

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
