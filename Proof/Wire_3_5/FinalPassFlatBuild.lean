import Proof.Wire_3_5.FinalPassFlatVisit
import Proof.Wire_3_5.FinalPassFiltTabWalk

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.RepairSource.VerifierDecoding Theorem25Completion NearCubicWires.RepairOrdinary.RecoveryRootRound

variable (cap : ℕ)

/-! ## The combined bank -/

theorem l_vw_tau (y : LSt) (X Y : List Bool) : (y.w.sets qV X).sets qTAU Y = { y with vw := X, tauw := Y }.w := by
  lst_eq

/-- The walk's tapes inside the bank: tapes `0` and `1` are the streams `V` and `TAU`, tapes `2..7` follow. -/
def wslotsL : Fin 8 → Fin (11 + 2 + 19 + 6) := fun k =>
  if k.val = 0 then ⟨0, by omega⟩ else if k.val = 1 then ⟨3, by omega⟩ else ⟨30 + k.val, by omega⟩

theorem wslotsL_val (k : Fin 8) :
    (wslotsL k).val = if k.val = 0 then 0 else if k.val = 1 then 3 else 30 + k.val := by
  unfold wslotsL; split_ifs <;> rfl

theorem wslotsL_inj : Function.Injective wslotsL := by
  intro a b h
  have := congrArg Fin.val h
  rw [wslotsL_val, wslotsL_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

/-- The combined tapes: the visit's, then the walk's tapes `2..7`. -/
def cAL (y : LSt) (bk : Fin 8 → List Bool) : Fin (11 + 2 + 19 + 6) → List Bool :=
  Fin.addCases (m := 11 + 2 + 19) (n := 6) (wenc cap y.w).A (fun k => bk k.succ.succ)

/-- The combined heads. -/
def cHL (y : LSt) (hk : Fin 8 → ℕ) : Fin (11 + 2 + 19 + 6) → ℕ :=
  Fin.addCases (m := 11 + 2 + 19) (n := 6) (wenc cap y.w).H (fun k => hk k.succ.succ)

theorem wslotsL_zero : wslotsL 0 = Fin.castAdd 6 (⟨0, by omega⟩ : Fin (11 + 2 + 19)) := by
  apply Fin.ext; rw [wslotsL_val]; rfl

theorem wslotsL_one : wslotsL 1 = Fin.castAdd 6 (⟨3, by omega⟩ : Fin (11 + 2 + 19)) := by
  apply Fin.ext; rw [wslotsL_val]; rfl

theorem wslotsL_ss (k : Fin 6) : wslotsL k.succ.succ = Fin.natAdd (11 + 2 + 19) k := by
  apply Fin.ext; rw [wslotsL_val]; simp [Fin.val_succ]; omega

theorem not_slotL (e : Fin (11 + 2 + 19)) (h0 : e.val ≠ 0) (h3 : e.val ≠ 3) (k : Fin 8) :
    wslotsL k ≠ Fin.castAdd 6 e := by
  intro h
  have h1 := congrArg Fin.val h
  rw [wslotsL_val, Fin.val_castAdd] at h1
  have := e.isLt
  split_ifs at h1 <;> omega

theorem sTape_zero : (sTape (ns := 11) (nr := 19) 0 : Fin (11 + 2 + 19)) = ⟨0, by omega⟩ := rfl
theorem sTape_two : (sTape (ns := 11) (nr := 19) 2 : Fin (11 + 2 + 19)) = ⟨3, by omega⟩ := rfl

/-- **The walk transition in the bank** changes the visit's tapes only at the two coordinate words. -/
theorem install_cAL (y : LSt) (bk bk' : Fin 8 → List Bool) :
    install wslotsL (cAL cap y bk) bk' = cAL cap { y with vw := bk' 0, tauw := bk' 1 } bk' := by
  funext j
  refine Fin.addCases (fun e => ?_) (fun k => ?_) j
  · by_cases he : e.val = 0
    · have hj : Fin.castAdd 6 e = wslotsL 0 := by rw [wslotsL_zero]; congr 1; exact Fin.ext he
      rw [hj, install_slot wslotsL wslotsL_inj, ← hj]
      simp only [cAL, Fin.addCases_left]
      have hs : e = sTape (ns := 11) (nr := 19) 0 := Fin.ext (by rw [he]; rfl)
      rw [← l_vw_tau y (bk' 0) (bk' 1), wenc_sets_A, wenc_sets_A, if_neg (by rw [hs]; decide), if_pos hs]
    · by_cases he3 : e.val = 3
      · have hj : Fin.castAdd 6 e = wslotsL 1 := by rw [wslotsL_one]; congr 1; exact Fin.ext he3
        rw [hj, install_slot wslotsL wslotsL_inj, ← hj]
        simp only [cAL, Fin.addCases_left]
        have hs : e = sTape (ns := 11) (nr := 19) 2 := Fin.ext (by rw [he3]; rfl)
        rw [← l_vw_tau y (bk' 0) (bk' 1), wenc_sets_A, if_pos hs]
      · rw [install_other wslotsL _ _ _ (fun k => not_slotL e he he3 k)]
        simp only [cAL, Fin.addCases_left]
        have hs0 : ¬ e = sTape (ns := 11) (nr := 19) 0 := fun h => he (by rw [h]; rfl)
        have hs2 : ¬ e = sTape (ns := 11) (nr := 19) 2 := fun h => he3 (by rw [h]; rfl)
        rw [← l_vw_tau y (bk' 0) (bk' 1), wenc_sets_A, wenc_sets_A, if_neg hs2, if_neg hs0]
  · rw [← wslotsL_ss, install_slot wslotsL wslotsL_inj]
    simp only [cAL, wslotsL_ss, Fin.addCases_right]

/-- The walk's heads in the bank, when the coordinate words' heads are the visit's. -/
theorem dock_cHL (y : LSt) (hk hk' : Fin 8 → ℕ) (h0 : hk' 0 = y.vh) (h1 : hk' 1 = y.tauh) :
    dockH wslotsL (cHL cap y hk) hk' = cHL cap y hk' := by
  funext j
  refine Fin.addCases (fun e => ?_) (fun k => ?_) j
  · by_cases he : e.val = 0
    · have hj : Fin.castAdd 6 e = wslotsL 0 := by rw [wslotsL_zero]; congr 1; exact Fin.ext he
      rw [hj, dockH_slot wslotsL wslotsL_inj, ← hj, h0]
      simp only [cHL, Fin.addCases_left]
      have : e = ⟨0, by omega⟩ := Fin.ext he
      rw [this]; rfl
    · by_cases he3 : e.val = 3
      · have hj : Fin.castAdd 6 e = wslotsL 1 := by rw [wslotsL_one]; congr 1; exact Fin.ext he3
        rw [hj, dockH_slot wslotsL wslotsL_inj, ← hj, h1]
        simp only [cHL, Fin.addCases_left]
        have : e = ⟨3, by omega⟩ := Fin.ext he3
        rw [this]; rfl
      · rw [dockH_other wslotsL _ _ _ (fun k => not_slotL e he he3 k)]
        simp only [cHL, Fin.addCases_left]
  · rw [← wslotsL_ss, dockH_slot wslotsL wslotsL_inj]
    simp only [cHL, wslotsL_ss, Fin.addCases_right]

/-! ## The canonical state and the visit's word -/

/-- The state before a visit: the coordinate words, the table so far, and the previous visit's seed words. -/
def canonL (m lb L tf n : ℕ) (sw vw tauw ow : List Bool) : LSt where
  vw := vw
  ow := ow
  tauw := tauw
  pmw := frameP sw ++ [false]
  fv := List.replicate n true ++ [false]
  fu := []
  pw := []
  acc := []
  st := []
  kw := frame (binary lb 0)
  bw := frameP (bwOfSw lb sw) ++ [false]
  ep := frameP (epOfSw lb sw) ++ [false]
  vh := 0
  bwh := 0
  eph := 0
  f := 0
  ck := 0
  s := 0
  ns := 0
  tf := tf
  j := 0
  m := m
  lb := lb
  a := 0
  L := L
  cell := false
  tauh := 0
  pmh := 0
  g1 := 0
  g3 := 0

/-- The seed bits of the vertex `(x, y)`. -/
def vertexSw (m tf x y : ℕ) : List Bool := swOf tf (binary m y) (binary m x)

theorem vertexSw_length (m tf x y : ℕ) : (vertexSw m tf x y).length = 2 * m - tf := by
  simp [vertexSw, swOf]; omega

/-- **The visit's word**: the visit marker, then the rows of levels `n−1, …, 0`. -/
def visitWordL (m lb L tf n x y : ℕ) : List Bool :=
  true :: levelRows (epOfSw lb (vertexSw m tf x y)) (bwOfSw lb (vertexSw m tf x y)) lb L n

theorem visitWordL_length (m lb L tf n x y : ℕ) : (visitWordL m lb L tf n x y).length = 1 + n * (2 * L + 1) := by
  simp [visitWordL, levelRows_length]; ring

theorem word_split (r R : ℕ) (z : ZMod (2 ^ r)) :
    WalkEdgeReuse.word r R z = frameP (binary r z.val) ++ (false :: List.replicate (R - (2 * r + 1)) false) :=
  word_eq r R z

/-- **One visit between canonical states.** -/
theorem visitL_canon (m lb L tf n : ℕ) (sw ow : List Bool) (x y : ℕ) (restX restY : List Bool)
    (hsw : sw.length = 2 * m - tf) (hpad : tf ≤ 1) (hps : tf ≤ m) (hsd : 2 * lb - 1 + lb ≤ 2 * m - tf)
    (hlb : 1 ≤ lb) (hn : n ≤ lb + 1) (hcap : 8 * m + 8 * lb + 8 ≤ cap)
    (hO : ow.length + 1 + n * (2 * L + 1) + 4 < cap) :
    WExec cap visitL (canonL m lb L tf n sw (frameP (binary m x) ++ restX) (frameP (binary m y) ++ restY) ow).w
      (canonL m lb L tf n (vertexSw m tf x y) (frameP (binary m x) ++ restX) (frameP (binary m y) ++ restY)
        (ow ++ visitWordL m lb L tf n x y)).w (visitLCost m lb L n) := by
  have h := visitL_spec cap (canonL m lb L tf n sw (frameP (binary m x) ++ restX) (frameP (binary m y) ++ restY) ow)
    (binary m y) (binary m x) sw (epOfSw lb sw) (bwOfSw lb sw) restY restX [false] [] n rfl rfl rfl rfl rfl rfl rfl
    (binary_length m y) (binary_length m x) hsw hpad hps (epOfSw_length lb sw (by omega))
    (bwOfSw_length lb sw (by omega)) hsd hlb hn rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcap hO
  exact h

/-! ## One visit and one transition -/

/-- The visit machine. -/
noncomputable def visitM : Machine (11 + 2 + 19) visitL.toProg.size := visitL.toProg.compile

/-- One loop body: a visit, then a walk transition. -/
noncomputable def bodyML :=
  Composition.machine (TapeEmbedding.machine 6 visitM) (RecoveryFocus.machine wslotsL WalkPoweredRun.machine)

theorem walkA_one {r n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) (tail : List Bool) (i : ℕ) :
    WalkTimeLoop.A R LW sample tail i 1 = WalkEdgeReuse.word r R (WalkTimeLoop.vertex sample i).2 := rfl

theorem walkH_one (n i : ℕ) : WalkTimeLoop.H n i 1 = 0 := rfl

/-- The seed bits before visit `i`: blank before the first visit, else the previous vertex's. -/
def swAt (m tf : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) : List Bool :=
  if i = 0 then List.replicate (2 * m - tf) false
  else vertexSw m tf (WalkTimeLoop.vertex sample (i - 1)).1.val (WalkTimeLoop.vertex sample (i - 1)).2.val

theorem swAt_length (m tf : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) :
    (swAt m tf sample i).length = 2 * m - tf := by
  unfold swAt; split_ifs
  · simp
  · exact vertexSw_length _ _ _ _

theorem swAt_succ (m tf : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) :
    swAt m tf sample (i + 1) =
      vertexSw m tf (WalkTimeLoop.vertex sample i).1.val (WalkTimeLoop.vertex sample i).2.val := by
  simp [swAt]

/-- The state before visit `i`. -/
def canonAt (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ m) (n + 1)) (tail : List Bool)
    (i : ℕ) (ow : List Bool) : LSt :=
  canonL m lb L tf nJ (swAt m tf sample i) (WalkTimeLoop.A R LW sample tail i 0) (WalkTimeLoop.A R LW sample tail i 1) ow

/-- The word of visit `i`. -/
def visitAt (m lb L tf nJ : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) : List Bool :=
  visitWordL m lb L tf nJ (WalkTimeLoop.vertex sample i).1.val (WalkTimeLoop.vertex sample i).2.val

theorem canonL_coords (m lb L tf nJ : ℕ) (sw vw tauw ow X Y : List Bool) :
    ({ canonL m lb L tf nJ sw vw tauw ow with vw := X, tauw := Y } : LSt) = canonL m lb L tf nJ sw X Y ow := rfl

/-- **One loop body**: the visit of vertex `i` is appended to the table, then the walk moves to vertex `i+1`. -/
theorem bodyStepL (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ m) (n + 1))
    (tail ow : List Bool) (i : ℕ) (hi : i < n) (hR : 2 * m + 1 ≤ R) (hLW : 2 * m + 1 ≤ LW)
    (hpad : tf ≤ 1) (hps : tf ≤ m) (hsd : 2 * lb - 1 + lb ≤ 2 * m - tf) (hlb : 1 ≤ lb) (hnJ : nJ ≤ lb + 1)
    (hcap : 8 * m + 8 * lb + 8 ≤ cap) (hO : ow.length + 1 + nJ * (2 * L + 1) + 4 < cap) :
    Step bodyML (visitLCost m lb L nJ + 1 + (160 * m + 160 * R + 1160))
      (cHL cap (canonAt m lb L tf nJ R LW sample tail i ow) (WalkTimeLoop.H n i))
      (cAL cap (canonAt m lb L tf nJ R LW sample tail i ow) (WalkTimeLoop.A R LW sample tail i))
      (cHL cap (canonAt m lb L tf nJ R LW sample tail (i + 1) (ow ++ visitAt m lb L tf nJ sample i))
        (WalkTimeLoop.H n (i + 1)))
      (cAL cap (canonAt m lb L tf nJ R LW sample tail (i + 1) (ow ++ visitAt m lb L tf nJ sample i))
        (WalkTimeLoop.A R LW sample tail (i + 1))) := by
  -- the visit
  have hv := visitL_canon cap m lb L tf nJ (swAt m tf sample i) ow (WalkTimeLoop.vertex sample i).1.val
    (WalkTimeLoop.vertex sample i).2.val (false :: List.replicate (R - (2 * m + 1)) false)
    (false :: List.replicate (R - (2 * m + 1)) false) (swAt_length m tf sample i) hpad hps hsd hlb hnJ hcap hO
  rw [← word_split, ← word_split, ← walkA_zero, ← walkA_one] at hv
  have e1 := ((WExec.exec cap hv).step).embed (fun k : Fin 6 => WalkTimeLoop.H n i k.succ.succ)
    (fun k : Fin 6 => WalkTimeLoop.A R LW sample tail i k.succ.succ)
  -- the transition
  have w1 := (WalkTimeLoop.iteration R LW sample tail i hi hR hLW).focus wslotsL wslotsL_inj
    (cHL cap (canonL m lb L tf nJ (vertexSw m tf (WalkTimeLoop.vertex sample i).1.val
      (WalkTimeLoop.vertex sample i).2.val) (WalkTimeLoop.A R LW sample tail i 0) (WalkTimeLoop.A R LW sample tail i 1)
      (ow ++ visitAt m lb L tf nJ sample i)) (WalkTimeLoop.H n i))
    (cAL cap (canonL m lb L tf nJ (vertexSw m tf (WalkTimeLoop.vertex sample i).1.val
      (WalkTimeLoop.vertex sample i).2.val) (WalkTimeLoop.A R LW sample tail i 0) (WalkTimeLoop.A R LW sample tail i 1)
      (ow ++ visitAt m lb L tf nJ sample i)) (WalkTimeLoop.A R LW sample tail i))
  rw [dock_cHL cap _ _ _ (walkH_zero n i) (walkH_one n i), dock_cHL cap _ _ _ (walkH_zero n (i + 1))
    (walkH_one n (i + 1)), install_cAL, install_cAL, canonL_coords, canonL_coords] at w1
  unfold canonAt
  rw [swAt_succ]
  exact Step.seq e1 w1

/-! ## All visits -/

/-- The visits' words before visit `i`. -/
def owAt (m lb L tf nJ : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun i' => visitAt m lb L tf nJ sample i'

theorem owAt_length (m lb L tf nJ : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) :
    (owAt m lb L tf nJ sample i).length = i * (1 + nJ * (2 * L + 1)) := by
  induction i with
  | zero => simp [owAt]
  | succ i ih =>
    rw [owAt, List.range_succ, List.flatMap_append, List.length_append, ← owAt, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [visitAt, visitWordL_length]; ring

theorem owAt_succ (m lb L tf nJ : ℕ) {n : ℕ} (sample : MargulisWalkSample (2 ^ m) (n + 1)) (i : ℕ) :
    owAt m lb L tf nJ sample (i + 1) = owAt m lb L tf nJ sample i ++ visitAt m lb L tf nJ sample i := by
  simp [owAt, List.range_succ, List.flatMap_append]

/-- The bank before visit `i`. -/
def loopHL (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ m) (n + 1)) (tail : List Bool)
    (i : ℕ) : Fin (11 + 2 + 19 + 6) → ℕ :=
  cHL cap (canonAt m lb L tf nJ R LW sample tail i (owAt m lb L tf nJ sample i)) (WalkTimeLoop.H n i)

def loopAL (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ m) (n + 1)) (tail : List Bool)
    (i : ℕ) : Fin (11 + 2 + 19 + 6) → List Bool :=
  cAL cap (canonAt m lb L tf nJ R LW sample tail i (owAt m lb L tf nJ sample i)) (WalkTimeLoop.A R LW sample tail i)

/-- The cost of one loop body. -/
def bodyCostL (m lb L nJ R : ℕ) : ℕ := visitLCost m lb L nJ + 1 + (160 * m + 160 * R + 1160)

/-- **All transitions**: the visits `0, …, n−1` are appended to the table. -/
theorem loopStepL (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ m) (n + 1))
    (tail : List Bool) (hR : 2 * m + 1 ≤ R) (hLW : 2 * m + 1 ≤ LW)
    (hpad : tf ≤ 1) (hps : tf ≤ m) (hsd : 2 * lb - 1 + lb ≤ 2 * m - tf) (hlb : 1 ≤ lb) (hnJ : nJ ≤ lb + 1)
    (hcap : 8 * m + 8 * lb + 8 ≤ cap) (hO : (n + 1) * (1 + nJ * (2 * L + 1)) + 5 < cap) :
    Step (RepeatMachine.machine bodyML (fun _ _ => true)) (n * (bodyCostL m lb L nJ R + 3) + 3)
      (Fin.addCases (loopHL cap m lb L tf nJ R LW sample tail 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (loopAL cap m lb L tf nJ R LW sample tail 0) (fun _ : Fin 1 => CompareMachine.word n))
      (Fin.addCases (loopHL cap m lb L tf nJ R LW sample tail n) (fun _ : Fin 1 => 1))
      (Fin.addCases (loopAL cap m lb L tf nJ R LW sample tail n) (fun _ : Fin 1 => CompareMachine.word n)) := by
  refine FixedLivePackets.Materializer.PhysicalRepeatStep.run bodyML n (bodyCostL m lb L nJ R) _ _ ?_
  intro i hi
  have hle : i * (1 + nJ * (2 * L + 1)) ≤ n * (1 + nJ * (2 * L + 1)) := Nat.mul_le_mul_right _ hi.le
  have hex : (n + 1) * (1 + nJ * (2 * L + 1)) = n * (1 + nJ * (2 * L + 1)) + (1 + nJ * (2 * L + 1)) := by ring
  have h := bodyStepL cap m lb L tf nJ R LW sample tail (owAt m lb L tf nJ sample i) i hi hR hLW hpad hps hsd hlb
    hnJ hcap (by rw [owAt_length]; omega)
  unfold loopHL loopAL
  rw [owAt_succ]
  exact h

/-! ## The last visit and the whole builder -/

/-- The last visit, the table's end marker, and the table's head back to its start. -/
def lastL : TProg := .seq visitL (.seq (emitC qO gOP false) (WM.rewind qO gOP))

/-- The machine of the last visit. -/
noncomputable def lastML : Machine (11 + 2 + 19) lastL.toProg.size := lastL.toProg.compile

/-- The final state: the table on `O`, its head and counter at `0`. -/
def finalWL (m lb L tf nJ : ℕ) (sw vw tauw tw : List Bool) : TState :=
  ((canonL m lb L tf nJ sw vw tauw tw).w.seth qO 0).setv gOP 0

theorem lastL_spec (m lb L tf nJ : ℕ) (sw ow : List Bool) (x y : ℕ) (restX restY : List Bool)
    (hsw : sw.length = 2 * m - tf) (hpad : tf ≤ 1) (hps : tf ≤ m) (hsd : 2 * lb - 1 + lb ≤ 2 * m - tf)
    (hlb : 1 ≤ lb) (hnJ : nJ ≤ lb + 1) (hcap : 8 * m + 8 * lb + 8 ≤ cap)
    (hO : ow.length + 1 + nJ * (2 * L + 1) + 6 < cap) :
    WExec cap lastL (canonL m lb L tf nJ sw (frameP (binary m x) ++ restX) (frameP (binary m y) ++ restY) ow).w
      (finalWL m lb L tf nJ (vertexSw m tf x y) (frameP (binary m x) ++ restX) (frameP (binary m y) ++ restY)
        (ow ++ visitWordL m lb L tf nJ x y ++ [false]))
      (visitLCost m lb L nJ + 1 + (7 + 1 + (5 * (ow.length + (1 + nJ * (2 * L + 1)) + 1) + 1))) := by
  have h1 := visitL_canon cap m lb L tf nJ sw ow x y restX restY hsw hpad hps hsd hlb hnJ hcap (by omega)
  obtain ⟨y1, hy1⟩ : ∃ z : LSt, z = canonL m lb L tf nJ (vertexSw m tf x y) (frameP (binary m x) ++ restX)
      (frameP (binary m y) ++ restY) (ow ++ visitWordL m lb L tf nJ x y) := ⟨_, rfl⟩
  rw [← hy1] at h1
  have hl1 : y1.ow.length = ow.length + (1 + nJ * (2 * L + 1)) := by
    rw [hy1]; show (ow ++ visitWordL m lb L tf nJ x y).length = _; rw [List.length_append, visitWordL_length]
  have h2 := emitC_spec cap qO gOP false y1.w rfl (by show y1.ow.length < cap; omega)
  rw [l_o_emit] at h2
  obtain ⟨y2, hy2⟩ : ∃ z : LSt, z = { y1 with ow := y1.ow ++ [false] } := ⟨_, rfl⟩
  rw [← hy2] at h2
  have hl2 : y2.ow.length = ow.length + (1 + nJ * (2 * L + 1)) + 1 := by rw [hy2]; simp [hl1]
  have h3 := wrewind_spec cap qO gOP y2.ow.length y2.w rfl (by show y2.ow.length ≤ cap; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by rw [hl2])
  have e : (y2.w.setv gOP 0).seth qO (y2.w.sh qO - y2.ow.length) = (y2.w.seth qO 0).setv gOP 0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; simp only [WState.setv_sh, WState.seth_sh]
    have hz : y2.w.sh qO - y2.ow.length = 0 := by show y2.ow.length - y2.ow.length = 0; omega
    rw [hz]
  rw [e, hy2, hy1]
  rfl

theorem addCases_assoc6 {α : Type} (f : Fin (11 + 2 + 19) → α) (g : Fin 6 → α) (h : Fin 1 → α) :
    (Fin.addCases (m := 11 + 2 + 19 + 6) (n := 1) (Fin.addCases (m := 11 + 2 + 19) (n := 6) f g) h :
      Fin (11 + 2 + 19 + 7) → α) =
      Fin.addCases (m := 11 + 2 + 19) (n := 7) f (Fin.addCases (m := 6) (n := 1) g h) := by
  funext i
  refine Fin.addCases (m := 11 + 2 + 19) (n := 7) (fun e => ?_) (fun k => ?_) i
  · have hc : (Fin.castAdd 7 e : Fin (11 + 2 + 19 + 7)) = Fin.castAdd 1 (Fin.castAdd 6 e) := Fin.ext rfl
    rw [Fin.addCases_left, hc, Fin.addCases_left, Fin.addCases_left]
  · rw [Fin.addCases_right]
    refine Fin.addCases (m := 6) (n := 1) (fun k' => ?_) (fun z => ?_) k
    · have hc : (Fin.natAdd (11 + 2 + 19) (Fin.castAdd 1 k') : Fin (11 + 2 + 19 + 7)) =
          Fin.castAdd 1 (Fin.natAdd (11 + 2 + 19) k') := Fin.ext rfl
      rw [hc, Fin.addCases_left, Fin.addCases_right, Fin.addCases_left]
    · have hc : (Fin.natAdd (11 + 2 + 19) (Fin.natAdd 6 z) : Fin (11 + 2 + 19 + 7)) =
          Fin.natAdd (11 + 2 + 19 + 6) z := Fin.ext (by simp)
      rw [hc, Fin.addCases_right, Fin.addCases_right]

/-- **The list walk's table builder**: all transitions with their visits, then the last visit. -/
noncomputable def builderML :=
  Composition.machine (RepeatMachine.machine bodyML (fun _ _ => true)) (TapeEmbedding.machine 7 lastML)

/-- The cost of the last visit. -/
def lastCostL (m lb L nJ n : ℕ) : ℕ :=
  visitLCost m lb L nJ + 1 + (7 + 1 + (5 * (n * (1 + nJ * (2 * L + 1)) + (1 + nJ * (2 * L + 1)) + 1) + 1))

/-- **The table builder's run**: from the list seed's walk tapes and an empty table, the table holds every visit's
word and the end marker. -/
theorem builderStepL (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ m) (n + 1))
    (tail : List Bool) (hR : 2 * m + 1 ≤ R) (hLW : 2 * m + 1 ≤ LW)
    (hpad : tf ≤ 1) (hps : tf ≤ m) (hsd : 2 * lb - 1 + lb ≤ 2 * m - tf) (hlb : 1 ≤ lb) (hnJ : nJ ≤ lb + 1)
    (hcap : 8 * m + 8 * lb + 8 ≤ cap) (hO : (n + 1) * (1 + nJ * (2 * L + 1)) + 7 < cap) :
    Step builderML (n * (bodyCostL m lb L nJ R + 3) + 3 + 1 + lastCostL m lb L nJ n)
      (Fin.addCases (loopHL cap m lb L tf nJ R LW sample tail 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (loopAL cap m lb L tf nJ R LW sample tail 0) (fun _ : Fin 1 => CompareMachine.word n))
      (Fin.addCases (m := 11 + 2 + 19) (n := 7)
        (wenc cap (finalWL m lb L tf nJ (swAt m tf sample (n + 1)) (WalkTimeLoop.A R LW sample tail n 0)
          (WalkTimeLoop.A R LW sample tail n 1) (owAt m lb L tf nJ sample (n + 1) ++ [false]))).H
        (Fin.addCases (m := 6) (n := 1) (fun k => WalkTimeLoop.H n n k.succ.succ) (fun _ => 1)))
      (Fin.addCases (m := 11 + 2 + 19) (n := 7)
        (wenc cap (finalWL m lb L tf nJ (swAt m tf sample (n + 1)) (WalkTimeLoop.A R LW sample tail n 0)
          (WalkTimeLoop.A R LW sample tail n 1) (owAt m lb L tf nJ sample (n + 1) ++ [false]))).A
        (Fin.addCases (m := 6) (n := 1) (fun k => WalkTimeLoop.A R LW sample tail n k.succ.succ)
          (fun _ => CompareMachine.word n))) := by
  have hex : (n + 1) * (1 + nJ * (2 * L + 1)) = n * (1 + nJ * (2 * L + 1)) + (1 + nJ * (2 * L + 1)) := by ring
  have h1 := loopStepL cap m lb L tf nJ R LW sample tail hR hLW hpad hps hsd hlb hnJ hcap (by omega)
  have hl := lastL_spec cap m lb L tf nJ (swAt m tf sample n) (owAt m lb L tf nJ sample n)
    (WalkTimeLoop.vertex sample n).1.val (WalkTimeLoop.vertex sample n).2.val
    (false :: List.replicate (R - (2 * m + 1)) false) (false :: List.replicate (R - (2 * m + 1)) false)
    (swAt_length m tf sample n) hpad hps hsd hlb hnJ hcap (by rw [owAt_length]; omega)
  rw [← word_split, ← word_split, ← walkA_zero, ← walkA_one, ← swAt_succ] at hl
  have h2 := ((WExec.exec cap hl).step).embed
    (Fin.addCases (m := 6) (n := 1) (fun k => WalkTimeLoop.H n n k.succ.succ) (fun _ => 1))
    (Fin.addCases (m := 6) (n := 1) (fun k => WalkTimeLoop.A R LW sample tail n k.succ.succ)
      (fun _ => CompareMachine.word n))
  have e1 : Fin.addCases (m := 11 + 2 + 19 + 6) (n := 1) (motive := fun _ => ℕ)
      (loopHL cap m lb L tf nJ R LW sample tail n) (fun _ : Fin 1 => 1) =
      Fin.addCases (m := 11 + 2 + 19) (n := 7) (motive := fun _ => ℕ)
        (wenc cap (canonAt m lb L tf nJ R LW sample tail n (owAt m lb L tf nJ sample n)).w).H
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n n k.succ.succ)
          (fun _ => 1)) := by
    unfold loopHL cHL; exact addCases_assoc6 _ _ _
  have e2 : Fin.addCases (m := 11 + 2 + 19 + 6) (n := 1) (motive := fun _ => List Bool)
      (loopAL cap m lb L tf nJ R LW sample tail n) (fun _ : Fin 1 => CompareMachine.word n) =
      Fin.addCases (m := 11 + 2 + 19) (n := 7) (motive := fun _ => List Bool)
        (wenc cap (canonAt m lb L tf nJ R LW sample tail n (owAt m lb L tf nJ sample n)).w).A
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample tail n k.succ.succ) (fun _ => CompareMachine.word n)) := by
    unfold loopAL cAL; exact addCases_assoc6 _ _ _
  rw [e1, e2] at h1
  have e3 : owAt m lb L tf nJ sample n ++ visitWordL m lb L tf nJ (WalkTimeLoop.vertex sample n).1.val
      (WalkTimeLoop.vertex sample n).2.val ++ [false] = owAt m lb L tf nJ sample (n + 1) ++ [false] := by
    rw [owAt_succ]; rfl
  rw [e3] at h2
  refine (Step.seq h1 h2).enlarge ?_
  rw [owAt_length]; unfold lastCostL; omega

end NearCubicWires.WireExponent3_5.FinalPass.Flat
