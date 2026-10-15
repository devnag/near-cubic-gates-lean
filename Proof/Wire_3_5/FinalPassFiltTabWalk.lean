import Proof.Wire_3_5.FinalPassFiltTabZero
import Proof.Packets.PacketsXWalkTimeLoop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.RepairSource.VerifierDecoding Theorem25Completion NearCubicWires.RepairOrdinary.RecoveryRootRound

variable (cap : ℕ)

/-! ## Word states and banks -/

theorem w_vw (x : TSt) (X : List Bool) : x.w.sets qV X = { x with vw := X }.w := by tst_eq

theorem wenc_sets_A {ns nr : ℕ} (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) (j : Fin (ns + 2 + nr)) :
    (wenc cap (σ.sets i l)).A j = if j = sTape i then l else (wenc cap σ).A j := by
  by_cases hj : j = sTape i
  · subst hj; simp [wenc, role_sTape]
  · rw [if_neg hj]
    simp only [wenc, WState.sets_st, WState.sets_val, WState.sets_cell]
    cases hr : role j with
    | stream i' =>
      have hne : i' ≠ i := by rintro rfl; exact hj (role_stream hr)
      simp [Function.update_of_ne hne]
    | cell => rfl
    | reg r => rfl

theorem wenc_sets_H {ns nr : ℕ} (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) :
    (wenc cap (σ.sets i l)).H = (wenc cap σ).H := by
  funext j
  simp only [wenc, WState.sets_sh, WState.sets_val]

/-- The emitter's tape 0 is the vertex word. -/
theorem wencA_zero (y : TSt) : (wenc cap y.w).A ⟨0, by omega⟩ = y.vw := rfl
theorem wencH_zero (y : TSt) : (wenc cap y.w).H ⟨0, by omega⟩ = y.vh := rfl

/-! ## The combined bank -/

/-- The walk's tapes inside the bank: tape `0` is the emitter's tape `0`, tapes `1..7` follow the emitter's. -/
def wslots : Fin 8 → Fin (11 + 2 + 19 + 7) := fun k => if k.val = 0 then ⟨0, by omega⟩ else ⟨31 + k.val, by omega⟩

theorem wslots_val (k : Fin 8) : (wslots k).val = if k.val = 0 then 0 else 31 + k.val := by
  unfold wslots; split <;> rfl

theorem wslots_inj : Function.Injective wslots := by
  intro a b h
  have := congrArg Fin.val h
  rw [wslots_val, wslots_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

/-- The combined tapes: the emitter's, then the walk's tapes `1..7`. -/
def cA (y : TSt) (bk : Fin 8 → List Bool) : Fin (11 + 2 + 19 + 7) → List Bool :=
  Fin.addCases (m := 11 + 2 + 19) (n := 7) (wenc cap y.w).A (fun k => bk k.succ)

/-- The combined heads. -/
def cH (y : TSt) (hk : Fin 8 → ℕ) : Fin (11 + 2 + 19 + 7) → ℕ :=
  Fin.addCases (m := 11 + 2 + 19) (n := 7) (wenc cap y.w).H (fun k => hk k.succ)

theorem wslots_zero : wslots 0 = Fin.castAdd 7 (⟨0, by omega⟩ : Fin (11 + 2 + 19)) := by
  apply Fin.ext; rw [wslots_val]; rfl

theorem wslots_succ (k : Fin 7) : wslots k.succ = Fin.natAdd (11 + 2 + 19) k := by
  apply Fin.ext; rw [wslots_val]; simp [Fin.val_succ]; omega

theorem not_slot (e : Fin (11 + 2 + 19)) (he : e.val ≠ 0) (k : Fin 8) : wslots k ≠ Fin.castAdd 7 e := by
  intro h
  have h1 := congrArg Fin.val h
  rw [wslots_val, Fin.val_castAdd] at h1
  have := e.isLt
  by_cases hk : k.val = 0
  · rw [if_pos hk] at h1; omega
  · rw [if_neg hk] at h1; omega

/-- **The walk transition in the bank** changes the emitter's tapes only at the vertex word. -/
theorem install_cA (y : TSt) (bk bk' : Fin 8 → List Bool) :
    install wslots (cA cap y bk) bk' = cA cap { y with vw := bk' 0 } bk' := by
  funext j
  refine Fin.addCases (fun e => ?_) (fun k => ?_) j
  · by_cases he : e.val = 0
    · have hj : Fin.castAdd 7 e = wslots 0 := by rw [wslots_zero]; congr 1; exact Fin.ext he
      rw [hj, install_slot wslots wslots_inj, ← hj]
      simp only [cA, Fin.addCases_left]
      have hs : e = sTape (ns := 11) (nr := 19) 0 := Fin.ext (by rw [he]; rfl)
      rw [← w_vw y (bk' 0), wenc_sets_A, if_pos hs]
    · rw [install_other wslots _ _ _ (fun k => not_slot e he k)]
      simp only [cA, Fin.addCases_left]
      have hs : ¬ e = sTape (ns := 11) (nr := 19) 0 := fun h => he (by rw [h]; rfl)
      rw [← w_vw y (bk' 0), wenc_sets_A, if_neg hs]
  · rw [← wslots_succ, install_slot wslots wslots_inj]
    simp only [cA, wslots_succ, Fin.addCases_right]

/-- The walk's heads in the bank, when the vertex word's head is the emitter's. -/
theorem dock_cH (y : TSt) (hk hk' : Fin 8 → ℕ) (h0 : hk' 0 = y.vh) :
    dockH wslots (cH cap y hk) hk' = cH cap y hk' := by
  funext j
  refine Fin.addCases (fun e => ?_) (fun k => ?_) j
  · by_cases he : e.val = 0
    · have hj : Fin.castAdd 7 e = wslots 0 := by rw [wslots_zero]; congr 1; exact Fin.ext he
      rw [hj, dockH_slot wslots wslots_inj, ← hj, h0]
      simp only [cH, Fin.addCases_left]
      have : e = ⟨0, by omega⟩ := Fin.ext he
      rw [this]; rfl
    · rw [dockH_other wslots _ _ _ (fun k => not_slot e he k)]
      simp only [cH, Fin.addCases_left]
  · rw [← wslots_succ, dockH_slot wslots wslots_inj]
    simp only [cH, wslots_succ, Fin.addCases_right]

/-! ## One visit and one transition -/

/-- The emitter machine. -/
noncomputable def emitM : Machine (11 + 2 + 19) visitZ.toProg.size := visitZ.toProg.compile

/-- One loop body: a visit, then a walk transition. -/
noncomputable def bodyM :=
  Composition.machine (TapeEmbedding.machine 7 emitM) (RecoveryFocus.machine wslots WalkPoweredRun.machine)

theorem word_eq (r R : ℕ) (x : ZMod (2 ^ r)) :
    WalkEdgeReuse.word r R x = frameP (binary r x.val) ++ false :: List.replicate (R - (2 * r + 1)) false := by
  unfold WalkEdgeReuse.word ZeroPadding.pad FinalWalkStep.coordEncode
  rw [frame_eq_frameP]
  simp [frameP_length]

theorem walkA_zero {r n : ℕ} (R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) (tail : List Bool) (i : ℕ) :
    WalkTimeLoop.A R LW sample tail i 0 = WalkEdgeReuse.word r R (WalkTimeLoop.vertex sample i).1 := rfl

theorem walkH_zero (n i : ℕ) : WalkTimeLoop.H n i 0 = 0 := rfl

theorem canon_vw (m lb a L : ℕ) (tauw pmw vw ow X : List Bool) :
    ({ canon m lb a L tauw pmw vw ow with vw := X } : TSt) = canon m lb a L tauw pmw X ow := rfl

/-- **One loop body**: the visit of vertex `i` is appended to the table, then the walk moves to vertex `i+1`. -/
theorem bodyStep (p tv m lb a L nd : ℕ) (tauw pmw ow : List Bool) {n : ℕ} (R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf m lb * nd)) (n + 1)) (tail : List Bool) (i : ℕ) (hi : i < n)
    (hR : 2 * (wOf m lb * nd) + 1 ≤ R) (hLW : 2 * (wOf m lb * nd) + 1 ≤ LW)
    (hn : 1 ≤ nd) (hm : 1 ≤ m) (hlb : 1 ≤ lb) (ha : a ≤ lb)
    (htau : tauw = frame (binary m tv)) (hpm : pmw = frame (binary m p))
    (hcap : 2 * (wOf m lb * nd) + 4 * lb + 2 * m + L + 10 ≤ cap) (hO : ow.length + nd * (2 * L + 2) + 8 < cap) :
    Step bodyM (visitZCost m lb a L nd + 1 + (160 * (wOf m lb * nd) + 160 * R + 1160))
      (cH cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail i 0) ow) (WalkTimeLoop.H n i))
      (cA cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail i 0) ow) (WalkTimeLoop.A R LW sample tail i))
      (cH cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail (i + 1) 0)
        (ow ++ visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample i).1.val L nd))) (WalkTimeLoop.H n (i + 1)))
      (cA cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail (i + 1) 0)
        (ow ++ visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample i).1.val L nd)))
        (WalkTimeLoop.A R LW sample tail (i + 1))) := by
  -- the visit
  have hv := visitZ_spec cap p tv (WalkTimeLoop.vertex sample i).1.val nd m lb a L
    (false :: List.replicate (R - (2 * (wOf m lb * nd) + 1)) false) tauw pmw ow ⟨_, rfl⟩ hn hm hlb ha htau hpm hcap hO
  rw [← word_eq, ← walkA_zero] at hv
  have e1 := ((WExec.exec cap hv).step).embed (fun k => WalkTimeLoop.H n i k.succ)
    (fun k => WalkTimeLoop.A R LW sample tail i k.succ)
  -- the transition
  have w1 := (WalkTimeLoop.iteration R LW sample tail i hi hR hLW).focus wslots wslots_inj
    (cH cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail i 0)
      (ow ++ visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample i).1.val L nd))) (WalkTimeLoop.H n i))
    (cA cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail i 0)
      (ow ++ visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample i).1.val L nd)))
      (WalkTimeLoop.A R LW sample tail i))
  rw [dock_cH cap _ _ _ (walkH_zero n i), dock_cH cap _ _ _ (walkH_zero n (i + 1)), install_cA, install_cA,
    canon_vw, canon_vw] at w1
  exact Step.seq e1 w1

/-! ## All visits -/

/-- The visits' words before visit `i`. -/
def owOf (p tv m lb a L nd : ℕ) {r n : ℕ} (sample : MargulisWalkSample (2 ^ r) (n + 1)) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun i' => visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample i').1.val L nd)

theorem visitWord_length (vs : List (List Bool)) : (visitWord vs).length = (vs.flatMap copyWord).length + 2 := by
  simp [visitWord]

theorem copyList_flat_length (p m lb a tv X L nd : ℕ) :
    ((copyList p m lb a tv X L nd).flatMap copyWord).length = nd * (2 * L + 2) := by
  rw [← copiesOut_eq, copiesOut_length]

theorem owOf_length (p tv m lb a L nd : ℕ) {r n : ℕ} (sample : MargulisWalkSample (2 ^ r) (n + 1)) (i : ℕ) :
    (owOf p tv m lb a L nd sample i).length = i * (nd * (2 * L + 2) + 2) := by
  induction i with
  | zero => simp [owOf]
  | succ i ih =>
    rw [owOf, List.range_succ, List.flatMap_append, List.length_append, ← owOf, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [visitWord_length, copyList_flat_length]; ring

theorem owOf_succ (p tv m lb a L nd : ℕ) {r n : ℕ} (sample : MargulisWalkSample (2 ^ r) (n + 1)) (i : ℕ) :
    owOf p tv m lb a L nd sample (i + 1) = owOf p tv m lb a L nd sample i ++
      visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample i).1.val L nd) := by
  simp [owOf, List.range_succ, List.flatMap_append]

/-- The bank before visit `i`. -/
def loopH (m lb a L : ℕ) (tauw pmw : List Bool) (p tv nd : ℕ) {r n : ℕ} (R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ r) (n + 1)) (tail : List Bool) (i : ℕ) : Fin (11 + 2 + 19 + 7) → ℕ :=
  cH cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail i 0) (owOf p tv m lb a L nd sample i))
    (WalkTimeLoop.H n i)

def loopA (m lb a L : ℕ) (tauw pmw : List Bool) (p tv nd : ℕ) {r n : ℕ} (R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ r) (n + 1)) (tail : List Bool) (i : ℕ) : Fin (11 + 2 + 19 + 7) → List Bool :=
  cA cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail i 0) (owOf p tv m lb a L nd sample i))
    (WalkTimeLoop.A R LW sample tail i)

/-- The cost of one loop body. -/
def bodyCost (m lb a L nd R : ℕ) : ℕ := visitZCost m lb a L nd + 1 + (160 * (wOf m lb * nd) + 160 * R + 1160)

/-- **All transitions**: the visits `0, …, n−1` are appended to the table. -/
theorem loopStep (p tv m lb a L nd : ℕ) (tauw pmw : List Bool) {n : ℕ} (R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf m lb * nd)) (n + 1)) (tail : List Bool)
    (hR : 2 * (wOf m lb * nd) + 1 ≤ R) (hLW : 2 * (wOf m lb * nd) + 1 ≤ LW)
    (hn : 1 ≤ nd) (hm : 1 ≤ m) (hlb : 1 ≤ lb) (ha : a ≤ lb)
    (htau : tauw = frame (binary m tv)) (hpm : pmw = frame (binary m p))
    (hcap : 2 * (wOf m lb * nd) + 4 * lb + 2 * m + L + 10 ≤ cap)
    (hO : (n + 1) * (nd * (2 * L + 2) + 2) + 8 < cap) :
    Step (RepeatMachine.machine bodyM (fun _ _ => true)) (n * (bodyCost m lb a L nd R + 3) + 3)
      (Fin.addCases (loopH cap m lb a L tauw pmw p tv nd R LW sample tail 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (loopA cap m lb a L tauw pmw p tv nd R LW sample tail 0) (fun _ : Fin 1 => CompareMachine.word n))
      (Fin.addCases (loopH cap m lb a L tauw pmw p tv nd R LW sample tail n) (fun _ : Fin 1 => 1))
      (Fin.addCases (loopA cap m lb a L tauw pmw p tv nd R LW sample tail n) (fun _ : Fin 1 => CompareMachine.word n)) := by
  refine FixedLivePackets.Materializer.PhysicalRepeatStep.run bodyM n (bodyCost m lb a L nd R) _ _ ?_
  intro i hi
  have hle : i * (nd * (2 * L + 2) + 2) ≤ n * (nd * (2 * L + 2) + 2) := Nat.mul_le_mul_right _ hi.le
  have hex : (n + 1) * (nd * (2 * L + 2) + 2) = n * (nd * (2 * L + 2) + 2) + nd * (2 * L + 2) + 2 := by ring
  have h := bodyStep cap p tv m lb a L nd tauw pmw (owOf p tv m lb a L nd sample i) R LW sample tail i hi hR hLW hn hm
    hlb ha htau hpm hcap (by rw [owOf_length]; omega)
  unfold loopH loopA
  rw [owOf_succ]
  exact h

/-! ## The last visit and the whole builder -/

/-- The last visit, the table's end marker, and the table's head back to its start. -/
def lastZ : TProg := .seq visitZ (.seq (emitC qO gOP false) (WM.rewind qO gOP))

/-- The machine of the last visit. -/
noncomputable def lastM : Machine (11 + 2 + 19) lastZ.toProg.size := lastZ.toProg.compile

theorem canon_ow (m lb a L : ℕ) (tauw pmw vw ow X : List Bool) :
    ({ canon m lb a L tauw pmw vw ow with ow := X } : TSt) = canon m lb a L tauw pmw vw X := rfl

/-- The final state: the table on `O`, its head and counter at `0`. -/
def finalW (m lb a L : ℕ) (tauw pmw vw tw : List Bool) : TState :=
  ((canon m lb a L tauw pmw vw tw).w.seth qO 0).setv gOP 0

theorem lastZ_spec (p tv X nd m lb a L : ℕ) (restV tauw pmw ow : List Bool) (hrest : ∃ t, restV = false :: t)
    (hn : 1 ≤ nd) (hm : 1 ≤ m) (hlb : 1 ≤ lb) (ha : a ≤ lb)
    (htau : tauw = frame (binary m tv)) (hpm : pmw = frame (binary m p))
    (hcap : 2 * (wOf m lb * nd) + 4 * lb + 2 * m + L + 10 ≤ cap) (hO : ow.length + nd * (2 * L + 2) + 12 < cap) :
    WExec cap lastZ (canon m lb a L tauw pmw (frameP (binary (wOf m lb * nd) X) ++ restV) ow).w
      (finalW m lb a L tauw pmw (frameP (binary (wOf m lb * nd) X) ++ restV)
        (ow ++ visitWord (copyList p m lb a tv X L nd) ++ [false]))
      (visitZCost m lb a L nd + 1 + (7 + 1 + (5 * (ow.length + nd * (2 * L + 2) + 3) + 1))) := by
  have h1 := visitZ_spec cap p tv X nd m lb a L restV tauw pmw ow hrest hn hm hlb ha htau hpm hcap (by omega)
  obtain ⟨y1, hy1⟩ : ∃ y : TSt, y = canon m lb a L tauw pmw (frameP (binary (wOf m lb * nd) X) ++ restV)
      (ow ++ visitWord (copyList p m lb a tv X L nd)) := ⟨_, rfl⟩
  rw [← hy1] at h1
  have hl1 : y1.ow.length = ow.length + nd * (2 * L + 2) + 2 := by
    rw [hy1]; show (ow ++ visitWord _).length = _; rw [List.length_append, visitWord_length, copyList_flat_length]; ring
  have h2 := emitC_spec cap qO gOP false y1.w rfl (by show y1.ow.length < cap; omega)
  rw [w_o_emit] at h2
  obtain ⟨y2, hy2⟩ : ∃ y : TSt, y = { y1 with ow := y1.ow ++ [false] } := ⟨_, rfl⟩
  rw [← hy2] at h2
  have hl2 : y2.ow.length = ow.length + nd * (2 * L + 2) + 3 := by rw [hy2]; simp [hl1]
  have h3 := wrewind_spec cap qO gOP y2.ow.length y2.w rfl (by show y2.ow.length ≤ cap; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by rw [hl2])
  have e : (y2.w.setv gOP 0).seth qO (y2.w.sh qO - y2.ow.length) = (y2.w.seth qO 0).setv gOP 0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext i; simp only [WState.setv_sh, WState.seth_sh]
    have hz : y2.w.sh qO - y2.ow.length = 0 := by show y2.ow.length - y2.ow.length = 0; omega
    rw [hz]
  rw [e, hy2, hy1, canon_ow]
  rfl

theorem addCases_assoc {α : Type} (f : Fin (11 + 2 + 19) → α) (g : Fin 7 → α) (h : Fin 1 → α) :
    (Fin.addCases (m := 11 + 2 + 19 + 7) (n := 1) (Fin.addCases (m := 11 + 2 + 19) (n := 7) f g) h :
      Fin (11 + 2 + 19 + 8) → α) =
      Fin.addCases (m := 11 + 2 + 19) (n := 8) f (Fin.addCases (m := 7) (n := 1) g h) := by
  funext i
  refine Fin.addCases (m := 11 + 2 + 19) (n := 8) (fun e => ?_) (fun k => ?_) i
  · have hc : (Fin.castAdd 8 e : Fin (11 + 2 + 19 + 8)) = Fin.castAdd 1 (Fin.castAdd 7 e) := Fin.ext rfl
    rw [Fin.addCases_left, hc, Fin.addCases_left, Fin.addCases_left]
  · rw [Fin.addCases_right]
    refine Fin.addCases (m := 7) (n := 1) (fun k' => ?_) (fun z => ?_) k
    · have hc : (Fin.natAdd (11 + 2 + 19) (Fin.castAdd 1 k') : Fin (11 + 2 + 19 + 8)) =
          Fin.castAdd 1 (Fin.natAdd (11 + 2 + 19) k') := Fin.ext rfl
      rw [hc, Fin.addCases_left, Fin.addCases_right, Fin.addCases_left]
    · have hc : (Fin.natAdd (11 + 2 + 19) (Fin.natAdd 7 z) : Fin (11 + 2 + 19 + 8)) =
          Fin.natAdd (11 + 2 + 19 + 7) z := Fin.ext (by simp)
      rw [hc, Fin.addCases_right, Fin.addCases_right]

/-- **The table builder**: all transitions with their visits, then the last visit. -/
noncomputable def builderM :=
  Composition.machine (RepeatMachine.machine bodyM (fun _ _ => true)) (TapeEmbedding.machine 8 lastM)

/-- The cost of the last visit. -/
def lastCost (m lb a L nd n : ℕ) : ℕ :=
  visitZCost m lb a L nd + 1 + (7 + 1 + (5 * (n * (nd * (2 * L + 2) + 2) + nd * (2 * L + 2) + 3) + 1))

/-- **The table builder's run**: from the seed's walk tapes and a blank table, the table holds every visit's word
and the end marker. -/
theorem builderStep (p tv m lb a L nd : ℕ) (tauw pmw : List Bool) {n : ℕ} (R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf m lb * nd)) (n + 1)) (tail : List Bool)
    (hR : 2 * (wOf m lb * nd) + 1 ≤ R) (hLW : 2 * (wOf m lb * nd) + 1 ≤ LW)
    (hn : 1 ≤ nd) (hm : 1 ≤ m) (hlb : 1 ≤ lb) (ha : a ≤ lb)
    (htau : tauw = frame (binary m tv)) (hpm : pmw = frame (binary m p))
    (hcap : 2 * (wOf m lb * nd) + 4 * lb + 2 * m + L + 10 ≤ cap)
    (hO : (n + 1) * (nd * (2 * L + 2) + 2) + 12 < cap) :
    Step builderM (n * (bodyCost m lb a L nd R + 3) + 3 + 1 + lastCost m lb a L nd n)
      (Fin.addCases (loopH cap m lb a L tauw pmw p tv nd R LW sample tail 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (loopA cap m lb a L tauw pmw p tv nd R LW sample tail 0) (fun _ : Fin 1 => CompareMachine.word n))
      (Fin.addCases (m := 11 + 2 + 19) (n := 8)
        (wenc cap (finalW m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail n 0)
          (owOf p tv m lb a L nd sample (n + 1) ++ [false]))).H
        (Fin.addCases (m := 7) (n := 1) (fun k => WalkTimeLoop.H n n k.succ) (fun _ => 1)))
      (Fin.addCases (m := 11 + 2 + 19) (n := 8)
        (wenc cap (finalW m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail n 0)
          (owOf p tv m lb a L nd sample (n + 1) ++ [false]))).A
        (Fin.addCases (m := 7) (n := 1) (fun k => WalkTimeLoop.A R LW sample tail n k.succ)
          (fun _ => CompareMachine.word n))) := by
  have h1 := loopStep cap p tv m lb a L nd tauw pmw R LW sample tail hR hLW hn hm hlb ha htau hpm hcap (by omega)
  have hl := lastZ_spec cap p tv (WalkTimeLoop.vertex sample n).1.val nd m lb a L
    (false :: List.replicate (R - (2 * (wOf m lb * nd) + 1)) false) tauw pmw (owOf p tv m lb a L nd sample n) ⟨_, rfl⟩
    hn hm hlb ha htau hpm hcap (by rw [owOf_length]; nlinarith)
  rw [← word_eq, ← walkA_zero] at hl
  have h2 := ((WExec.exec cap hl).step).embed
    (Fin.addCases (m := 7) (n := 1) (fun k => WalkTimeLoop.H n n k.succ) (fun _ => 1))
    (Fin.addCases (m := 7) (n := 1) (fun k => WalkTimeLoop.A R LW sample tail n k.succ)
      (fun _ => CompareMachine.word n))
  have e1 : Fin.addCases (m := 11 + 2 + 19 + 7) (n := 1) (motive := fun _ => ℕ)
      (loopH cap m lb a L tauw pmw p tv nd R LW sample tail n) (fun _ : Fin 1 => 1) =
      Fin.addCases (m := 11 + 2 + 19) (n := 8) (motive := fun _ => ℕ)
        (wenc cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail n 0)
          (owOf p tv m lb a L nd sample n)).w).H
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n n k.succ) (fun _ => 1)) := by
    unfold loopH cH; exact addCases_assoc _ _ _
  have e2 : Fin.addCases (m := 11 + 2 + 19 + 7) (n := 1) (motive := fun _ => List Bool)
      (loopA cap m lb a L tauw pmw p tv nd R LW sample tail n) (fun _ : Fin 1 => CompareMachine.word n) =
      Fin.addCases (m := 11 + 2 + 19) (n := 8) (motive := fun _ => List Bool)
        (wenc cap (canon m lb a L tauw pmw (WalkTimeLoop.A R LW sample tail n 0)
          (owOf p tv m lb a L nd sample n)).w).A
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool) (fun k => WalkTimeLoop.A R LW sample tail n k.succ)
          (fun _ => CompareMachine.word n)) := by
    unfold loopA cA; exact addCases_assoc _ _ _
  rw [e1, e2] at h1
  have e3 : owOf p tv m lb a L nd sample n ++ visitWord (copyList p m lb a tv (WalkTimeLoop.vertex sample n).1.val L nd)
      ++ [false] = owOf p tv m lb a L nd sample (n + 1) ++ [false] := by rw [owOf_succ]
  rw [e3] at h2
  refine (Step.seq h1 h2).enlarge ?_
  rw [owOf_length]; unfold lastCost; ring_nf; omega

end NearCubicWires.WireExponent3_5.FinalPass.Filt
