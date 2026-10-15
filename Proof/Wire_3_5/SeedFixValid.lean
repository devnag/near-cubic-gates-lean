import Proof.Wire_3_5.SeedFixCells

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open Split Cells

namespace Valid

/-! ## Slot maps (tapes 0 the count ruler, 1 the label stream, 2 the label register, 3 the bound `Q − 1`, 4 the
comparison cell, 5 the validity cell, 6 a unit cell, 7 a log) -/

def v8F : Fin 3 → Fin 8 := ![1, 2, 7]

theorem install_v8F (A : Fin 8 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install v8F A v = ![A 0, v 0, v 1, A 3, A 4, A 5, A 6, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_v8F (H : Fin 8 → ℕ) (v : Fin 3 → ℕ) :
    dockH v8F H v = ![H 0, v 0, v 1, H 3, H 4, H 5, H 6, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def v8C : Fin 4 → Fin 8 := ![2, 3, 4, 7]

theorem install_v8C (A : Fin 8 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install v8C A v = ![A 0, A 1, v 0, v 1, v 2, A 5, A 6, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_v8C (H : Fin 8 → ℕ) (v : Fin 4 → ℕ) :
    dockH v8C H v = ![H 0, H 1, v 0, v 1, v 2, H 5, H 6, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def v8A : Fin 3 → Fin 8 := ![5, 4, 6]

theorem install_v8A (A : Fin 8 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install v8A A v = ![A 0, A 1, A 2, A 3, v 1, v 0, v 2, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_v8A (H : Fin 8 → ℕ) (v : Fin 3 → ℕ) :
    dockH v8A H v = ![H 0, H 1, H 2, H 3, v 1, v 0, v 2, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def v8N : Fin 1 → Fin 8 := ![0]

theorem install_v8N (A : Fin 8 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install v8N A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_v8N (H : Fin 8 → ℕ) (v : Fin 1 → ℕ) :
    dockH v8N H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

/-! ## One label -/

/-- The comparison `a ≤ q` of equal-width words (`foldCmp_rel`). -/
def cmpQ (q a : List Bool) : Bool := foldBits cmpStep true a q

def labAt (x0 : List Bool) (as : List (List Bool)) (i : ℕ) : List Bool := if i = 0 then x0 else as.getD (i - 1) []
def ccAt (c0 : Bool) (q : List Bool) (as : List (List Bool)) (i : ℕ) : Bool :=
  if i = 0 then c0 else cmpQ q (as.getD (i - 1) [])

def validH (as : List (List Bool)) (i : ℕ) : Fin 8 → ℕ := ![i, ((as.take i).flatMap frame).length, 0, 0, 0, 0, 0, 0]

def validA (R8 S x0 q : List Bool) (c0 : Bool) (as : List (List Bool)) (cL i : ℕ) : Fin 8 → List Bool :=
  ![R8, S, frame (labAt x0 as i), frame q, [ccAt c0 q as i], [(as.take i).all (cmpQ q)], [true], List.replicate cL false]

def selLab : Fin 2 → Bool := ![false, true]
def selLQ : Fin 3 → Bool := ![true, true, false]
def andOp : Bool → Bool → Bool → Bool := fun v c _ => v && c
def setOp : Bool → Bool → Bool → Bool := fun _ _ _ => true

/-- One label: copied into the register, compared with `Q − 1`, folded into the validity cell; one ruler step. -/
noncomputable def validBody :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine v8F (MaskedReset.machine frameT selLab))
    (RecoveryFocus.machine v8C (MaskedReset.machine (FoldCell.machine cmpStep true) selLQ)))
    (RecoveryFocus.machine v8A (CellOp.machine andOp))) (RecoveryFocus.machine v8N nudgeM)

def validCost (r : ℕ) : ℕ := (2 * (2 * r + 1 + 1 + 1) + 2) + 1 + (2 * (2 * r + 1) + 2) + 1 + 1 + 1 + 1

theorem valid_step (r : ℕ) (R8 S x0 q tail : List Bool) (c0 : Bool) (as : List (List Bool)) (cL : ℕ)
    (hS : S = as.flatMap frame ++ tail) (has : ∀ a ∈ as, a.length = r) (hx : x0.length = r) (hq : q.length = r)
    (hcL : 2 * r + 1 + 1 + 1 ≤ cL) (i : ℕ) (hi : i < as.length) :
    Step validBody (validCost r) (validH as i) (validA R8 S x0 q c0 as cL i) (validH as (i + 1))
      (validA R8 S x0 q c0 as cL (i + 1)) := by
  set a := as[i]
  set pre := (as.take i).flatMap frame
  set vi := (as.take i).all (cmpQ q)
  have hal : a.length = r := has a (List.getElem_mem hi)
  have hlab : (labAt x0 as i).length = r := by
    unfold labAt
    split
    · exact hx
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact has _ (List.getElem_mem _)
  have eS : S = pre ++ frame a ++ ((as.drop (i + 1)).flatMap frame ++ tail) := by
    have e : as = as.take i ++ a :: as.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    rw [hS]
    conv_lhs => rw [e]
    simp [pre, List.append_assoc]
  -- 1: the label into the register
  have h1 := frameT_run pre a ((as.drop (i + 1)).flatMap frame ++ tail) [] (frame (labAt x0 as i))
  rw [← eS] at h1
  have eL : overlay ([] ++ frame a) (frame (labAt x0 as i)) = frame a := by
    simp [overlay, frame_length, hal, hlab]
  rw [eL] at h1
  have hm1 := h1.mask (cap := cL) selLab (by intro j hj; fin_cases j <;> first | rfl | simp [selLab] at hj)
    (by rw [hal]; exact hcL)
  have hm1' : Step (MaskedReset.machine frameT selLab) (2 * (2 * a.length + 1 + 1 + 1) + 2)
      ![pre.length, 0, 0] ![S, frame (labAt x0 as i), List.replicate cL false]
      ![pre.length + (frame a).length, 0, 0] ![S, frame a, List.replicate cL false] := by
    refine (hm1.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s1 := dockRun hm1' v8F (by decide) (validH as i) (validA R8 S x0 q c0 as cL i)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_v8F, install_v8F] at s1
  -- 2: the comparison with `Q − 1`
  have hC := FoldCell.run cmpStep true a q (ccAt c0 q as i) (by rw [hal, hq])
  have hm2 := hC.mask (cap := cL) selLQ (by intro j _; fin_cases j <;> rfl)
    (by rw [hal]; omega)
  have hm2' : Step (MaskedReset.machine (FoldCell.machine cmpStep true) selLQ) (2 * (2 * a.length + 1) + 2)
      ![0, 0, 0, 0] ![frame a, frame q, [ccAt c0 q as i], List.replicate cL false]
      ![0, 0, 0, 0] ![frame a, frame q, [cmpQ q a], List.replicate cL false] := by
    refine (hm2.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s2 := dockRun hm2' v8C (by decide) ![i, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0]
    ![R8, S, frame a, frame q, [ccAt c0 q as i], [vi], [true], List.replicate cL false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_v8C, install_v8C] at s2
  -- 3: the validity cell
  have s3 := dockRun (CellOp.run andOp vi (cmpQ q a) true) v8A (by decide)
    ![i, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0]
    ![R8, S, frame a, frame q, [cmpQ q a], [vi], [true], List.replicate cL false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_v8A, install_v8A] at s3
  -- 4: one ruler step
  have s4 := dockRun (nudge_run R8 i) v8N (by decide) ![i, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0]
    ![R8, S, frame a, frame q, [cmpQ q a], [vi && cmpQ q a], [true], List.replicate cL false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_v8N, install_v8N] at s4
  have hall := (((s1.congr (hout' := ![i, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0])
      (tout' := ![R8, S, frame a, frame q, [ccAt c0 q as i], [vi], [true], List.replicate cL false])
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := ![i, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0])
      (tout' := ![R8, S, frame a, frame q, [cmpQ q a], [vi], [true], List.replicate cL false])
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq
    (s3.congr (hout' := ![i, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0])
      (tout' := ![R8, S, frame a, frame q, [cmpQ q a], [vi && cmpQ q a], [true], List.replicate cL false])
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq s4
  have eLab : labAt x0 as (i + 1) = a := by
    simp only [labAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have eCC : ccAt c0 q as (i + 1) = cmpQ q a := by
    simp only [ccAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have eTake : as.take (i + 1) = as.take i ++ [a] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
  have eAll : (as.take (i + 1)).all (cmpQ q) = (vi && cmpQ q a) := by
    rw [eTake, List.all_append]; simp [vi]
  have ePre : ((as.take (i + 1)).flatMap frame).length = pre.length + (frame a).length := by
    rw [eTake, List.flatMap_append]; simp [pre]
  have eH : validH as (i + 1) = ![i + 1, pre.length + (frame a).length, 0, 0, 0, 0, 0, 0] := by
    unfold validH; rw [ePre]
  have eA : validA R8 S x0 q c0 as cL (i + 1) =
      ![R8, S, frame a, frame q, [cmpQ q a], [vi && cmpQ q a], [true], List.replicate cL false] := by
    unfold validA; rw [eLab, eCC, eAll]
  rw [eH, eA]
  unfold validCost
  rw [← hal]
  exact hall.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)

/-! ## The eight labels -/

noncomputable def validLoopM := StreamController.machine validBody 0

theorem validLoop_run (r : ℕ) (r8s S x0 q tail : List Bool) (c0 : Bool) (as : List (List Bool)) (cL : ℕ)
    (hS : S = as.flatMap frame ++ tail) (has : ∀ a ∈ as, a.length = r) (hx : x0.length = r) (hq : q.length = r)
    (hcL : 2 * r + 1 + 1 + 1 ≤ cL) :
    Step validLoopM (as.length * (validCost r + 2) + 1) (validH as 0)
      (validA (List.replicate as.length true ++ false :: r8s) S x0 q c0 as cL 0) (validH as as.length)
      (validA (List.replicate as.length true ++ false :: r8s) S x0 q c0 as cL as.length) := by
  set R8 := List.replicate as.length true ++ false :: r8s
  let L : WhileBody 8 _ :=
    { body := validBody
      tape := 0
      bound := as.length
      H := validH as
      A := validA R8 S x0 q c0 as cL
      cost := fun _ => validCost r
      step := fun i hi => valid_step r R8 S x0 q tail c0 as cL hS has hx hq hcL i hi
      cont := fun i hi => by
        show readTapeBit R8 i = true
        exact read_rep_app as.length i (false :: r8s) hi
      halt := by
        show readTapeBit R8 as.length = false
        simpa using Streaming.read_append (List.replicate as.length true) r8s false }
  have h := L.run
  rw [L.rest_const (validCost r) (fun _ => rfl)] at h
  exact h

def selV8 : Fin 8 → Bool := ![true, true, false, false, false, false, false, false]

/-- **The validity block**: the validity cell set, then the eight labels, every head back at cell 0. -/
noncomputable def validM :=
  MaskedReset.machine (Composition.machine (RecoveryFocus.machine v8A (CellOp.machine setOp)) validLoopM) selV8

def validInnerCost (m r : ℕ) : ℕ := 1 + 1 + (m * (validCost r + 2) + 1)

theorem valid_run (r : ℕ) (r8s S x0 q tail : List Bool) (c0 v0 : Bool) (as : List (List Bool)) (cL cL2 : ℕ)
    (hS : S = as.flatMap frame ++ tail) (has : ∀ a ∈ as, a.length = r) (hx : x0.length = r) (hq : q.length = r)
    (hcL : 2 * r + 1 + 1 + 1 ≤ cL) (hcL2 : validInnerCost as.length r ≤ cL2) :
    Step validM (2 * validInnerCost as.length r + 2) (fun _ => 0)
      ![List.replicate as.length true ++ false :: r8s, S, frame x0, frame q, [c0], [v0], [true],
        List.replicate cL false, List.replicate cL2 false]
      (fun _ => 0)
      ![List.replicate as.length true ++ false :: r8s, S, frame (labAt x0 as as.length), frame q,
        [ccAt c0 q as as.length], [as.all (cmpQ q)], [true], List.replicate cL false, List.replicate cL2 false] := by
  set R8 := List.replicate as.length true ++ false :: r8s
  have s0 := dockRun (CellOp.run setOp v0 c0 true) v8A (by decide) (fun _ => 0)
    ![R8, S, frame x0, frame q, [c0], [v0], [true], List.replicate cL false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_v8A, install_v8A] at s0
  have hl := validLoop_run r r8s S x0 q tail c0 as cL hS has hx hq hcL
  have hall := (s0.congr (hout' := validH as 0) (tout' := validA R8 S x0 q c0 as cL 0)
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> simp [validA, labAt, ccAt, setOp])).seq hl
  have hm := hall.mask (cap := cL2) selV8 (by intro j _; fin_cases j <;> rfl) hcL2
  have eA : validA R8 S x0 q c0 as cL as.length = ![R8, S, frame (labAt x0 as as.length), frame q,
      [ccAt c0 q as as.length], [as.all (cmpQ q)], [true], List.replicate cL false] := by
    unfold validA; rw [List.take_length]
  rw [eA] at hm
  unfold validInnerCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

/-! ## The link: the block's cell is the test `∀ k, α_k < Q` -/

section Link
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
variable (P : SeedParams)

theorem aOf_eq (j : ℕ) (k : Fin 8) : aOf P j k = j / 2 ^ 8 / 2 ^ ((k : ℕ) * P.ell) % 2 ^ P.ell := by
  unfold aOf
  have hk := k.isLt
  have e8 : (2 ^ P.ell) ^ 8 = (2 ^ P.ell) ^ (k : ℕ) * (2 ^ P.ell) ^ (8 - (k : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  rw [e8, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self (2 ^ P.ell) (by omega)), ← pow_mul,
    mul_comm P.ell]

theorem cmpQ_binary (ℓ Q x : ℕ) (hQ : 1 ≤ Q) (hQl : Q ≤ 2 ^ ℓ) :
    cmpQ (binary ℓ (Q - 1)) (binary ℓ x) = decide (x % 2 ^ ℓ < Q) := by
  unfold cmpQ
  rw [foldCmp_rel true _ _ (by simp [binary_length]), ← binary_mod ℓ x]
  apply decide_eq_decide.mpr
  unfold rel
  rw [binary_value _ _ (Nat.mod_lt _ (by positivity)), binary_value _ _ (by omega)]
  simp only [true_and]
  constructor
  · rintro (h | h) <;> omega
  · intro h
    rcases Nat.lt_or_ge (x % 2 ^ ℓ) (Q - 1) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by omega)

/-- **The validity cell of the counter's labels.** -/
theorem valid_eq (j : ℕ) (hQ : 1 ≤ P.Q) :
    (alphasOf P.ell j).all (cmpQ (binary P.ell (P.Q - 1))) = decide (∀ k, aOf P j k < P.Q) := by
  have key : ∀ k : Fin 8, cmpQ (binary P.ell (P.Q - 1)) (binary P.ell (j / 2 ^ 8 / 2 ^ ((k : ℕ) * P.ell))) =
      decide (aOf P j k < P.Q) := by
    intro k
    rw [cmpQ_binary P.ell P.Q _ hQ P.Q_le, aOf_eq]
  unfold alphasOf fields8
  rw [List.all_map, Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h k
    have hk := h k (List.mem_range.2 k.isLt)
    rw [Function.comp_apply, key k] at hk
    simpa using hk
  · intro h k hk
    rw [Function.comp_apply, key ⟨k, List.mem_range.1 hk⟩]
    simpa using h ⟨k, List.mem_range.1 hk⟩

end Link

end Valid

end NearCubicWires.WireExponent3_5.SeedFix
