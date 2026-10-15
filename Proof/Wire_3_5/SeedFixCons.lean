import Proof.Wire_3_5.SeedFixValid
import Proof.Wire_3_5.SeedFixElimX

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open Split Cells Valid

namespace Cons

/-! ## Slot maps (tapes 0 the sign word, 1 the label stream, 2 the cell stream, 3 the records) -/

def k4B : Fin 1 → Fin 4 := ![0]

theorem install_k4B (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install k4B A v = ![v 0, A 1, A 2, A 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k4B (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) :
    dockH k4B H v = ![v 0, H 1, H 2, H 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def k4C : Fin 2 → Fin 4 := ![0, 3]

theorem install_k4C (A : Fin 4 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install k4C A v = ![v 0, A 1, A 2, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k4C (H : Fin 4 → ℕ) (v : Fin 2 → ℕ) :
    dockH k4C H v = ![v 0, H 1, H 2, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def k4A : Fin 2 → Fin 4 := ![1, 3]

theorem install_k4A (A : Fin 4 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install k4A A v = ![A 0, v 0, A 2, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k4A (H : Fin 4 → ℕ) (v : Fin 2 → ℕ) :
    dockH k4A H v = ![H 0, v 0, H 2, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def k4L : Fin 2 → Fin 4 := ![2, 3]

theorem install_k4L (A : Fin 4 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install k4L A v = ![A 0, A 1, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k4L (H : Fin 4 → ℕ) (v : Fin 2 → ℕ) :
    dockH k4L H v = ![H 0, H 1, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def k4E : Fin 1 → Fin 4 := ![3]

theorem install_k4E (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install k4E A v = ![A 0, A 1, A 2, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k4E (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) :
    dockH k4E H v = ![H 0, H 1, H 2, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

/-! ## One position -/

/-- A set bit: the marker, the label's word, the cell's word. -/
noncomputable def consT := Composition.machine (Composition.machine (RecoveryFocus.machine k4C CopyCell.machine)
  (RecoveryFocus.machine k4A frameT)) (RecoveryFocus.machine k4L frameT)

/-- A clear bit: past the bit, past the label's word, past the cell's word. -/
noncomputable def consF := Composition.machine (Composition.machine (RecoveryFocus.machine k4B nudgeM)
  (RecoveryFocus.machine k4A frameP)) (RecoveryFocus.machine k4L frameP)

def consTCost (a c : ℕ) : ℕ := 1 + 1 + (2 * a + 1 + 1 + 1) + 1 + (2 * c + 1 + 1 + 1)

theorem consT_run (BT AL CL pa a ta pc c tc o B : List Bool) (h0 : ℕ) (hA : AL = pa ++ frame a ++ ta)
    (hC : CL = pc ++ frame c ++ tc) (hb : readTapeBit BT h0 = true) :
    Step consT (consTCost a.length c.length) ![h0, pa.length, pc.length, o.length] ![BT, AL, CL, overlay o B]
      ![h0 + 1, pa.length + (frame a).length, pc.length + (frame c).length, (o ++ true :: (frame a ++ frame c)).length]
      ![BT, AL, CL, overlay (o ++ true :: (frame a ++ frame c)) B] := by
  have h1 := CopyCell.run BT h0 o B
  rw [hb] at h1
  have s1 := dockRun h1 k4C (by decide) ![h0, pa.length, pc.length, o.length] ![BT, AL, CL, overlay o B]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_k4C, install_k4C] at s1
  have h2 := frameT_run pa a ta (o ++ [true]) B
  rw [← hA] at h2
  have s2 := dockRun h2 k4A (by decide) ![h0 + 1, pa.length, pc.length, (o ++ [true]).length]
    ![BT, AL, CL, overlay (o ++ [true]) B] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_k4A, install_k4A] at s2
  have h3 := frameT_run pc c tc (o ++ [true] ++ frame a) B
  rw [← hC] at h3
  have s3 := dockRun h3 k4L (by decide) ![h0 + 1, pa.length + (frame a).length, pc.length, (o ++ [true] ++ frame a).length]
    ![BT, AL, CL, overlay (o ++ [true] ++ frame a) B] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_k4L, install_k4L] at s3
  have hall := ((s1.congr (hout' := ![h0 + 1, pa.length, pc.length, (o ++ [true]).length])
      (tout' := ![BT, AL, CL, overlay (o ++ [true]) B]) (by funext i; fin_cases i <;> simp)
      (by funext i; fin_cases i <;> rfl)).seq
    (s2.congr (hout' := ![h0 + 1, pa.length + (frame a).length, pc.length, (o ++ [true] ++ frame a).length])
      (tout' := ![BT, AL, CL, overlay (o ++ [true] ++ frame a) B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl))).seq s3
  have eo : o ++ [true] ++ frame a ++ frame c = o ++ true :: (frame a ++ frame c) := by simp
  rw [eo] at hall
  refine hall.congr ?_ rfl
  funext i; fin_cases i <;> rfl

theorem consF_run (BT AL CL pa a ta pc c tc o B : List Bool) (h0 : ℕ) (hA : AL = pa ++ frame a ++ ta)
    (hC : CL = pc ++ frame c ++ tc) :
    Step consF (consTCost a.length c.length) ![h0, pa.length, pc.length, o.length] ![BT, AL, CL, overlay o B]
      ![h0 + 1, pa.length + (frame a).length, pc.length + (frame c).length, o.length]
      ![BT, AL, CL, overlay o B] := by
  have s1 := dockRun (nudge_run BT h0) k4B (by decide) ![h0, pa.length, pc.length, o.length] ![BT, AL, CL, overlay o B]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_k4B, install_k4B] at s1
  have h2 := frameP_run pa a ta o B
  rw [← hA] at h2
  have s2 := dockRun h2 k4A (by decide) ![h0 + 1, pa.length, pc.length, o.length]
    ![BT, AL, CL, overlay o B] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_k4A, install_k4A] at s2
  have h3 := frameP_run pc c tc o B
  rw [← hC] at h3
  have s3 := dockRun h3 k4L (by decide) ![h0 + 1, pa.length + (frame a).length, pc.length, o.length]
    ![BT, AL, CL, overlay o B] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [dockH_k4L, install_k4L] at s3
  have hall := ((s1.congr (hout' := ![h0 + 1, pa.length, pc.length, o.length])
      (tout' := ![BT, AL, CL, overlay o B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl)).seq
    (s2.congr (hout' := ![h0 + 1, pa.length + (frame a).length, pc.length, o.length])
      (tout' := ![BT, AL, CL, overlay o B]) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl))).seq s3
  unfold consTCost
  refine hall.congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

/-! ## The eight positions -/

/-- The records of the first `i` positions. -/
def consOut (bs : List Bool) (as cs : List (List Bool)) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun k => if bs.getD k false then true :: (frame (as.getD k []) ++ frame (cs.getD k [])) else []

theorem consOut_succ (bs : List Bool) (as cs : List (List Bool)) (i : ℕ) :
    consOut bs as cs (i + 1) = consOut bs as cs i ++
      (if bs.getD i false then true :: (frame (as.getD i []) ++ frame (cs.getD i [])) else []) := by
  simp [consOut, List.range_succ, List.flatMap_append]

/-- One position: past the pair's marker, then the bit decides. -/
noncomputable def consBody := Composition.machine (RecoveryFocus.machine k4B nudgeM) (branchM (0 : Fin 4) consT consF)

noncomputable def consLoopM := StreamController.machine consBody 0

def consBodyCost (a c : ℕ) : ℕ := 1 + 1 + (consTCost a c + 2)

def consH (bs : List Bool) (as cs : List (List Bool)) (o : List Bool) (i : ℕ) : Fin 4 → ℕ :=
  ![2 * i, ((as.take i).flatMap frame).length, ((cs.take i).flatMap frame).length, (o ++ consOut bs as cs i).length]

def consA (BT AL CL o B : List Bool) (bs : List Bool) (as cs : List (List Bool)) (i : ℕ) : Fin 4 → List Bool :=
  ![BT, AL, CL, overlay (o ++ consOut bs as cs i) B]

theorem frame_read_marker (bs tB : List Bool) (i : ℕ) (hi : i < bs.length) :
    readTapeBit (frame bs ++ tB) (2 * i) = true ∧ readTapeBit (frame bs ++ tB) (2 * i + 1) = bs[i] := by
  have e : bs = bs.take i ++ bs[i] :: bs.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have eP : pairsOf bs = pairsOf (bs.take i) ++ true :: bs[i] :: pairsOf (bs.drop (i + 1)) := by
    conv_lhs => rw [e]
    rw [pairsOf_append]
    rfl
  have eF : frame bs ++ tB = pairsOf (bs.take i) ++ true :: (bs[i] :: (pairsOf (bs.drop (i + 1)) ++ false :: tB)) := by
    rw [frame_pairs, eP]
    simp [List.append_assoc]
  have hl : (pairsOf (bs.take i)).length = 2 * i := by
    rw [pairsOf_length, List.length_take, Nat.min_eq_left (by omega)]
  constructor
  · rw [eF, ← hl]; exact Streaming.read_append _ _ _
  · rw [eF, show 2 * i + 1 = (pairsOf (bs.take i) ++ [true]).length by simp [hl]]
    simpa [List.append_assoc] using Streaming.read_append (pairsOf (bs.take i) ++ [true])
      (pairsOf (bs.drop (i + 1)) ++ false :: tB) bs[i]

theorem frame_read_end (bs tB : List Bool) : readTapeBit (frame bs ++ tB) (2 * bs.length) = false := by
  rw [frame_pairs, ← pairsOf_length]
  simpa [List.append_assoc] using Streaming.read_append (pairsOf bs) tB false

theorem cons_step (ra rc : ℕ) (BT AL CL o B tB tA tC : List Bool) (bs : List Bool) (as cs : List (List Bool))
    (hBT : BT = frame bs ++ tB) (hAL : AL = as.flatMap frame ++ tA) (hCL : CL = cs.flatMap frame ++ tC)
    (has : ∀ a ∈ as, a.length = ra) (hcs : ∀ c ∈ cs, c.length = rc) (hla : as.length = bs.length)
    (hlc : cs.length = bs.length) (i : ℕ) (hi : i < bs.length) :
    Step consBody (consBodyCost ra rc) (consH bs as cs o i) (consA BT AL CL o B bs as cs i) (consH bs as cs o (i + 1))
      (consA BT AL CL o B bs as cs (i + 1)) := by
  have hia : i < as.length := by omega
  have hic : i < cs.length := by omega
  set a := as[i]
  set c := cs[i]
  set pa := (as.take i).flatMap frame
  set pc := (cs.take i).flatMap frame
  set oi := o ++ consOut bs as cs i
  have hal : a.length = ra := has a (List.getElem_mem hia)
  have hcl : c.length = rc := hcs c (List.getElem_mem hic)
  have eA : AL = pa ++ frame a ++ ((as.drop (i + 1)).flatMap frame ++ tA) := by
    have e : as = as.take i ++ a :: as.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hia, List.take_append_drop]
    rw [hAL]
    conv_lhs => rw [e]
    simp [pa, List.append_assoc]
  have eC : CL = pc ++ frame c ++ ((cs.drop (i + 1)).flatMap frame ++ tC) := by
    have e : cs = cs.take i ++ c :: cs.drop (i + 1) := by rw [← List.drop_eq_getElem_cons hic, List.take_append_drop]
    rw [hCL]
    conv_lhs => rw [e]
    simp [pc, List.append_assoc]
  obtain ⟨_, hbit⟩ := frame_read_marker bs tB i hi
  rw [← hBT] at hbit
  have s1 := dockRun (nudge_run BT (2 * i)) k4B (by decide) (consH bs as cs o i) (consA BT AL CL o B bs as cs i)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_k4B, install_k4B] at s1
  have ePa : ((as.take (i + 1)).flatMap frame).length = pa.length + (frame a).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hia, Option.toList_some, List.flatMap_append]; simp [pa, a]
  have ePc : ((cs.take (i + 1)).flatMap frame).length = pc.length + (frame c).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hic, Option.toList_some, List.flatMap_append]; simp [pc, c]
  have eOut : o ++ consOut bs as cs (i + 1) = oi ++ (if bs[i] then true :: (frame a ++ frame c) else []) := by
    rw [consOut_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hic, Option.getD_some, ← List.append_assoc]
  have key : Step (branchM (0 : Fin 4) consT consF) (consTCost ra rc + 2) ![2 * i + 1, pa.length, pc.length, oi.length]
      ![BT, AL, CL, overlay oi B] (consH bs as cs o (i + 1)) (consA BT AL CL o B bs as cs (i + 1)) := by
    have eH : consH bs as cs o (i + 1) = ![2 * i + 1 + 1, pa.length + (frame a).length, pc.length + (frame c).length,
        (oi ++ (if bs[i] then true :: (frame a ++ frame c) else [])).length] := by
      unfold consH; rw [ePa, ePc, eOut]; congr 2
    have eT : consA BT AL CL o B bs as cs (i + 1) =
        ![BT, AL, CL, overlay (oi ++ (if bs[i] then true :: (frame a ++ frame c) else [])) B] := by
      unfold consA; rw [eOut]
    rw [eH, eT]
    cases hb : bs[i]
    · have hF := consF_run BT AL CL pa a ((as.drop (i + 1)).flatMap frame ++ tA) pc c
        ((cs.drop (i + 1)).flatMap frame ++ tC) oi B (2 * i + 1) eA eC
      rw [hal, hcl] at hF
      refine (branch_false (0 : Fin 4) consT hF (by rw [hb] at hbit; exact hbit)).congr ?_ ?_
      · funext j; fin_cases j <;> simp
      · funext j; fin_cases j <;> simp
    · have hT := consT_run BT AL CL pa a ((as.drop (i + 1)).flatMap frame ++ tA) pc c
        ((cs.drop (i + 1)).flatMap frame ++ tC) oi B (2 * i + 1) eA eC (by rw [hb] at hbit; exact hbit)
      rw [hal, hcl] at hT
      refine (branch_true (0 : Fin 4) consF hT (by rw [hb] at hbit; exact hbit)).congr ?_ ?_
      · funext j; fin_cases j <;> simp
      · funext j; fin_cases j <;> simp
  have hall := (s1.congr (hout' := ![2 * i + 1, pa.length, pc.length, oi.length]) (tout' := ![BT, AL, CL, overlay oi B])
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq key
  exact hall

theorem consLoop_run (ra rc : ℕ) (BT AL CL o B tB tA tC : List Bool) (bs : List Bool) (as cs : List (List Bool))
    (hBT : BT = frame bs ++ tB) (hAL : AL = as.flatMap frame ++ tA) (hCL : CL = cs.flatMap frame ++ tC)
    (has : ∀ a ∈ as, a.length = ra) (hcs : ∀ c ∈ cs, c.length = rc) (hla : as.length = bs.length)
    (hlc : cs.length = bs.length) :
    Step consLoopM (bs.length * (consBodyCost ra rc + 2) + 1) (consH bs as cs o 0) (consA BT AL CL o B bs as cs 0)
      (consH bs as cs o bs.length) (consA BT AL CL o B bs as cs bs.length) := by
  let L : WhileBody 4 _ :=
    { body := consBody
      tape := 0
      bound := bs.length
      H := consH bs as cs o
      A := consA BT AL CL o B bs as cs
      cost := fun _ => consBodyCost ra rc
      step := fun i hi => cons_step ra rc BT AL CL o B tB tA tC bs as cs hBT hAL hCL has hcs hla hlc i hi
      cont := fun i hi => by
        show readTapeBit BT (2 * i) = true
        rw [hBT]; exact (frame_read_marker bs tB i hi).1
      halt := by
        show readTapeBit BT (2 * bs.length) = false
        rw [hBT]; exact frame_read_end bs tB }
  have h := L.run
  rw [L.rest_const (consBodyCost ra rc) (fun _ => rfl)] at h
  exact h

def selK4 : Fin 4 → Bool := ![true, true, true, true]

/-- **The record block**: the records of the set positions and a terminator, every head back at cell 0. -/
noncomputable def consM := MaskedReset.machine (Composition.machine consLoopM (RecoveryFocus.machine k4E EndF.machine)) selK4

def consInnerCost (m ra rc : ℕ) : ℕ := m * (consBodyCost ra rc + 2) + 1 + 1 + 1

theorem cons_run (ra rc : ℕ) (BT AL CL B tB tA tC : List Bool) (bs : List Bool) (as cs : List (List Bool)) (cap : ℕ)
    (hBT : BT = frame bs ++ tB) (hAL : AL = as.flatMap frame ++ tA) (hCL : CL = cs.flatMap frame ++ tC)
    (has : ∀ a ∈ as, a.length = ra) (hcs : ∀ c ∈ cs, c.length = rc) (hla : as.length = bs.length)
    (hlc : cs.length = bs.length) (hcap : consInnerCost bs.length ra rc ≤ cap) :
    Step consM (2 * consInnerCost bs.length ra rc + 2) (fun _ => 0) ![BT, AL, CL, B, List.replicate cap false]
      (fun _ => 0) ![BT, AL, CL, overlay (consOut bs as cs bs.length ++ [false]) B, List.replicate cap false] := by
  have hl := consLoop_run ra rc BT AL CL [] B tB tA tC bs as cs hBT hAL hCL has hcs hla hlc
  have hE := dockRun (EndF.run ([] ++ consOut bs as cs bs.length) B) k4E (by decide) (consH bs as cs [] bs.length)
    (consA BT AL CL [] B bs as cs bs.length) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_k4E, install_k4E] at hE
  have hall := (hl.congr_in (hin' := fun _ => 0) (tin' := ![BT, AL, CL, B]) (by funext j; fin_cases j <;> simp [consH, consOut])
    (by funext j; fin_cases j <;> simp [consA, consOut, overlay])).seq hE
  have hm := hall.mask (cap := cap) selK4 (by intro j _; fin_cases j <;> rfl) hcap
  unfold consInnerCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

/-! ## The link: the block's records are the constraints of the counter's `(w, α, β)` -/

theorem filterMap_flatMap_ite {α β γ : Type} (l : List α) (p : α → Bool) (h : α → β) (g : β → List γ) :
    (l.filterMap fun k => if p k then some (h k) else none).flatMap g = l.flatMap fun k => if p k then g (h k) else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases hp : p a <;> simp [hp, ih]

section Link
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
variable (P : SeedParams)

theorem finTwo_val (v : ℕ) (hv : v < 2) : finTwoEquiv ⟨v, hv⟩ = decide (v = 1) := by
  interval_cases v <;> rfl

theorem bOf_eq (j k : ℕ) (hk : k < 8) : bOf j ⟨k, hk⟩ = (binary 8 j).getD k false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [binary_length]; exact hk), Option.getD_some,
    binary_getElem, Nat.testBit_eq_decide_div_mod_eq]
  unfold bOf
  rw [finTwo_val]
  have e8 : 2 ^ 8 = 2 ^ k * 2 ^ (8 - k) := by rw [← pow_add]; congr 1; omega
  rw [e8, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

theorem alphas_getD (j k : ℕ) (hk : k < 8) : (alphasOf P.ell j).getD k [] = binary P.ell (aOf P j ⟨k, hk⟩) := by
  unfold alphasOf fields8
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some,
    aOf_eq, binary_mod]

theorem cells_getD (j k : ℕ) (hk : k < 8) : ((List.finRange 8).map (cellW P j)).getD k [] = cellW P j ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hk), Option.getD_some, List.getElem_map,
    List.getElem_finRange]
  rfl

/-- **The records of the counter's constraints**: the block's output is `consL`'s records, the tape
`consTape` of the elimination. -/
theorem cons_eq (j : ℕ) :
    consOut (binary 8 j) (alphasOf P.ell j) ((List.finRange 8).map (cellW P j)) 8 =
      (consL P.N (aOf P j) (fun k => cellOf (by norm_num) (wOf P j) k) (bOf j)).flatMap
        (consRec P.ell (2 * P.kh)) := by
  set CS := (List.finRange 8).map (cellW P j)
  have key : ∀ k (hk : k < 8), (if (binary 8 j).getD k false then
      true :: (frame ((alphasOf P.ell j).getD k []) ++ frame (CS.getD k [])) else []) =
      (if bOf j ⟨k, hk⟩ then consRec P.ell (2 * P.kh)
        (aOf P j ⟨k, hk⟩, cellNumC (cellOf (by norm_num) (wOf P j) ⟨k, hk⟩)) else []) := by
    intro k hk
    rw [bOf_eq j k hk, alphas_getD P j k hk, cells_getD P j k hk]
    rfl
  unfold consL consOut
  rw [filterMap_flatMap_ite]
  have hF : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  have hR : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hF, hR]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num), key 3 (by norm_num), key 4 (by norm_num),
    key 5 (by norm_num), key 6 (by norm_num), key 7 (by norm_num)]
  rfl

end Link

end Cons

end NearCubicWires.WireExponent3_5.SeedFix
