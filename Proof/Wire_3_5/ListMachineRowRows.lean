import Proof.Wire_3_5.ListMachineWordCopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun atomCode monoBits recW polyWord coefWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## The majority flag -/

theorem read_unary (θ p : ℕ) : readTapeBit (List.replicate θ true ++ [false]) p = decide (p < θ) := by
  by_cases h : p < θ
  · obtain ⟨e, he⟩ : ∃ e, θ = p + 1 + e := ⟨θ - p - 1, by omega⟩
    have e1 : List.replicate θ true ++ [false] = List.replicate p true ++ true :: (List.replicate e true ++ [false]) := by
      rw [he, List.replicate_add, List.replicate_add]; simp [List.append_assoc]
    rw [e1]
    have := Streaming.read_append (List.replicate p true) (List.replicate e true ++ [false]) true
    simp only [List.length_replicate] at this
    rw [this, decide_eq_true h]
  · rw [decide_eq_false h]
    by_cases h2 : p = θ
    · subst h2
      simpa using Streaming.read_append (List.replicate p true) [] false
    · unfold readTapeBit
      rw [List.getD_eq_default]
      simp; omega

/-- **The majority flag** `[θ ≤ pop X]`. -/
theorem popge_run (xs : List Bool) (θ : ℕ) (c : Bool) :
    Step PopEq.machine (2 * xs.length + 1) ![0, 0, 0] ![frame xs, List.replicate θ true ++ [false], [c]]
      ![2 * xs.length, Interp.pop xs, 0] ![frame xs, List.replicate θ true ++ [false], [decide (θ ≤ Interp.pop xs)]] := by
  have t := PopEq.timed (List.replicate θ true ++ [false]) c xs [] 0
  simp only [List.nil_append, List.length_nil, Nat.zero_add, read_unary] at t
  obtain ⟨r, hr, hf, _⟩ := t.run rfl
  refine ⟨r, hr, by rw [hf]; rfl, ?_, by omega⟩
  rw [hf]
  have e : (!decide (Interp.pop xs < θ)) = decide (θ ≤ Interp.pop xs) := by
    by_cases h : θ ≤ Interp.pop xs
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false h]; rfl
  rw [e]; rfl

/-! ## The bank -/

structure RB where
  x : List Bool
  z : List Bool
  th : List Bool
  c : List Bool
  fo : List Bool
  cw : List Bool
  st : List Bool
  o : List Bool
  log : List Bool

def RB.tapes (b : RB) : Fin 9 → List Bool := ![b.x, b.z, b.th, b.c, b.fo, b.cw, b.st, b.o, b.log]

/-- The heads: all at `0` but the output's. -/
def rbH (o : ℕ) : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, o, 0]

/-- A masked worker docked into the bank. -/
theorem mdock {k s n cap : ℕ} {p : Machine k s} {hin hout : Fin k → ℕ} {tin tout : Fin k → List Bool}
    (h : Step p n hin tin hout tout) (sel : Fin k → Bool) (hstart : ∀ i, sel i = true → hin i = 0) (hcap : n ≤ cap)
    (slots : Fin (k + 1) → Fin 9) (hi : Function.Injective slots) (H : Fin 9 → ℕ) (A : Fin 9 → List Bool)
    (hH : ∀ j, H (slots j) = Fin.addCases (motive := fun _ => ℕ) hin (fun _ : Fin 1 => 0) j)
    (hA : ∀ j, A (slots j) = Fin.addCases (motive := fun _ => List Bool) tin (fun _ : Fin 1 => List.replicate cap false) j) :
    Step (RecoveryFocus.machine slots (MaskedReset.machine p sel)) (2 * n + 2) H A
      (dockH slots H (Fin.addCases (fun i => if sel i then 0 else hout i) (fun _ : Fin 1 => 0)))
      (install slots A (Fin.addCases tout (fun _ : Fin 1 => List.replicate cap false))) :=
  dockRun (maskRun h sel hstart hcap) slots hi H A hH hA

/-! ## The stages -/

def sPG : Fin 4 → Fin 9 := ![0, 2, 3, 8]
def sCC : Fin 3 → Fin 9 := ![5, 7, 8]
def sSL : Fin 4 → Fin 9 := ![0, 6, 7, 8]
def sRP : Fin 3 → Fin 9 := ![0, 1, 8]
def sAN : Fin 4 → Fin 9 := ![0, 1, 4, 8]
def sO7 : Fin 1 → Fin 9 := ![7]

theorem sPG_inj : Function.Injective sPG := by decide
theorem sCC_inj : Function.Injective sCC := by decide
theorem sSL_inj : Function.Injective sSL := by decide
theorem sRP_inj : Function.Injective sRP := by decide
theorem sAN_inj : Function.Injective sAN := by decide
theorem sO7_inj : Function.Injective sO7 := by decide

noncomputable def popgeM := RecoveryFocus.machine sPG (MaskedReset.machine PopEq.machine ![true, true, false])
noncomputable def coefM := RecoveryFocus.machine sCC (MaskedReset.machine Rec.CopyPast.machine ![true, false])
noncomputable def selMM := RecoveryFocus.machine sSL (MaskedReset.machine selM ![true, true, false])
noncomputable def putOM (b : Bool) := RecoveryFocus.machine sO7 (Put.machine b)
noncomputable def incM :=
  RecoveryFocus.machine sRP (MaskedReset.machine (Block.RippleIn.machine Block.sum3 Block.carry3 true) ![true, true])
noncomputable def anyM := RecoveryFocus.machine sAN (MaskedReset.machine (Block.FoldCell.machine orFold false) ![true, true, false])

/-- The term of the current row. -/
noncomputable def termW := Composition.machine (Composition.machine (Composition.machine (putOM true) coefM) selMM)
  (putOM false)
noncomputable def brTerm := Block.branchM (3 : Fin 9) termW (Block.idle 9)

/-- **One pass.** -/
noncomputable def rowBody := Composition.machine (Composition.machine popgeM brTerm) (Composition.machine incM anyM)

/-! ## Stage lemmas -/

def pPG : Fin 9 → Option (Fin 4) := ![some 0, none, some 1, some 2, none, none, none, none, some 3]
def pCC : Fin 9 → Option (Fin 3) := ![none, none, none, none, none, some 0, none, some 1, some 2]
def pSL : Fin 9 → Option (Fin 4) := ![some 0, none, none, none, none, none, some 1, some 2, some 3]
def pRP : Fin 9 → Option (Fin 3) := ![some 0, some 1, none, none, none, none, none, none, some 2]
def pAN : Fin 9 → Option (Fin 4) := ![some 0, some 1, none, none, some 2, none, none, none, some 3]
def pO7 : Fin 9 → Option (Fin 1) := ![none, none, none, none, none, none, none, some 0, none]

theorem pick_sPG : ∀ i, RecoveryFocus.pick sPG i = pPG i := by pick_table sPG_inj
theorem pick_sCC : ∀ i, RecoveryFocus.pick sCC i = pCC i := by pick_table sCC_inj
theorem pick_sSL : ∀ i, RecoveryFocus.pick sSL i = pSL i := by pick_table sSL_inj
theorem pick_sRP : ∀ i, RecoveryFocus.pick sRP i = pRP i := by pick_table sRP_inj
theorem pick_sAN : ∀ i, RecoveryFocus.pick sAN i = pAN i := by pick_table sAN_inj
theorem pick_sO7 : ∀ i, RecoveryFocus.pick sO7 i = pO7 i := by pick_table sO7_inj

theorem popge_stage (b : RB) (o : ℕ) (xs : List Bool) (θ cap : ℕ) (c : Bool) (hx : b.x = frame xs)
    (hth : b.th = List.replicate θ true ++ [false]) (hc : b.c = [c]) (hl : b.log = List.replicate cap false)
    (hcap : 2 * xs.length + 1 ≤ cap) :
    Step popgeM (2 * (2 * xs.length + 1) + 2) (rbH o) b.tapes (rbH o)
      { b with c := [decide (θ ≤ Interp.pop xs)] }.tapes := by
  have hm := maskRun (popge_run xs θ c) ![true, true, false] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine PopEq.machine ![true, true, false]) (2 * (2 * xs.length + 1) + 2)
      (fun _ => 0) ![frame xs, List.replicate θ true ++ [false], [c], List.replicate cap false]
      (fun _ => 0) ![frame xs, List.replicate θ true ++ [false], [decide (θ ≤ Interp.pop xs)], List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc' sPG sPG_inj (rbH o) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sPG, RB.tapes, hx, hth, hc, hl])
  rw [install_of_pick sPG pPG pick_sPG] at h
  refine h.congr rfl ?_
  funext i; fin_cases i <;> simp [pPG, RB.tapes, hx, hth, hl]

theorem putO_stage (b : RB) (o : List Bool) (B : List Bool) (x : Bool) (ho : b.o = overlay o B) :
    Step (putOM x) 1 (rbH o.length) b.tapes (rbH (o ++ [x]).length) { b with o := overlay (o ++ [x]) B }.tapes := by
  have h := dockRun (Put.run x o B) sO7 sO7_inj (rbH o.length) b.tapes (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; simp [sO7, RB.tapes, ho])
  rw [dockH_of_pick sO7 pO7 pick_sO7, install_of_pick sO7 pO7 pick_sO7] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pO7, rbH]
  · funext i; fin_cases i <;> simp [pO7, RB.tapes]

theorem coef_stage (b : RB) (o B : List Bool) (w tail : List Bool) (cap : ℕ) (hcw : b.cw = frame w ++ tail)
    (ho : b.o = overlay o B) (hl : b.log = List.replicate cap false) (hcap : 2 * w.length + 1 ≤ cap) :
    Step coefM (2 * (2 * w.length + 1) + 2) (rbH o.length) b.tapes (rbH (o ++ frame w).length)
      { b with o := overlay (o ++ frame w) B }.tapes := by
  have hr := Rec.CopyPast.run [] w tail o B
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hr
  have hm := maskRun hr ![true, false] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine Rec.CopyPast.machine ![true, false]) (2 * (2 * w.length + 1) + 2)
      ![0, o.length, 0] ![frame w ++ tail, overlay o B, List.replicate cap false]
      ![0, (o ++ frame w).length, 0] ![frame w ++ tail, overlay (o ++ frame w) B, List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := dockRun hc' sCC sCC_inj (rbH o.length) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sCC, RB.tapes, hcw, ho, hl])
  rw [dockH_of_pick sCC pCC pick_sCC, install_of_pick sCC pCC pick_sCC] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pCC, rbH]
  · funext i; fin_cases i <;> simp [pCC, RB.tapes, hcw, hl]

theorem sel_stage (b : RB) (o B : List Bool) (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ)))
    (hlen : r.length = ps.length) (tail : List Bool) (cap : ℕ) (hx : b.x = frame r) (hst : b.st = stW ps ++ tail)
    (ho : b.o = overlay o B) (hl : b.log = List.replicate cap false)
    (hcap : ((List.range r.length).map fun j => selPass ps j + 2).sum + 1 ≤ cap) :
    Step selMM (2 * (((List.range r.length).map fun j => selPass ps j + 2).sum + 1) + 2) (rbH o.length) b.tapes
      (rbH (o ++ selW r ps).length) { b with o := overlay (o ++ selW r ps) B }.tapes := by
  have hm := maskRun (sel_run r ps hlen tail o B) ![true, true, false] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine selM ![true, true, false])
      (2 * (((List.range r.length).map fun j => selPass ps j + 2).sum + 1) + 2)
      ![0, 0, o.length, 0] ![frame r, stW ps ++ tail, overlay o B, List.replicate cap false]
      ![0, 0, (o ++ selW r ps).length, 0] ![frame r, stW ps ++ tail, overlay (o ++ selW r ps) B, List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := dockRun hc' sSL sSL_inj (rbH o.length) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sSL, RB.tapes, hx, hst, ho, hl])
  rw [dockH_of_pick sSL pSL pick_sSL, install_of_pick sSL pSL pick_sSL] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pSL, rbH]
  · funext i; fin_cases i <;> simp [pSL, RB.tapes, hx, hst, hl]

theorem inc_stage (b : RB) (o : ℕ) (u : List Bool) (cap : ℕ) (hx : b.x = frame u)
    (hz : b.z = frame (List.replicate u.length false)) (hl : b.log = List.replicate cap false)
    (hcap : 2 * u.length + 1 ≤ cap) :
    Step incM (2 * (2 * u.length + 1) + 2) (rbH o) b.tapes (rbH o)
      { b with x := frame (Block.ripple Block.sum3 Block.carry3 true u (List.replicate u.length false)) }.tapes := by
  have hm := maskRun (Block.RippleIn.run Block.sum3 Block.carry3 true u (List.replicate u.length false) (by simp))
    ![true, true] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine (Block.RippleIn.machine Block.sum3 Block.carry3 true) ![true, true])
      (2 * (2 * u.length + 1) + 2)
      (fun _ => 0) ![frame u, frame (List.replicate u.length false), List.replicate cap false]
      (fun _ => 0) ![frame (Block.ripple Block.sum3 Block.carry3 true u (List.replicate u.length false)),
        frame (List.replicate u.length false), List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc' sRP sRP_inj (rbH o) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sRP, RB.tapes, hx, hz, hl])
  rw [install_of_pick sRP pRP pick_sRP] at h
  refine h.congr rfl ?_
  funext i; fin_cases i <;> simp [pRP, RB.tapes, hz, hl]

theorem any_stage (b : RB) (o : ℕ) (u : List Bool) (cap : ℕ) (f0 : Bool) (hx : b.x = frame u)
    (hz : b.z = frame (List.replicate u.length false)) (hfo : b.fo = [f0]) (hl : b.log = List.replicate cap false)
    (hcap : 2 * u.length + 1 ≤ cap) :
    Step anyM (2 * (2 * u.length + 1) + 2) (rbH o) b.tapes (rbH o) { b with fo := [u.any id] }.tapes := by
  have hr := Block.FoldCell.run orFold false u (List.replicate u.length false) f0 (by simp)
  rw [foldBits_orFold u _ (by simp) false, Bool.false_or] at hr
  have hm := maskRun hr ![true, true, false] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine (Block.FoldCell.machine orFold false) ![true, true, false])
      (2 * (2 * u.length + 1) + 2)
      (fun _ => 0) ![frame u, frame (List.replicate u.length false), [f0], List.replicate cap false]
      (fun _ => 0) ![frame u, frame (List.replicate u.length false), [u.any id], List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc' sAN sAN_inj (rbH o) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sAN, RB.tapes, hx, hz, hfo, hl])
  rw [install_of_pick sAN pAN pick_sAN] at h
  refine h.congr rfl ?_
  funext i; fin_cases i <;> simp [pAN, RB.tapes, hx, hz, hl]

/-! ## The loop over the rows -/

/-- The term record of row `i` (`binary t i`), if it has at least `θ` ones. -/
def rowTerm (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (i : ℕ) : List Bool :=
  if θ ≤ Interp.pop (binary t i) then true :: (coefWord c ++ selW (binary t i) ps ++ [false]) else []

/-- What the first `j` passes write. -/
def rowsAt (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) : List Bool :=
  (List.range j).flatMap (rowTerm t θ c ps)

/-- **The rows' term records**, in counter order. -/
def rowsW (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) : List Bool := rowsAt t θ c ps (2 ^ t)

theorem rowsAt_succ (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) :
    rowsAt t θ c ps (j + 1) = rowsAt t θ c ps j ++ rowTerm t θ c ps j := by
  simp [rowsAt, List.range_succ, List.flatMap_append]

/-- The majority cell before pass `j`. -/
def cAt (t θ : ℕ) (c0 : Bool) : ℕ → Bool
  | 0 => c0
  | j + 1 => decide (θ ≤ Interp.pop (binary t j))

/-- The bank before pass `j`. -/
def rbAt (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (tailC tailS o B : List Bool) (cap : ℕ)
    (c0 : Bool) (j : ℕ) : RB :=
  ⟨frame (binary t j), frame (List.replicate t false), List.replicate θ true ++ [false], [cAt t θ c0 j],
    [decide (j < 2 ^ t)], coefWord c ++ tailC, stW ps ++ tailS, overlay (o ++ rowsAt t θ c ps j) B,
    List.replicate cap false⟩

/-- The cost of one term. -/
def termCost (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) : ℕ :=
  ((1 + 1 + (2 * (2 * (decide (c < 0) :: Nat.bits c.natAbs).length + 1) + 2)) + 1 +
    (2 * (((List.range ps.length).map fun j => selPass ps j + 2).sum + 1) + 2)) + 1 + 1

/-- The cost of pass `j`. -/
def rowPass (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) : ℕ :=
  ((2 * (2 * t + 1) + 2) + 1 + ((if θ ≤ Interp.pop (binary t j) then termCost c ps else 0) + 2)) + 1 +
    ((2 * (2 * t + 1) + 2) + 1 + (2 * (2 * t + 1) + 2))

theorem termW_step (b : RB) (o B : List Bool) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (r : List Bool)
    (hlen : r.length = ps.length) (tailC tailS : List Bool) (cap : ℕ) (hx : b.x = frame r)
    (hcw : b.cw = coefWord c ++ tailC) (hst : b.st = stW ps ++ tailS) (ho : b.o = overlay o B)
    (hl : b.log = List.replicate cap false) (hc1 : 2 * (decide (c < 0) :: Nat.bits c.natAbs).length + 1 ≤ cap)
    (hc2 : ((List.range r.length).map fun j => selPass ps j + 2).sum + 1 ≤ cap) :
    Step termW (termCost c ps) (rbH o.length) b.tapes
      (rbH (o ++ (true :: (coefWord c ++ selW r ps ++ [false]))).length)
      { b with o := overlay (o ++ (true :: (coefWord c ++ selW r ps ++ [false]))) B }.tapes := by
  have s1 := putO_stage b o B true ho
  set b1 : RB := { b with o := overlay (o ++ [true]) B } with hb1
  have s2 := coef_stage b1 (o ++ [true]) B (decide (c < 0) :: Nat.bits c.natAbs) tailC cap (by simp [hb1, hcw, coefWord])
    rfl (by simp [hb1, hl]) hc1
  set b2 : RB := { b1 with o := overlay (o ++ [true] ++ frame (decide (c < 0) :: Nat.bits c.natAbs)) B } with hb2
  have s3 := sel_stage b2 (o ++ [true] ++ frame (decide (c < 0) :: Nat.bits c.natAbs)) B r ps hlen tailS cap
    (by simp [hb2, hb1, hx]) (by simp [hb2, hb1, hst]) rfl (by simp [hb2, hb1, hl]) hc2
  set o3 := o ++ [true] ++ frame (decide (c < 0) :: Nat.bits c.natAbs) ++ selW r ps with ho3
  set b3 : RB := { b2 with o := overlay o3 B } with hb3
  have s4 := putO_stage b3 o3 B false rfl
  have t := ((s1.seq s2).seq s3).seq s4
  have e : o3 ++ [false] = o ++ (true :: (coefWord c ++ selW r ps ++ [false])) := by
    rw [ho3]; simp [coefWord, List.append_assoc]
  rw [e] at t
  refine (t.congr rfl ?_).enlarge (le_of_eq ?_)
  · simp [hb3, hb2, hb1]
  · simp only [termCost, hlen]

theorem rowBody_step (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (hps : ps.length = t)
    (tailC tailS o B : List Bool) (cap : ℕ) (c0 : Bool) (hcap0 : 2 * t + 1 ≤ cap)
    (hc1 : 2 * (decide (c < 0) :: Nat.bits c.natAbs).length + 1 ≤ cap)
    (hc2 : ((List.range t).map fun j => selPass ps j + 2).sum + 1 ≤ cap) (j : ℕ) (hj : j < 2 ^ t) :
    Step rowBody (rowPass t θ c ps j) (rbH (o ++ rowsAt t θ c ps j).length) (rbAt t θ c ps tailC tailS o B cap c0 j).tapes
      (rbH (o ++ rowsAt t θ c ps (j + 1)).length) (rbAt t θ c ps tailC tailS o B cap c0 (j + 1)).tapes := by
  set b := rbAt t θ c ps tailC tailS o B cap c0 j with hb
  set o' := o ++ rowsAt t θ c ps j with ho'
  have hbl : (binary t j).length = t := binary_length t j
  have s1 := popge_stage b o'.length (binary t j) θ cap (cAt t θ c0 j) rfl rfl rfl rfl (by rw [hbl]; exact hcap0)
  set flag := decide (θ ≤ Interp.pop (binary t j)) with hflag
  set b1 : RB := { b with c := [flag] } with hb1
  have s2 : Step brTerm ((if θ ≤ Interp.pop (binary t j) then termCost c ps else 0) + 2) (rbH o'.length) b1.tapes
      (rbH (o ++ rowsAt t θ c ps (j + 1)).length) { b1 with o := overlay (o ++ rowsAt t θ c ps (j + 1)) B }.tapes := by
    by_cases hf : θ ≤ Interp.pop (binary t j)
    · have tw := termW_step b1 o' B c ps (binary t j) (by rw [hbl, hps]) tailC tailS cap rfl rfl rfl rfl rfl hc1
        (by rw [hbl]; exact hc2)
      have e : o' ++ (true :: (coefWord c ++ selW (binary t j) ps ++ [false])) = o ++ rowsAt t θ c ps (j + 1) := by
        rw [ho', rowsAt_succ, rowTerm, if_pos hf, List.append_assoc]
      rw [e] at tw
      have := Block.branch_true (3 : Fin 9) (Block.idle 9) tw (by simp [hb1, RB.tapes, rbH, hflag, hf, readTapeBit])
      rwa [if_pos hf]
    · have hi := idle_step (rbH o'.length) b1.tapes
      have e : o ++ rowsAt t θ c ps (j + 1) = o' := by rw [ho', rowsAt_succ, rowTerm, if_neg hf, List.append_nil]
      rw [e, if_neg hf]
      have e2 : ({ b1 with o := overlay o' B } : RB) = b1 := by simp [hb1, hb, rbAt, ho']
      rw [e2]
      exact Block.branch_false (3 : Fin 9) termW hi (by simp [hb1, RB.tapes, rbH, hflag, hf, readTapeBit])
  set b2 : RB := { b1 with o := overlay (o ++ rowsAt t θ c ps (j + 1)) B } with hb2
  have s3 := inc_stage b2 (o ++ rowsAt t θ c ps (j + 1)).length (binary t j) cap rfl (by simp [hb2, hb1, hb, rbAt, hbl])
    rfl (by rw [hbl]; exact hcap0)
  have hinc : Block.ripple Block.sum3 Block.carry3 true (binary t j) (List.replicate (binary t j).length false) =
      binary t (j + 1) := by
    rw [hbl, ← Interp.binary_zero, Block.ripple_add]; simp
  rw [hinc] at s3
  set b3 : RB := { b2 with x := frame (binary t (j + 1)) } with hb3
  have s4 := any_stage b3 (o ++ rowsAt t θ c ps (j + 1)).length (binary t (j + 1)) cap (decide (j < 2 ^ t)) rfl
    (by simp [hb3, hb2, hb1, hb, rbAt]) rfl rfl (by rw [binary_length]; exact hcap0)
  have hany : (binary t (j + 1)).any id = decide (j + 1 < 2 ^ t) := by
    by_cases hlt : j + 1 < 2 ^ t
    · rw [any_binary t (j + 1) hlt]; simp [hlt]
    · have e : j + 1 = 2 ^ t := by omega
      rw [e, Interp.binary_pow]; simp
  rw [hany] at s4
  have tt := (s1.seq s2).seq (s3.seq s4)
  refine (tt.congr rfl ?_).enlarge (le_of_eq ?_)
  · simp [hb3, hb2, hb1, hb, rbAt, cAt, hflag]
  · simp [rowPass, hbl]

/-- **The rows loop.** -/
noncomputable def rowsM := StreamController.machine rowBody (4 : Fin 9)

/-- The cost of the rows loop. -/
def rowsCost (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) : ℕ :=
  ((List.range (2 ^ t)).map fun j => rowPass t θ c ps j + 2).sum + 1

/-- **The truth-table rows**: the output receives `rowsW t θ c ps`. -/
theorem rows_run (t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (hps : ps.length = t)
    (tailC tailS o B : List Bool) (cap : ℕ) (c0 : Bool) (hcap0 : 2 * t + 1 ≤ cap)
    (hc1 : 2 * (decide (c < 0) :: Nat.bits c.natAbs).length + 1 ≤ cap)
    (hc2 : ((List.range t).map fun j => selPass ps j + 2).sum + 1 ≤ cap) :
    Step rowsM (rowsCost t θ c ps) (rbH o.length) (rbAt t θ c ps tailC tailS o B cap c0 0).tapes
      (rbH (o ++ rowsW t θ c ps).length) (rbAt t θ c ps tailC tailS o B cap c0 (2 ^ t)).tapes := by
  have hW := Block.WhileBody.run ({
    body := rowBody
    tape := (4 : Fin 9)
    bound := 2 ^ t
    H := fun j => rbH (o ++ rowsAt t θ c ps j).length
    A := fun j => (rbAt t θ c ps tailC tailS o B cap c0 j).tapes
    cost := rowPass t θ c ps
    step := fun j hj => rowBody_step t θ c ps hps tailC tailS o B cap c0 hcap0 hc1 hc2 j hj
    cont := by intro j hj; simp [rbAt, RB.tapes, rbH, readTapeBit, hj]
    halt := by simp [rbAt, RB.tapes, rbH, readTapeBit] } : Block.WhileBody 9 _)
  have hW' : Step rowsM (((List.range (2 ^ t - 0)).map fun i => rowPass t θ c ps (0 + i) + 2).sum + 1)
      (rbH (o ++ rowsAt t θ c ps 0).length) (rbAt t θ c ps tailC tailS o B cap c0 0).tapes
      (rbH (o ++ rowsAt t θ c ps (2 ^ t)).length) (rbAt t θ c ps tailC tailS o B cap c0 (2 ^ t)).tapes := hW
  simp only [Nat.sub_zero, Nat.zero_add] at hW'
  have e0 : rowsAt t θ c ps 0 = [] := by simp [rowsAt]
  rw [e0, List.append_nil] at hW'
  exact hW'

end NearCubicWires.WireExponent3_5.ListMachine.Row
