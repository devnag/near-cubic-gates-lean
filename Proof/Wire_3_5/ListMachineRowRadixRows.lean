import Proof.Wire_3_5.ListMachineRowRadixSel

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun atomCode monoBits recW polyWord coefWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm (WExec WState wenc regTape Exec role sTape cTape rTape)

/-! ## The two programs as machine steps -/

/-- The residue test's machine. -/
def resRM := (resP).toProg.compile
/-- The odometer's machine. -/
def incRM := (incP).toProg.compile

theorem wenc_rS (X C T : List Bool) (a b c : ℕ) (x : Bool) :
    (wenc 0 (rS X C T a b c x)).H = ![a, 0, b, c] ∧ (wenc 0 (rS X C T a b c x)).A = ![X, [x], C, T] := by
  constructor <;> (funext j; fin_cases j <;> simp [wenc, role, rS])

theorem wenc_iS (cap : ℕ) (X Z : List Bool) (hx hz f g : ℕ) (c : Bool) :
    (wenc cap (iS X Z hx hz f g c)).H = ![hx, 0, hz, f, g] ∧
      (wenc cap (iS X Z hx hz f g c)).A = ![X, [c], Z, regTape cap f, regTape cap g] := by
  constructor <;> (funext j; fin_cases j <;> simp [wenc, role, iS])

/-- **The residue test, as a step.** -/
theorem res_step (bs : List Bool) (cs : List ℕ) (hl : bs.length = cs.length) (T : List Bool) (x : Bool) :
    Step resRM (resLoopCost cs + 3) ![0, 0, 0, 0] ![frame bs, [x], fieldsU cs, T]
      ![2 * bs.length, 0, (fieldsU cs).length, dotB bs cs] ![frame bs, [readTapeBit T (dotB bs cs)], fieldsU cs, T] := by
  have h := Exec.step (WExec.exec 0 (resP_spec 0 (frame bs) (fieldsU cs) T bs cs hl rfl rfl x))
  rw [(wenc_rS _ _ _ _ _ _ _).1, (wenc_rS _ _ _ _ _ _ _).2, (wenc_rS _ _ _ _ _ _ _).1, (wenc_rS _ _ _ _ _ _ _).2] at h
  exact h

/-- **The odometer, as a step.** -/
theorem inc_step (cap : ℕ) (hcap : 1 ≤ cap) (K : ℕ) (τ : List ℕ) (hτ : τ ≠ []) (hd : ∀ x ∈ τ, x ≤ K) (c : Bool) :
    ∃ h', Step incRM (incCost K τ.length) ![0, 0, 0, 0, 0]
      ![frame (encT K τ), [c], zW K (τ.length * (K + 1)), regTape cap 0, regTape cap 0]
      ![h', 0, h', 0, 0]
      ![frame (encT K (incT K τ)), [!allK K τ], zW K (τ.length * (K + 1)), regTape cap 0, regTape cap 0] := by
  obtain ⟨h', hw⟩ := incP_spec cap hcap K τ hτ hd c
  have h := Exec.step (WExec.exec cap hw)
  rw [(wenc_iS _ _ _ _ _ _ _ _).1, (wenc_iS _ _ _ _ _ _ _ _).2, (wenc_iS _ _ _ _ _ _ _ _).1,
    (wenc_iS _ _ _ _ _ _ _ _).2] at h
  exact ⟨h', h⟩

/-! ## The bank -/

structure RX where
  x : List Bool
  z : List Bool
  c : List Bool
  t : List Bool
  cell : List Bool
  st : List Bool
  o : List Bool
  log : List Bool
  rf : List Bool
  rg : List Bool

def RX.tapes (b : RX) : Fin 10 → List Bool := ![b.x, b.z, b.c, b.t, b.cell, b.st, b.o, b.log, b.rf, b.rg]

/-- The heads: all at `0` but the output's. -/
def rxH (o : ℕ) : Fin 10 → ℕ := ![0, 0, 0, 0, 0, 0, o, 0, 0, 0]

def sRS : Fin 5 → Fin 10 := ![0, 4, 2, 3, 7]
def sIN : Fin 6 → Fin 10 := ![0, 4, 1, 8, 9, 7]
def sMS : Fin 4 → Fin 10 := ![0, 5, 6, 7]
def sO6 : Fin 1 → Fin 10 := ![6]

theorem sRS_inj : Function.Injective sRS := by decide
theorem sIN_inj : Function.Injective sIN := by decide
theorem sMS_inj : Function.Injective sMS := by decide
theorem sO6_inj : Function.Injective sO6 := by decide

noncomputable def resS := RecoveryFocus.machine sRS (MaskedReset.machine resRM (fun _ => true))
noncomputable def incS := RecoveryFocus.machine sIN (MaskedReset.machine incRM (fun _ => true))
noncomputable def mselS := RecoveryFocus.machine sMS (MaskedReset.machine mselM ![true, true, false])
noncomputable def putX (w : List Bool) := RecoveryFocus.machine sO6 (putW w)

/-- The term of the current tuple. -/
noncomputable def termRX := Composition.machine (Composition.machine (putX (true :: coefWord 1)) mselS) (putX [false])
noncomputable def brRX := Block.branchM (4 : Fin 10) termRX (Block.idle 10)
/-- **One pass.** -/
noncomputable def radBody := Composition.machine (Composition.machine resS brRX) incS
/-- **The tuple loop.** -/
noncomputable def radLoop := StreamController.machine radBody (4 : Fin 10)

def pRS : Fin 10 → Option (Fin 5) := ![some 0, none, some 2, some 3, some 1, none, none, some 4, none, none]
def pIN : Fin 10 → Option (Fin 6) := ![some 0, some 2, none, none, some 1, none, none, some 5, some 3, some 4]
def pMS : Fin 10 → Option (Fin 4) := ![some 0, none, none, none, none, some 1, some 2, some 3, none, none]
def pO6 : Fin 10 → Option (Fin 1) := ![none, none, none, none, none, none, some 0, none, none, none]

/-- Prove a pick table of a concrete slot map (up to six slots). -/
macro "pick_table6" inj:term : tactic => `(tactic| (intro i; fin_cases i <;> first
  | exact RecoveryFocus.pick_slot _ $inj 0
  | exact RecoveryFocus.pick_slot _ $inj 1
  | exact RecoveryFocus.pick_slot _ $inj 2
  | exact RecoveryFocus.pick_slot _ $inj 3
  | exact RecoveryFocus.pick_slot _ $inj 4
  | exact RecoveryFocus.pick_slot _ $inj 5
  | decide))

theorem pick_sRS : ∀ i, RecoveryFocus.pick sRS i = pRS i := by pick_table6 sRS_inj
theorem pick_sIN : ∀ i, RecoveryFocus.pick sIN i = pIN i := by pick_table6 sIN_inj
theorem pick_sMS : ∀ i, RecoveryFocus.pick sMS i = pMS i := by pick_table6 sMS_inj
theorem pick_sO6 : ∀ i, RecoveryFocus.pick sO6 i = pO6 i := by pick_table6 sO6_inj

/-! ## The stages -/

theorem res_stage (b : RX) (o : ℕ) (bs : List Bool) (cs : List ℕ) (hl : bs.length = cs.length) (cap : ℕ) (x : Bool)
    (hx : b.x = frame bs) (hc : b.c = fieldsU cs) (hcell : b.cell = [x]) (hlog : b.log = List.replicate cap false)
    (hcap : resLoopCost cs + 3 ≤ cap) :
    Step resS (2 * (resLoopCost cs + 3) + 2) (rxH o) b.tapes (rxH o)
      { b with cell := [readTapeBit b.t (dotB bs cs)] }.tapes := by
  have hm := maskRun (res_step bs cs hl b.t x) (fun _ => true) (by intro j _; fin_cases j <;> rfl) hcap
  have hc' : Step (MaskedReset.machine resRM (fun _ => true)) (2 * (resLoopCost cs + 3) + 2)
      (fun _ => 0) ![frame bs, [x], fieldsU cs, b.t, List.replicate cap false]
      (fun _ => 0) ![frame bs, [readTapeBit b.t (dotB bs cs)], fieldsU cs, b.t, List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc' sRS sRS_inj (rxH o) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sRS, RX.tapes, hx, hc, hcell, hlog])
  rw [install_of_pick sRS pRS pick_sRS] at h
  refine h.congr rfl ?_
  funext i; fin_cases i <;> simp [pRS, RX.tapes, hx, hc, hlog]

theorem incR_stage (b : RX) (o : ℕ) (K : ℕ) (τ : List ℕ) (hτ : τ ≠ []) (hd : ∀ x ∈ τ, x ≤ K) (capR cap : ℕ)
    (hR : 1 ≤ capR) (x : Bool) (hx : b.x = frame (encT K τ)) (hz : b.z = zW K (τ.length * (K + 1)))
    (hcell : b.cell = [x]) (hrf : b.rf = regTape capR 0) (hrg : b.rg = regTape capR 0)
    (hlog : b.log = List.replicate cap false) (hcap : incCost K τ.length ≤ cap) :
    Step incS (2 * incCost K τ.length + 2) (rxH o) b.tapes (rxH o)
      { b with x := frame (encT K (incT K τ)), cell := [!allK K τ] }.tapes := by
  obtain ⟨h', hi⟩ := inc_step capR hR K τ hτ hd x
  have hm := maskRun hi (fun _ => true) (by intro j _; fin_cases j <;> rfl) hcap
  have hc' : Step (MaskedReset.machine incRM (fun _ => true)) (2 * incCost K τ.length + 2)
      (fun _ => 0) ![frame (encT K τ), [x], zW K (τ.length * (K + 1)), regTape capR 0, regTape capR 0,
        List.replicate cap false]
      (fun _ => 0) ![frame (encT K (incT K τ)), [!allK K τ], zW K (τ.length * (K + 1)), regTape capR 0,
        regTape capR 0, List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc' sIN sIN_inj (rxH o) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sIN, RX.tapes, hx, hz, hcell, hrf, hrg, hlog])
  rw [install_of_pick sIN pIN pick_sIN] at h
  refine h.congr rfl ?_
  funext i; fin_cases i <;> simp [pIN, RX.tapes, hz, hrf, hrg, hlog]

theorem put_stage (b : RX) (o B w : List Bool) (ho : b.o = overlay o B) :
    Step (putX w) (putCost w) (rxH o.length) b.tapes (rxH (o ++ w).length) { b with o := overlay (o ++ w) B }.tapes := by
  have h := dockRun (putW_run w o B) sO6 sO6_inj (rxH o.length) b.tapes (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; simp [sO6, RX.tapes, ho])
  rw [dockH_of_pick sO6 pO6 pick_sO6, install_of_pick sO6 pO6 pick_sO6] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pO6, rxH]
  · funext i; fin_cases i <;> simp [pO6, RX.tapes]

theorem msel_stage (b : RX) (o B : List Bool) (r : List Bool) (fs : List (List (List ℕ))) (hl : r.length = fs.length)
    (tail : List Bool) (cap : ℕ) (hx : b.x = frame r) (hst : b.st = stF fs ++ tail) (ho : b.o = overlay o B)
    (hlog : b.log = List.replicate cap false) (hcap : mselCost fs ≤ cap) :
    Step mselS (2 * mselCost fs + 2) (rxH o.length) b.tapes (rxH (o ++ mselW r fs).length)
      { b with o := overlay (o ++ mselW r fs) B }.tapes := by
  have hm := maskRun (msel_run r fs hl tail o B) ![true, true, false] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine mselM ![true, true, false]) (2 * mselCost fs + 2)
      ![0, 0, o.length, 0] ![frame r, stF fs ++ tail, overlay o B, List.replicate cap false]
      ![0, 0, (o ++ mselW r fs).length, 0] ![frame r, stF fs ++ tail, overlay (o ++ mselW r fs) B,
        List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := dockRun hc' sMS sMS_inj (rxH o.length) b.tapes (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [sMS, RX.tapes, hx, hst, ho, hlog])
  rw [dockH_of_pick sMS pMS pick_sMS, install_of_pick sMS pMS pick_sMS] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pMS, rxH]
  · funext i; fin_cases i <;> simp [pMS, RX.tapes, hx, hst, hlog]

/-- The term record of a selection. -/
def radTerm (r : List Bool) (fs : List (List (List ℕ))) : List Bool := (true :: coefWord 1) ++ mselW r fs ++ [false]

/-- The cost of one term. -/
def termCostR (fs : List (List (List ℕ))) : ℕ :=
  (putCost (true :: coefWord 1) + 1 + (2 * mselCost fs + 2)) + 1 + putCost [false]

theorem term_stage (b : RX) (o B : List Bool) (r : List Bool) (fs : List (List (List ℕ))) (hl : r.length = fs.length)
    (tail : List Bool) (cap : ℕ) (hx : b.x = frame r) (hst : b.st = stF fs ++ tail) (ho : b.o = overlay o B)
    (hlog : b.log = List.replicate cap false) (hcap : mselCost fs ≤ cap) :
    Step termRX (termCostR fs) (rxH o.length) b.tapes (rxH (o ++ radTerm r fs).length)
      { b with o := overlay (o ++ radTerm r fs) B }.tapes := by
  have s1 := put_stage b o B (true :: coefWord 1) ho
  set b1 : RX := { b with o := overlay (o ++ (true :: coefWord 1)) B } with hb1
  have s2 := msel_stage b1 (o ++ (true :: coefWord 1)) B r fs hl tail cap (by simp [hb1, hx]) (by simp [hb1, hst])
    rfl (by simp [hb1, hlog]) hcap
  set b2 : RX := { b1 with o := overlay (o ++ (true :: coefWord 1) ++ mselW r fs) B } with hb2
  have s3 := put_stage b2 (o ++ (true :: coefWord 1) ++ mselW r fs) B [false] rfl
  have t := (s1.seq s2).seq s3
  have e : o ++ (true :: coefWord 1) ++ mselW r fs ++ [false] = o ++ radTerm r fs := by
    simp [radTerm, List.append_assoc]
  rw [e] at t
  exact t.congr rfl (by simp [hb2, hb1])

/-! ## The loop -/

section Loop
variable (K P : ℕ) (cs : List ℕ) (T : List Bool) (fs : List (List (List ℕ)))

/-- The accepted tuple's term, or nothing. -/
def radTermOr (τ : List ℕ) : List Bool :=
  if readTapeBit T (dotB (encT K τ) cs) then radTerm (encT K τ) fs else []

/-- What the first `j` passes write. -/
def radAt (j : ℕ) : List Bool := (List.range j).flatMap fun i => radTermOr K cs T fs (tupAt K P i)

/-- **The RADIX row's term records**, over all tuples in order. -/
def radW : List Bool := radAt K P cs T fs ((K + 1) ^ P)

theorem radAt_succ (j : ℕ) : radAt K P cs T fs (j + 1) = radAt K P cs T fs j ++ radTermOr K cs T fs (tupAt K P j) := by
  simp [radAt, List.range_succ, List.flatMap_append]

/-- The bank before pass `j`. -/
def radA (Zw st o B : List Bool) (cap capR : ℕ) (j : ℕ) : RX :=
  ⟨frame (encT K (tupAt K P j)), Zw, fieldsU cs, T, [decide (j < (K + 1) ^ P)], st,
    overlay (o ++ radAt K P cs T fs j) B, List.replicate cap false, regTape capR 0, regTape capR 0⟩

/-- The cost of one pass (the same for every tuple). -/
def radPass : ℕ :=
  ((2 * (resLoopCost cs + 3) + 2) + 1 + (termCostR fs + 2)) + 1 + (2 * incCost K P + 2)

theorem tupAt_len (j : ℕ) (hj : j < (K + 1) ^ P) : (tupAt K P j).length = P := (mem_lexT (tupAt_mem K P j hj)).1

theorem radBody_step (hP : 1 ≤ P) (hcs : cs.length = P * (K + 1)) (hfs : fs.length = P * (K + 1)) (tail o B : List Bool)
    (cap capR : ℕ) (hR : 1 ≤ capR) (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost fs ≤ cap)
    (hc3 : incCost K P ≤ cap) (j : ℕ) (hj : j < (K + 1) ^ P) :
    Step radBody (radPass K P cs fs) (rxH (o ++ radAt K P cs T fs j).length)
      (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR j).tapes
      (rxH (o ++ radAt K P cs T fs (j + 1)).length)
      (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR (j + 1)).tapes := by
  set τ := tupAt K P j with hτ
  have hlen : τ.length = P := tupAt_len K P j hj
  have hd : ∀ x ∈ τ, x ≤ K := (mem_lexT (tupAt_mem K P j hj)).2
  have hne : τ ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  have hel : (encT K τ).length = cs.length := by rw [encT_length, hlen, hcs]
  have hel' : (encT K τ).length = fs.length := by rw [encT_length, hlen, hfs]
  set b := radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR j with hb
  set o' := o ++ radAt K P cs T fs j with ho'
  have s1 := res_stage b o'.length (encT K τ) cs hel cap (decide (j < (K + 1) ^ P)) rfl rfl rfl rfl hc1
  set acc := readTapeBit T (dotB (encT K τ) cs) with hacc
  set b1 : RX := { b with cell := [acc] } with hb1
  have s2 : Step brRX ((if acc then termCostR fs else 0) + 2) (rxH o'.length) b1.tapes
      (rxH (o ++ radAt K P cs T fs (j + 1)).length) { b1 with o := overlay (o ++ radAt K P cs T fs (j + 1)) B }.tapes := by
    cases hf : acc
    · have hi := idle_step (rxH o'.length) b1.tapes
      have e : o ++ radAt K P cs T fs (j + 1) = o' := by
        rw [ho', radAt_succ, radTermOr, ← hτ, ← hacc, hf]; simp
      rw [e]
      have e2 : ({ b1 with o := overlay o' B } : RX) = b1 := by simp [hb1, hb, radA, ho']
      rw [e2]
      exact Block.branch_false (4 : Fin 10) termRX hi (by simp [hb1, RX.tapes, rxH, hf, readTapeBit])
    · have tw := term_stage b1 o' B (encT K τ) fs hel' tail cap rfl rfl rfl rfl hc2
      have e : o' ++ radTerm (encT K τ) fs = o ++ radAt K P cs T fs (j + 1) := by
        rw [ho', radAt_succ, radTermOr, ← hτ, ← hacc, hf]; simp
      rw [e] at tw
      exact Block.branch_true (4 : Fin 10) (Block.idle 10) tw (by simp [hb1, RX.tapes, rxH, hf, readTapeBit])
  set b2 : RX := { b1 with o := overlay (o ++ radAt K P cs T fs (j + 1)) B } with hb2
  have s3 := incR_stage b2 (o ++ radAt K P cs T fs (j + 1)).length K τ hne hd capR cap hR acc rfl
    (by simp [hb2, hb1, hb, radA, hlen]) rfl rfl rfl rfl (by rw [hlen]; exact hc3)
  obtain ⟨hinc, hall⟩ := incT_tupAt K P j hj
  rw [← hτ] at hinc hall
  rw [hinc, hall] at s3
  have tt := (s1.seq s2).seq s3
  refine (tt.congr rfl ?_).enlarge ?_
  · have hc : (!decide (j + 1 = (K + 1) ^ P)) = decide (j + 1 < (K + 1) ^ P) := by
      by_cases h : j + 1 < (K + 1) ^ P
      · simp [h, Nat.ne_of_lt h]
      · have : j + 1 = (K + 1) ^ P := by omega
        simp [this]
    simp [hb2, hb1, hb, radA, hc]
  · unfold radPass
    rw [hlen]
    split_ifs <;> omega

/-- The cost of the tuple loop. -/
def radCost : ℕ := (K + 1) ^ P * (radPass K P cs fs + 2) + 1

/-- **The tuple loop**: the output receives `radW`, the terms of the accepted tuples in order. -/
theorem radLoop_run (hP : 1 ≤ P) (hcs : cs.length = P * (K + 1)) (hfs : fs.length = P * (K + 1)) (tail o B : List Bool)
    (cap capR : ℕ) (hR : 1 ≤ capR) (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost fs ≤ cap)
    (hc3 : incCost K P ≤ cap) :
    Step radLoop (radCost K P cs fs) (rxH o.length)
      (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR 0).tapes
      (rxH (o ++ radW K P cs T fs).length)
      (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR ((K + 1) ^ P)).tapes := by
  have hW := Block.WhileBody.run ({
    body := radBody
    tape := (4 : Fin 10)
    bound := (K + 1) ^ P
    H := fun j => rxH (o ++ radAt K P cs T fs j).length
    A := fun j => (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR j).tapes
    cost := fun _ => radPass K P cs fs
    step := fun j hj => radBody_step K P cs T fs hP hcs hfs tail o B cap capR hR hc1 hc2 hc3 j hj
    cont := by intro j hj; simp [radA, RX.tapes, rxH, readTapeBit, hj]
    halt := by simp [radA, RX.tapes, rxH, readTapeBit] } : Block.WhileBody 10 _)
  have hW' : Step radLoop (((List.range ((K + 1) ^ P - 0)).map fun _ => radPass K P cs fs + 2).sum + 1)
      (rxH (o ++ radAt K P cs T fs 0).length)
      (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR 0).tapes
      (rxH (o ++ radAt K P cs T fs ((K + 1) ^ P)).length)
      (radA K P cs T fs (zW K (P * (K + 1))) (stF fs ++ tail) o B cap capR ((K + 1) ^ P)).tapes := hW
  have e0 : radAt K P cs T fs 0 = [] := by simp [radAt]
  rw [e0, List.append_nil] at hW'
  refine hW'.enlarge (le_of_eq ?_)
  simp [radCost, List.map_const', List.sum_replicate]

end Loop

end NearCubicWires.WireExponent3_5.ListMachine.Row
