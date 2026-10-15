import Proof.Wire_3_5.UnionMachineSchedLayout
import Proof.Wire_3_5.UnionMachineRoundBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Sched
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires.WireExponent3_5.UnionMachine.Entry

/-- The kept data of one iteration: the table's word and head, `p`, the six accumulators. -/
structure Kept where
  tbl : List Bool
  pos : ℕ
  p : ℕ
  acc : Fin 6 → ℕ

/-- The fixed tapes of an iteration, scratch blank. -/
def fixedA (cap : ℕ) (K : Kept) (k : Fin 31) : List Bool :=
  if k.val = 0 then K.tbl else if k.val = 1 then [false] else if k.val ≤ 3 then []
  else if k.val = 13 then regTape cap K.p
  else if h : 24 ≤ k.val ∧ k.val ≤ 29 then regTape cap (K.acc ⟨k.val - 24, by omega⟩)
  else regTape cap 0

/-- The fixed heads of an iteration. -/
def fixedH (K : Kept) (k : Fin 31) : ℕ :=
  if k.val = 0 then K.pos else if k.val = 13 then K.p
  else if h : 24 ≤ k.val ∧ k.val ≤ 29 then K.acc ⟨k.val - 24, by omega⟩ else 0

section Iter
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- **An iteration's bank**: the fixed tapes, the estimator's tapes blank. -/
noncomputable def iterA (cap : ℕ) (K : Kept) : Fin (NA P) → List Bool :=
  fun i => if h : i.val < 31 then fixedA cap K ⟨i.val, h⟩ else []
noncomputable def iterH (K : Kept) : Fin (NA P) → ℕ :=
  fun i => if h : i.val < 31 then fixedH K ⟨i.val, h⟩ else 0

theorem iterA_fx (cap : ℕ) (K : Kept) (k : Fin 31) : iterA P cap K (fx P k) = fixedA cap K k := by
  simp [iterA, fx_val]
theorem iterH_fx (K : Kept) (k : Fin 31) : iterH P K (fx P k) = fixedH K k := by
  simp [iterH, fx_val]
theorem iterA_es (cap : ℕ) (K : Kept) (j : Fin (TE P)) : iterA P cap K (es P j) = [] := by
  simp [iterA, es_val]
theorem iterH_es (K : Kept) (j : Fin (TE P)) : iterH P K (es P j) = 0 := by
  simp [iterH, es_val]

/-- The entry bank's registers at an iteration: the accumulators, `0` elsewhere. -/
def entryVal (K : Kept) (r : Fin 15) : ℕ := if h : 8 ≤ r.val ∧ r.val ≤ 13 then K.acc ⟨r.val - 8, by omega⟩ else 0

/-- The entry bank at an iteration. -/
def σE (K : Kept) : ES := ⟨![K.pos, 0], ![K.tbl, []], entryVal K, false⟩

theorem eb_entry (cap : ℕ) (K : Kept) (k : Fin (1 + 2 + 15)) :
    iterH P K (eb P k) = (wenc cap (σE K)).H k ∧ iterA P cap K (eb P k) = (wenc cap (σE K)).A k := by
  fin_cases k <;>
    simp [eb, ebReg, iterH, iterA, fixedH, fixedA, fx_val, es_val, wenc, role, σE, entryVal, regTape_zero]

/-! ## Where the slot maps land -/

theorem eb_val (k : Fin (1 + 2 + 15)) : (eb P k).val =
    if k.val = 0 then 0 else if k.val = 1 then 1 else if k.val = 2 then 31 + (eIn P).val
    else (ebReg ⟨k.val - 3, by omega⟩).val := by
  unfold eb; split_ifs <;> simp [fx_val, es_val]

theorem rs_val (k : Fin (2 + 2 + 14)) : (rs P k).val = if k.val = 0 then 31 + (eOut P).val else k.val := by
  unfold rs; split_ifs <;> simp [fx_val, es_val]

theorem eb_ne_es (k : Fin (1 + 2 + 15)) (j : Fin (TE P)) (hj : j ≠ eIn P) : eb P k ≠ es P j := by
  intro h
  have hv := congrArg Fin.val h
  rw [eb_val, es_val] at hv
  split_ifs at hv with h1 h2 h3
  · omega
  · omega
  · exact hj (Fin.ext (by omega)).symm
  · have := ebReg_ge ⟨k.val - 3, by omega⟩
    have := (ebReg ⟨k.val - 3, by omega⟩).isLt
    omega

theorem eb_ne_fx (k : Fin (1 + 2 + 15)) (m : Fin 31) (h0 : m.val ≠ 0) (h1 : m.val ≠ 1)
    (hr : ∀ r, ebReg r ≠ m) : eb P k ≠ fx P m := by
  intro h
  have hv := congrArg Fin.val h
  rw [eb_val, fx_val] at hv
  split_ifs at hv with a b c
  · omega
  · omega
  · have := m.isLt; omega
  · exact hr _ (Fin.ext hv)

theorem rs_ne_fx0 (k : Fin (2 + 2 + 14)) : rs P k ≠ fx P 0 := by
  intro h; have hv := congrArg Fin.val h; rw [rs_val, fx_val] at hv; split_ifs at hv <;> simp at hv <;> omega

theorem rs_ne_fx (k : Fin (2 + 2 + 14)) (m : Fin 31) (hm : 18 ≤ m.val) : rs P k ≠ fx P m := by
  intro h; have hv := congrArg Fin.val h; rw [rs_val, fx_val] at hv
  split_ifs at hv <;> omega

theorem es_ne_fx (j : Fin (TE P)) (m : Fin 31) : es P j ≠ fx P m := fun h => fx_ne_es P m j h.symm

/-! ## Step 1: reading the entry -/

/-- The entry bank's reading machine, docked. -/
noncomputable def readM : Machine (NA P) readE.toProg.size := RecoveryFocus.machine (eb P) readE.toProg.compile

theorem stage_read (cap : ℕ) (K : Kept) (e : CallEntry) (pre rest : List Bool)
    (hK : K.tbl = pre ++ entryWord e ++ rest) (hpos : K.pos = pre.length)
    (hcap : 2 * e.word.length + e.mag + 2 ≤ cap) :
    ∃ τ : ES, τ.st 0 = K.tbl ∧ τ.sh 0 = pre.length + (entryWord e).length ∧ τ.st 1 = frame e.word ∧
      τ.sh 1 = 0 ∧ τ.val 0 = e.mag ∧ τ.val 1 = e.neg.toNat ∧ τ.val 2 = (kindHi e.kind).toNat ∧
      τ.val 3 = (kindLo e.kind).toNat ∧ τ.val 4 = 0 ∧ (∀ r, r ∉ readRegs → τ.val r = entryVal K r) ∧
      τ.cell = false ∧
      Step (readM P) (40 * (e.mag + e.word.length + 2)) (iterH P K) (iterA P cap K)
        (dockH (eb P) (iterH P K) (wenc cap τ).H) (install (eb P) (iterA P cap K) (wenc cap τ).A) := by
  obtain ⟨τ, hτ, h0, hs0, h1, hs1, hCC, hSG, hK1, hK0, hCT, hfr, hcell⟩ := readE_spec cap e pre rest (σE K)
    (by simp [σE, hK]) (by simp [σE, hpos]) (by simp [σE]) (by simp [σE])
    (by intro r hr; simp [readRegs] at hr; rcases hr with h | h | h | h | h | h <;> subst h <;> simp [σE, entryVal])
    hcap
  refine ⟨τ, by rw [h0]; simp [σE], hs0, h1, hs1, hCC, hSG, hK1, hK0, hCT, fun r hr => by rw [hfr r hr]; rfl,
    by rw [hcell]; rfl, ?_⟩
  exact (WExec.exec cap hτ).step.dock (eb P) (eb_inj P) (iterH P K) (iterA P cap K)
    (fun k => (eb_entry P cap K k).1) (fun k => (eb_entry P cap K k).2)

/-! ## Step 2: the call and the rounding -/

theorem fx1_eb : fx P 1 = eb P 1 := by apply Fin.ext; rw [eb_val, fx_val]; simp
theorem fx14_eb : fx P 14 = eb P 9 := by apply Fin.ext; rw [eb_val, fx_val]; simp [ebReg]
theorem fx15_eb : fx P 15 = eb P 10 := by apply Fin.ext; rw [eb_val, fx_val]; simp [ebReg]

theorem rs_out (k : Fin (2 + 2 + 14)) (h0 : k.val ≠ 0) (h1 : k.val ≠ 1) (h14 : k.val ≠ 14) (h15 : k.val ≠ 15) :
    ∀ k', eb P k' ≠ rs P k := by
  intro k' h
  have hv := congrArg Fin.val h
  rw [eb_val, rs_val, if_neg h0] at hv
  have hk := k.isLt
  fin_cases k' <;> simp [ebReg] at hv <;> omega

/-- The round bank's entry at an iteration, after reading. -/
theorem call_entry (cap : ℕ) (K : Kept) (τ : ES) (v : ℚ) (p : ℕ) (hp : K.p = p) (h6 : τ.val 6 = 0) (h7 : τ.val 7 = 0)
    (hc : τ.cell = false) (k : Fin (2 + 2 + 14)) (hk : k ≠ 0) :
    dockH (eb P) (iterH P K) (wenc cap τ).H (rs P k) = (wenc cap (parseIn v p false)).H k ∧
      install (eb P) (iterA P cap K) (wenc cap τ).A (rs P k) = (wenc cap (parseIn v p false)).A k := by
  have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
  by_cases e1 : k.val = 1
  · rw [show k = 1 from Fin.ext e1, rs_pos P 1 (by decide), show (⟨(1 : Fin (2 + 2 + 14)).val, by omega⟩ : Fin 31) = 1
      from rfl, fx1_eb, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
    simp [wenc, role, parseIn, st3, hc]
  by_cases e14 : k.val = 14
  · rw [show k = 14 from Fin.ext e14, rs_pos P 14 (by decide), show (⟨(14 : Fin (2 + 2 + 14)).val, by omega⟩ : Fin 31) = 14
      from rfl, fx14_eb, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
    simp [wenc, role, parseIn, st3, h6]
  by_cases e15 : k.val = 15
  · rw [show k = 15 from Fin.ext e15, rs_pos P 15 (by decide), show (⟨(15 : Fin (2 + 2 + 14)).val, by omega⟩ : Fin 31) = 15
      from rfl, fx15_eb, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
    simp [wenc, role, parseIn, st3, h7]
  rw [dockH_other _ _ _ _ (rs_out P k hk' e1 e14 e15), install_other _ _ _ _ (rs_out P k hk' e1 e14 e15),
    rs_pos P k hk', iterH_fx, iterA_fx]
  fin_cases k <;> simp_all [wenc, role, parseIn, st3, fixedH, fixedA, regTape_zero]

/-! ## Step 3: accumulating, and the whole stage -/

/-- The entry bank's accumulation machine, docked. -/
noncomputable def accM : Machine (NA P) accP.toProg.size := RecoveryFocus.machine (eb P) accP.toProg.compile

/-- **The stage machine**: read, call and round, accumulate. -/
noncomputable def stageM :
    Machine (NA P) (readE.toProg.size + (((estRW P).program.stateCount + roundP.toProg.size) + accP.toProg.size)) :=
  Composition.machine (readM P) (Composition.machine (callRoundM P (es P) (rs P)) (accM P))

/-- The accumulators' change for one entry (accumulator `i` is entry-bank register `8 + i`). -/
def accStep (e : CallEntry) (mp mn : ℕ) (i : Fin 6) : ℕ := accAdd e.kind e.neg e.mag mp mn ⟨8 + i.val, by omega⟩

/-- The next iteration's kept data. -/
def nextKept (K : Kept) (e : CallEntry) (mp mn : ℕ) : Kept :=
  ⟨K.tbl, K.pos + (entryWord e).length, K.p, fun i => K.acc i + accStep e mp mn i⟩

/-- The kept tapes. -/
def keptFx (m : Fin 31) : Prop := m.val = 0 ∨ m.val = 1 ∨ m.val = 13 ∨ (24 ≤ m.val ∧ m.val ≤ 29)

/-- The stage's step bound. -/
def stageCost (mag wl b lbv p : ℕ) : ℕ :=
  40 * (mag + wl + 2) + 1 + ((2 * b + 2 + 1 + roundCost lbv p) + 1 + (mag * (20 * (8 * 2 ^ p) + 7 + 4) + 1 + 3))

theorem ebReg_ge18 (r : Fin 15) (h6 : r.val ≠ 6) (h7 : r.val ≠ 7) : 18 ≤ (ebReg r).val := by
  fin_cases r <;> simp_all [ebReg]

theorem rs_ne_eb (k' : Fin (2 + 2 + 14)) (k : Fin (1 + 2 + 15)) (h1 : k.val ≠ 1) (h2 : k.val ≠ 2)
    (h9 : k.val ≠ 9) (h10 : k.val ≠ 10) : rs P k' ≠ eb P k := by
  have hk := k.isLt
  by_cases k0 : k.val = 0
  · rw [show k = 0 from Fin.ext k0, show eb P 0 = fx P 0 by simp [eb]]; exact rs_ne_fx0 P k'
  · have e : eb P k = fx P (ebReg ⟨k.val - 3, by omega⟩) := by simp [eb, k0, h1, h2]
    rw [e]; exact rs_ne_fx P k' _ (ebReg_ge18 _ (by simp; omega) (by simp; omega))

theorem es_ne_eb (j : Fin (TE P)) (k : Fin (1 + 2 + 15)) (h2 : k.val ≠ 2) : es P j ≠ eb P k := by
  obtain ⟨m, hm⟩ := eb_val_fixed P k h2
  rw [hm]; exact es_ne_fx P j m

/-- The call's hypotheses after reading. -/
theorem stage_call (cap : ℕ) (K : Kept) (e : CallEntry) (req : {req : PrimRequest // I.Call req})
    (hw : e.word = req.1.word) (τ1 : ES) (ts1 : τ1.sh 1 = 0) (t1 : τ1.st 1 = frame e.word) (t6 : τ1.val 6 = 0)
    (t7 : τ1.val 7 = 0) (tcell : τ1.cell = false)
    (hcapD : 4 * lb (P.value req.1) + 8 * 2 ^ K.p + 20 ≤ cap) :
    ∃ (H2 : Fin (NA P) → ℕ) (A2 : Fin (NA P) → List Bool),
      Step (callRoundM P (es P) (rs P)) (2 * B.callBudget req.1.n + 2 + 1 + roundCost (lb (P.value req.1)) K.p)
        (dockH (eb P) (iterH P K) (wenc cap τ1).H) (install (eb P) (iterA P cap K) (wenc cap τ1).A) H2 A2 ∧
      (∃ τ : RS, ((τ.val 10 : ℤ) - τ.val 11 = ⌊P.value req.1 * 2 ^ K.p⌋) ∧ τ.val 9 = K.p ∧ τ.cell = false ∧
        τ.val 10 = mpOf (P.value req.1) K.p ∧ τ.val 11 = mnOf (P.value req.1) K.p ∧
        ∀ k, H2 (rs P k) = (wenc cap τ).H k ∧ A2 (rs P k) = (wenc cap τ).A k) ∧
      (∀ i, (∀ j, es P j ≠ i) → (∀ k, rs P k ≠ i) →
        H2 i = dockH (eb P) (iterH P K) (wenc cap τ1).H i ∧ A2 i = install (eb P) (iterA P cap K) (wenc cap τ1).A i) :=
  callRound_bound P (es P) (rs P) (es_inj P) (rs_inj P) (rs_zero P) (rs_es_disj P) req K.p cap false _ _
    (fun j => by
      by_cases hj : j = eIn P
      · subst hj; rw [← eb_two, dockH_slot _ (eb_inj P)]; simp [wenc, role, ts1]
      · rw [dockH_other _ _ _ _ (fun k => eb_ne_es P k j hj)]; exact iterH_es P K j)
    (by rw [← eb_two, install_slot _ (eb_inj P)]; simp [wenc, role, t1, hw])
    (fun j hj => by rw [install_other _ _ _ _ (fun k => eb_ne_es P k j hj)]; exact iterA_es P cap K j)
    (fun k hk => (call_entry P cap K τ1 _ K.p rfl t6 t7 tcell k hk).1)
    (fun k hk => (call_entry P cap K τ1 _ K.p rfl t6 t7 tcell k hk).2) hcapD

/-- The entry bank before accumulating. -/
def accIn (τ1 : ES) (h : ℕ) (a : List Bool) (mp mn : ℕ) : ES :=
  ⟨![τ1.sh 0, h], ![τ1.st 0, a], fun r => if r = 6 then mp else if r = 7 then mn else τ1.val r, false⟩

theorem accIn_agree (cap : ℕ) (τ1 : ES) (h : ℕ) (a : List Bool) (mp mn : ℕ) (tcell : τ1.cell = false)
    (k : Fin (1 + 2 + 15)) (k2 : k.val ≠ 2) (k9 : k.val ≠ 9) (k10 : k.val ≠ 10) :
    (wenc cap τ1).H k = (wenc cap (accIn τ1 h a mp mn)).H k ∧
      (wenc cap τ1).A k = (wenc cap (accIn τ1 h a mp mn)).A k := by
  fin_cases k <;> first | exact absurd rfl k2 | exact absurd rfl k9 | exact absurd rfl k10 |
    simp [wenc, role, accIn, tcell]

theorem acc_entry (cap : ℕ) (K : Kept) (τ1 : ES) (H2 : Fin (NA P) → ℕ) (A2 : Fin (NA P) → List Bool)
    (τR' : RS) (hcellR : τR'.cell = false)
    (hRk : ∀ k, H2 (rs P k) = (wenc cap τR').H k ∧ A2 (rs P k) = (wenc cap τR').A k)
    (hout2 : ∀ i, (∀ j, es P j ≠ i) → (∀ k, rs P k ≠ i) →
        H2 i = dockH (eb P) (iterH P K) (wenc cap τ1).H i ∧ A2 i = install (eb P) (iterA P cap K) (wenc cap τ1).A i)
    (tcell : τ1.cell = false) (k : Fin (1 + 2 + 15)) :
    H2 (eb P k) = (wenc cap (accIn τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR'.val 10) (τR'.val 11))).H k ∧
      A2 (eb P k) = (wenc cap (accIn τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR'.val 10) (τR'.val 11))).A k := by
  by_cases k1 : k.val = 1
  · rw [show k = 1 from Fin.ext k1, ← fx1_eb, show fx P 1 = rs P 1 by rw [rs_pos P 1 (by decide)]; rfl]
    obtain ⟨a, b⟩ := hRk 1
    rw [a, b]; simp [wenc, role, accIn, hcellR]
  by_cases k2 : k.val = 2
  · rw [show k = 2 from Fin.ext k2, eb_two]; simp [wenc, role, accIn]
  by_cases k9 : k.val = 9
  · rw [show k = 9 from Fin.ext k9, ← fx14_eb, show fx P 14 = rs P 14 by rw [rs_pos P 14 (by decide)]; rfl]
    obtain ⟨a, b⟩ := hRk 14
    rw [a, b]; simp [wenc, role, accIn]
  by_cases k10 : k.val = 10
  · rw [show k = 10 from Fin.ext k10, ← fx15_eb, show fx P 15 = rs P 15 by rw [rs_pos P 15 (by decide)]; rfl]
    obtain ⟨a, b⟩ := hRk 15
    rw [a, b]; simp [wenc, role, accIn]
  obtain ⟨a, b⟩ := hout2 (eb P k) (fun j => es_ne_eb P j k k2) (fun k' => rs_ne_eb P k' k k1 k2 k9 k10)
  rw [a, b, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
  exact accIn_agree cap τ1 _ _ _ _ tcell k k2 k9 k10

theorem accIn_val (τ1 : ES) (h : ℕ) (a : List Bool) (mp mn : ℕ) (r : Fin 15) :
    (accIn τ1 h a mp mn).val r = if r = 6 then mp else if r = 7 then mn else τ1.val r := rfl

theorem accIn_acc (K : Kept) (τ1 : ES) (h : ℕ) (a : List Bool) (mp mn : ℕ)
    (tv : ∀ r : Fin 15, r ∉ readRegs → τ1.val r = entryVal K r) (i : Fin 6) :
    (accIn τ1 h a mp mn).val ⟨8 + i.val, by omega⟩ = K.acc i := by
  have hi := i.isLt
  rw [accIn_val, if_neg (by intro h; have := congrArg Fin.val h; simp at this; omega),
    if_neg (by intro h; have := congrArg Fin.val h; simp at this; omega)]
  rw [tv _ (by
    simp only [readRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> simp at this <;> omega)]
  simp only [entryVal]
  rw [dif_pos (by simp; omega)]
  congr 1; apply Fin.ext; simp

theorem fx0_eb : fx P 0 = eb P 0 := by apply Fin.ext; rw [eb_val, fx_val]; simp

theorem fxacc_eb (i : Fin 6) : fx P ⟨24 + i.val, by omega⟩ = eb P ⟨11 + i.val, by omega⟩ := by
  apply Fin.ext; rw [eb_val, fx_val]
  have hi := i.isLt
  simp only [show 11 + i.val ≠ 0 by omega, show 11 + i.val ≠ 1 by omega, show 11 + i.val ≠ 2 by omega, if_false]
  fin_cases i <;> simp [ebReg]

/-- The kept tapes after the stage. -/
theorem stage_kept (cap : ℕ) (K : Kept) (e : CallEntry) (mp mn : ℕ) (H2 : Fin (NA P) → ℕ)
    (A2 : Fin (NA P) → List Bool) (τR : RS) (τ3 : ES)
    (hRk : ∀ k, H2 (rs P k) = (wenc cap τR).H k ∧ A2 (rs P k) = (wenc cap τR).A k) (hpc : τR.val 9 = K.p)
    (hsh0 : τ3.sh 0 = K.pos + (entryWord e).length) (hst0 : τ3.st 0 = K.tbl) (hcell : τ3.cell = false)
    (hacc : ∀ i : Fin 6, τ3.val ⟨8 + i.val, by omega⟩ = K.acc i + accStep e mp mn i)
    (m : Fin 31) (hm : keptFx m) :
    dockH (eb P) H2 (wenc cap τ3).H (fx P m) = iterH P (nextKept K e mp mn) (fx P m) ∧
      install (eb P) A2 (wenc cap τ3).A (fx P m) = iterA P cap (nextKept K e mp mn) (fx P m) := by
  rw [iterH_fx, iterA_fx]
  rcases hm with h | h | h | ⟨h1, h2⟩
  · rw [show m = 0 from Fin.ext h, fx0_eb, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
    simp [wenc, role, hsh0, hst0, fixedH, fixedA, nextKept]
  · rw [show m = 1 from Fin.ext h, fx1_eb, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
    simp [wenc, role, hcell, fixedH, fixedA]
  · have hne : ∀ k, eb P k ≠ fx P m :=
      fun k => eb_ne_fx P k m (by omega) (by omega) (fun r hr => by
        have := congrArg Fin.val hr; rw [h] at this; fin_cases r <;> simp [ebReg] at this)
    rw [dockH_other _ _ _ _ hne, install_other _ _ _ _ hne, show m = 13 from Fin.ext h,
      show fx P 13 = rs P 13 by rw [rs_pos P 13 (by decide)]; rfl]
    obtain ⟨a, b⟩ := hRk 13
    rw [a, b]
    simp [wenc, role, hpc, fixedH, fixedA, nextKept]
  · obtain ⟨i, hi⟩ : ∃ i : Fin 6, m = ⟨24 + i.val, by omega⟩ := ⟨⟨m.val - 24, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [hi, fxacc_eb, dockH_slot _ (eb_inj P), install_slot _ (eb_inj P)]
    have hri : (⟨11 + i.val, by omega⟩ : Fin (1 + 2 + 15)) = rTape (ns := 1) ⟨8 + i.val, by omega⟩ :=
      Fin.ext (by simp [rTape]; omega)
    have e1 : (wenc cap τ3).H ⟨11 + i.val, by omega⟩ = τ3.val ⟨8 + i.val, by omega⟩ := by rw [hri, wenc_H_r]
    have e2 : (wenc cap τ3).A ⟨11 + i.val, by omega⟩ = regTape cap (τ3.val ⟨8 + i.val, by omega⟩) := by
      rw [hri, wenc_A_r]
    rw [e1, e2, hacc]
    have hi' := i.isLt
    simp only [fixedH, fixedA, nextKept]
    rw [if_neg (by omega), if_neg (by omega),
      dif_pos (by omega)]
    rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega),
      dif_pos (by omega)]
    have : (⟨(⟨24 + i.val, by omega⟩ : Fin 31).val - 24, by omega⟩ : Fin 6) = i :=
      Fin.ext (by simp)
    rw [this]
    exact ⟨rfl, rfl⟩

/-- **One stage**: from an iteration's bank (entry `e` at the table's head, `req` its admissible request), a
bank whose kept tapes are the next iteration's, the accumulators advanced by the entry's term. -/
theorem stage_step (cap : ℕ) (K : Kept) (e : CallEntry) (pre rest : List Bool)
    (hK : K.tbl = pre ++ entryWord e ++ rest) (hpos : K.pos = pre.length)
    (req : {req : PrimRequest // I.Call req}) (hw : e.word = req.1.word)
    (hcapR : 2 * e.word.length + e.mag + 2 ≤ cap)
    (hcapD : 4 * lb (P.value req.1) + 8 * 2 ^ K.p + 20 ≤ cap)
    (hcapA : ∀ i : Fin 6, K.acc i + e.mag * (8 * 2 ^ K.p) ≤ cap) :
    ∃ H' A', Step (stageM P) (stageCost e.mag e.word.length (B.callBudget req.1.n) (lb (P.value req.1)) K.p)
        (iterH P K) (iterA P cap K) H' A' ∧
      ∀ m : Fin 31, keptFx m →
        H' (fx P m) = iterH P (nextKept K e (mpOf (P.value req.1) K.p) (mnOf (P.value req.1) K.p)) (fx P m) ∧
        A' (fx P m) = iterA P cap (nextKept K e (mpOf (P.value req.1) K.p) (mnOf (P.value req.1) K.p)) (fx P m) := by
  have hvs := value_small I P req.1 req.2
  have hmpb := mpOf_le (P.value req.1) K.p hvs
  have hmnb := mnOf_le (P.value req.1) K.p hvs
  obtain ⟨τ1, t0, ts0, t1, ts1, tCC, tSG, tK1, tK0, tCT, tfr, tcell, st1⟩ :=
    stage_read P cap K e pre rest hK hpos hcapR
  have t6 : τ1.val 6 = 0 := by rw [tfr 6 (by simp [readRegs])]; simp [entryVal]
  have t7 : τ1.val 7 = 0 := by rw [tfr 7 (by simp [readRegs])]; simp [entryVal]
  have t14 : τ1.val 14 = 0 := by rw [tfr 14 (by simp [readRegs])]; simp [entryVal]
  obtain ⟨H2, A2, st2, ⟨τR, _, hpc, hcellR, hmp, hmn, hRk⟩, hout2⟩ :=
    stage_call P cap K e req hw τ1 ts1 t1 t6 t7 tcell hcapD
  have hE := acc_entry P cap K τ1 H2 A2 τR hcellR hRk hout2 tcell
  have v0 : (accIn τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR.val 10) (τR.val 11)).val 0 = e.mag := by
    rw [accIn_val]; simp [tCC]
  have v6 : (accIn τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR.val 10) (τR.val 11)).val 6 =
      mpOf (P.value req.1) K.p := by rw [accIn_val]; simp [hmp]
  have v7 : (accIn τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR.val 10) (τR.val 11)).val 7 =
      mnOf (P.value req.1) K.p := by rw [accIn_val]; simp [hmn]
  have vacc := accIn_acc K τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR.val 10) (τR.val 11) tfr
  obtain ⟨τ3, ha, hvals, hCC3, hst3, hsh3, hcell3⟩ :=
    acc_spec cap e.kind e.neg (accIn τ1 (H2 (es P (eIn P))) (A2 (es P (eIn P))) (τR.val 10) (τR.val 11))
      (by rw [accIn_val]; simp [tK1]) (by rw [accIn_val]; simp [tK0]) (by rw [accIn_val]; simp [tSG])
      (by rw [accIn_val]; simp [t14])
      (fun i => by rw [vacc, v0, v6, v7]; have := hcapA i; nlinarith) (by rw [v0]; omega)
      (by rw [v6]; omega) (by rw [v7]; omega)
  have st3 := (WExec.exec cap ha).step.dock (eb P) (eb_inj P) H2 A2 (fun k => (hE k).1) (fun k => (hE k).2)
  refine ⟨_, _, ((st1.seq (st2.seq st3))).enlarge ?_, fun m hm => ?_⟩
  · unfold stageCost
    rw [v0, v6, v7]
    have : e.mag * (20 * (mpOf (P.value req.1) K.p + mnOf (P.value req.1) K.p) + 7 + 4) ≤
        e.mag * (20 * (8 * 2 ^ K.p) + 7 + 4) := Nat.mul_le_mul_left _ (by omega)
    omega
  · exact stage_kept P cap K e _ _ H2 A2 τR τ3 hRk hpc
      (by rw [hsh3]; simp [accIn, ts0, hpos]) (by rw [hst3]; simp [accIn, t0]) (by rw [hcell3]; rfl)
      (fun i => by
        rw [hvals _ (by intro h; have := congrArg Fin.val h; simp at this), vacc, v0, v6, v7]; rfl) m hm

end Iter

end NearCubicWires.WireExponent3_5.UnionMachine.Sched
