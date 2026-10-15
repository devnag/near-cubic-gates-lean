import Proof.Packets.PacketsMetaArith

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

/-! ## Two-argument maps -/

/-- The input bank of a two-argument map: `replicate x true` on tape 0, `replicate y true` on tape 1. -/
def unIn2 (n x y : ℕ) : Fin n → List Bool :=
  fun i => if i.val = 0 then List.replicate x true else if i.val = 1 then List.replicate y true else []

/-- **A two-argument unary map**: one fixed machine, `(x, y) ↦ f x y`, the value on tape 2 (head 0);
private tapes existential. -/
structure UnaryMap2 (f : ℕ → ℕ → ℕ) where
  extra : ℕ
  states : ℕ
  machine : Machine (3 + extra) states
  cost : ℕ → ℕ → ℕ
  run : ∀ x y, ∃ (H' : Fin (3 + extra) → ℕ) (A' : Fin (3 + extra) → List Bool),
    Step machine (cost x y) (fun _ => 0) (unIn2 (3 + extra) x y) H' A' ∧
    A' ⟨2, by omega⟩ = List.replicate (f x y) true ∧ H' ⟨2, by omega⟩ = 0

/-! ## Slots of `pair`: 0 input, 1 output, 2 first value, 3 second value, then the private blocks -/

/-- The first stage: input on 0, value to 2, private tapes from 4. -/
def pA (e1 e2 em : ℕ) : Fin (2 + e1) → Fin (2 + (e1 + e2 + em + 2)) :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else if k.val = 1 then ⟨2, by omega⟩ else ⟨k.val + 2, by omega⟩

/-- The second stage: input on 0, value to 3, private tapes after the first stage's. -/
def pB (e1 e2 em : ℕ) : Fin (2 + e2) → Fin (2 + (e1 + e2 + em + 2)) :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else if k.val = 1 then ⟨3, by omega⟩
    else ⟨k.val + 2 + e1, by omega⟩

/-- The map: arguments from 2 and 3, value to 1, private tapes last. -/
def pM (e1 e2 em : ℕ) : Fin (3 + em) → Fin (2 + (e1 + e2 + em + 2)) :=
  fun k => if k.val = 0 then ⟨2, by omega⟩ else if k.val = 1 then ⟨3, by omega⟩
    else if k.val = 2 then ⟨1, by omega⟩ else ⟨k.val + 1 + e1 + e2, by omega⟩

theorem pA_val (e1 e2 em : ℕ) (k : Fin (2 + e1)) :
    (pA e1 e2 em k).val = if k.val = 0 then 0 else if k.val = 1 then 2 else k.val + 2 := by
  unfold pA; split_ifs <;> rfl

theorem pB_val (e1 e2 em : ℕ) (k : Fin (2 + e2)) :
    (pB e1 e2 em k).val = if k.val = 0 then 0 else if k.val = 1 then 3 else k.val + 2 + e1 := by
  unfold pB; split_ifs <;> rfl

theorem pM_val (e1 e2 em : ℕ) (k : Fin (3 + em)) :
    (pM e1 e2 em k).val =
      if k.val = 0 then 2 else if k.val = 1 then 3 else if k.val = 2 then 1 else k.val + 1 + e1 + e2 := by
  unfold pM; split_ifs <;> rfl

theorem pA_injective (e1 e2 em : ℕ) : Function.Injective (pA e1 e2 em) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [pA_val, pA_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem pB_injective (e1 e2 em : ℕ) : Function.Injective (pB e1 e2 em) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [pB_val, pB_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem pM_injective (e1 e2 em : ℕ) : Function.Injective (pM e1 e2 em) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [pM_val, pM_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The second stage meets the first only at the input tape. -/
theorem pB_off_pA (e1 e2 em : ℕ) (k : Fin (2 + e2)) (hk : k.val ≠ 0) (j : Fin (2 + e1)) :
    pA e1 e2 em j ≠ pB e1 e2 em k := by
  intro h
  have hv := congrArg Fin.val h
  rw [pA_val, pB_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

/-- The map's slot `k` is the first stage's value tape exactly when `k = 0`. -/
theorem pM_off_pA (e1 e2 em : ℕ) (k : Fin (3 + em)) (hk : k.val ≠ 0) (j : Fin (2 + e1)) :
    pA e1 e2 em j ≠ pM e1 e2 em k := by
  intro h
  have hv := congrArg Fin.val h
  rw [pA_val, pM_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

/-- The map's slot `k` is the second stage's value tape exactly when `k = 1`. -/
theorem pM_off_pB (e1 e2 em : ℕ) (k : Fin (3 + em)) (hk : k.val ≠ 1) (j : Fin (2 + e2)) :
    pB e1 e2 em j ≠ pM e1 e2 em k := by
  intro h
  have hv := congrArg Fin.val h
  rw [pB_val, pM_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

theorem pM_zero (e1 e2 em : ℕ) : pM e1 e2 em ⟨0, by omega⟩ = pA e1 e2 em ⟨1, by omega⟩ := by
  apply Fin.ext; rw [pM_val, pA_val]; simp

theorem pM_one (e1 e2 em : ℕ) : pM e1 e2 em ⟨1, by omega⟩ = pB e1 e2 em ⟨1, by omega⟩ := by
  apply Fin.ext; rw [pM_val, pB_val]; simp

theorem pB_zero (e1 e2 em : ℕ) : pB e1 e2 em ⟨0, by omega⟩ = pA e1 e2 em ⟨0, by omega⟩ := by
  apply Fin.ext; rw [pB_val, pA_val]; simp

theorem pM_ne_zero (e1 e2 em : ℕ) (k : Fin (3 + em)) : (pM e1 e2 em k).val ≠ 0 := by
  rw [pM_val]; split_ifs <;> omega

theorem pB_val_ne_zero (e1 e2 em : ℕ) (k : Fin (2 + e2)) (hk : k.val ≠ 0) : (pB e1 e2 em k).val ≠ 0 := by
  rw [pB_val, if_neg hk]; split_ifs <;> omega

theorem pA_val_ne_zero (e1 e2 em : ℕ) (k : Fin (2 + e1)) (hk : k.val ≠ 0) : (pA e1 e2 em k).val ≠ 0 := by
  rw [pA_val, if_neg hk]; split_ifs <;> omega

/-! ## `pair` -/

/-- The composite machine. -/
def pairMachine {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {f : ℕ → ℕ → ℕ}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : UnaryMap2 f) :=
  Composition.machine
    (Composition.machine (RecoveryFocus.machine (pA s1.extra s2.extra m.extra) s1.machine)
      (RecoveryFocus.machine (pB s1.extra s2.extra m.extra) s2.machine))
    (RecoveryFocus.machine (pM s1.extra s2.extra m.extra) m.machine)

theorem pair_run {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {f : ℕ → ℕ → ℕ}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : UnaryMap2 f) (r : Request) :
    ∃ (H' : Fin (2 + (s1.extra + s2.extra + m.extra + 2)) → ℕ)
      (A' : Fin (2 + (s1.extra + s2.extra + m.extra + 2)) → List Bool),
      Step (pairMachine s1 s2 m) (s1.cost r + 1 + s2.cost r + 1 + m.cost (v1 r) (v2 r)) (fun _ => 0)
        (inBank (2 + (s1.extra + s2.extra + m.extra + 2)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate (f (v1 r) (v2 r)) true ∧ H' ⟨1, by omega⟩ = 0 := by
  set e1 := s1.extra
  set e2 := s2.extra
  set em := m.extra
  set T := 2 + (e1 + e2 + em + 2)
  set I := inBank T (Request.input a r) with hI
  obtain ⟨H1, A1, hs1, a10, h10, a11, h11⟩ := s1.run r
  have d1 := hs1.dock (pA e1 e2 em) (pA_injective _ _ _) (fun _ => 0) I (fun _ => rfl)
    (by
      intro k
      rw [hI, inBank_val, inBank_val]
      by_cases hk : k.val = 0
      · rw [if_pos (by rw [pA_val, if_pos hk]), if_pos hk]
      · rw [if_neg (pA_val_ne_zero _ _ _ k hk), if_neg hk])
  set H1' := dockH (pA e1 e2 em) (fun _ => 0) H1 with hH1'
  set A1' := install (pA e1 e2 em) I A1 with hA1'
  obtain ⟨H2, A2, hs2, a20, h20, a21, h21⟩ := s2.run r
  have d2 := hs2.dock (pB e1 e2 em) (pB_injective _ _ _) H1' A1'
    (by
      intro k
      by_cases hk : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hk', pB_zero, hH1', dockH_slot _ (pA_injective _ _ _)]
        exact h10
      · rw [hH1', dockH_other _ _ _ _ (fun j => pB_off_pA _ _ _ k hk j)])
    (by
      intro k
      by_cases hk : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hk', pB_zero, hA1', install_slot _ (pA_injective _ _ _), a10]
        rfl
      · rw [hA1', install_other _ _ _ _ (fun j => pB_off_pA _ _ _ k hk j), hI, inBank_val, inBank_val,
          if_neg (pB_val_ne_zero _ _ _ k hk), if_neg hk])
  set H2' := dockH (pB e1 e2 em) H1' H2 with hH2'
  set A2' := install (pB e1 e2 em) A1' A2 with hA2'
  obtain ⟨H3, A3, hm, a32, h32⟩ := m.run (v1 r) (v2 r)
  have d3 := hm.dock (pM e1 e2 em) (pM_injective _ _ _) H2' A2'
    (by
      intro k
      by_cases hk0 : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hk', hH2', dockH_other _ _ _ _ (fun j => pM_off_pB _ _ _ _ (by simp) j), pM_zero, hH1',
          dockH_slot _ (pA_injective _ _ _)]
        exact h11
      · by_cases hk1 : k.val = 1
        · have hk' : k = ⟨1, by omega⟩ := Fin.ext hk1
          rw [hk', pM_one, hH2', dockH_slot _ (pB_injective _ _ _)]
          exact h21
        · rw [hH2', dockH_other _ _ _ _ (fun j => pM_off_pB _ _ _ k hk1 j), hH1',
            dockH_other _ _ _ _ (fun j => pM_off_pA _ _ _ k hk0 j)])
    (by
      intro k
      by_cases hk0 : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hk', hA2', install_other _ _ _ _ (fun j => pM_off_pB _ _ _ _ (by simp) j), pM_zero, hA1',
          install_slot _ (pA_injective _ _ _), a11]
        simp [unIn2]
      · by_cases hk1 : k.val = 1
        · have hk' : k = ⟨1, by omega⟩ := Fin.ext hk1
          rw [hk', pM_one, hA2', install_slot _ (pB_injective _ _ _), a21]
          simp [unIn2]
        · rw [hA2', install_other _ _ _ _ (fun j => pM_off_pB _ _ _ k hk1 j), hA1',
            install_other _ _ _ _ (fun j => pM_off_pA _ _ _ k hk0 j), hI, inBank_val,
            if_neg (pM_ne_zero _ _ _ k)]
          simp [unIn2, hk0, hk1])
  have hall := (d1.seq d2).seq d3
  have e0 : (⟨0, by omega⟩ : Fin T) = pB e1 e2 em ⟨0, by omega⟩ := by
    apply Fin.ext; rw [pB_val]; simp
  have e1' : (⟨1, by omega⟩ : Fin T) = pM e1 e2 em ⟨2, by omega⟩ := by
    apply Fin.ext; rw [pM_val]; simp
  have n0 : ∀ k, pM e1 e2 em k ≠ ⟨0, by omega⟩ := by
    intro k h
    have hv : (pM e1 e2 em k).val = 0 := by rw [h]
    exact pM_ne_zero _ _ _ k hv
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_⟩
  · rw [install_other _ _ _ _ n0, e0, hA2', install_slot _ (pB_injective _ _ _)]
    exact a20
  · rw [dockH_other _ _ _ _ n0, e0, hH2', dockH_slot _ (pB_injective _ _ _)]
    exact h20
  · rw [e1', install_slot _ (pM_injective _ _ _)]
    exact a32
  · rw [e1', dockH_slot _ (pM_injective _ _ _)]
    exact h32

theorem one_le_small (a : DecompositionAlgorithm) (r : Request) : 1 ≤ r.smallSize a := by
  unfold Request.smallSize; exact Nat.le_add_left 1 _

/-- **Two stages, then a two-argument map on their values.** -/
def UnaryStage.pair {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {f : ℕ → ℕ → ℕ}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : UnaryMap2 f) (c d : ℕ)
    (hc : ∀ r, m.cost (v1 r) (v2 r) ≤ c * (r.smallSize a) ^ d) :
    UnaryStage a (fun r => f (v1 r) (v2 r)) where
  extra := s1.extra + s2.extra + m.extra + 2
  states := _
  machine := pairMachine s1 s2 m
  cost := fun r => s1.cost r + 1 + s2.cost r + 1 + m.cost (v1 r) (v2 r)
  coefficient := s1.coefficient + s2.coefficient + 2 + c
  degree := s1.degree + s2.degree + d
  cost_le := by
    intro r
    set D := s1.degree + s2.degree + d
    have h1 := s1.cost_le r
    have h2 := s2.cost_le r
    have h3 := hc r
    have p1 : (r.smallSize a) ^ s1.degree ≤ (r.smallSize a) ^ D :=
      Nat.pow_le_pow_right (one_le_small a r) (by omega)
    have p2 : (r.smallSize a) ^ s2.degree ≤ (r.smallSize a) ^ D :=
      Nat.pow_le_pow_right (one_le_small a r) (by omega)
    have p3 : (r.smallSize a) ^ d ≤ (r.smallSize a) ^ D :=
      Nat.pow_le_pow_right (one_le_small a r) (by omega)
    have p0 : 1 ≤ (r.smallSize a) ^ D := Nat.one_le_pow _ _ (one_le_small a r)
    have q1 := Nat.mul_le_mul_left s1.coefficient p1
    have q2 := Nat.mul_le_mul_left s2.coefficient p2
    have q3 := Nat.mul_le_mul_left c p3
    calc s1.cost r + 1 + s2.cost r + 1 + m.cost (v1 r) (v2 r)
        ≤ s1.coefficient * (r.smallSize a) ^ D + (r.smallSize a) ^ D + s2.coefficient * (r.smallSize a) ^ D +
            (r.smallSize a) ^ D + c * (r.smallSize a) ^ D := by omega
      _ = (s1.coefficient + s2.coefficient + 2 + c) * (r.smallSize a) ^ D := by ring
  run := pair_run s1 s2 m

/-! ## `+` -/

def addMap2 : UnaryMap2 (fun x y => x + y) where
  extra := 1
  states := _
  machine := ClockUnarySum.machine
  cost := fun x y => 2 * (x + y) + 6
  run := by
    intro x y
    refine ⟨_, _, (UnaryCalc.sum_step x y).congr_in rfl ?_, rfl, rfl⟩
    funext i; fin_cases i <;> rfl

/-! ## `max` -/

theorem read_rep (x i : ℕ) : readTapeBit (List.replicate x true) i = decide (i < x) := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < x
  · simp [h]
  · simp [h]

namespace MaxM

/-- Tapes 0, 1 the arguments, 2 the output: write a one while either argument still reads one. -/
def machine : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q b =>
    if q.val = 0 then
      (if b 0 || b 1 then some ⟨0, ![none, none, some true], ![.right, .right, .right]⟩
       else some ⟨1, fun _ => none, fun _ => .stay⟩)
    else none

def cfg (q : Fin 2) (x y i : ℕ) : Configuration 3 2 :=
  ⟨q, ![i, i, i], ![List.replicate x true, List.replicate y true, List.replicate i true]⟩

theorem scan_step (x y i : ℕ) (hi : i < max x y) :
    step machine (cfg 0 x y i) = some (cfg 0 x y (i + 1)) := by
  have h0 := read_rep x i
  have h1 := read_rep y i
  have hb : (decide (i < x) || decide (i < y)) = true := by
    rcases Nat.lt_or_ge i x with h | h
    · simp [h]
    · have : i < y := by omega
      simp [this]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0, h1, hb]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate]

theorem end_step (x y : ℕ) :
    step machine (cfg 0 x y (max x y)) = some (cfg 1 x y (max x y)) := by
  have h0 := read_rep x (max x y)
  have h1 := read_rep y (max x y)
  have hx : ¬ max x y < x := by omega
  have hy : ¬ max x y < y := by omega
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0, h1, hx, hy]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem scan_timed (x y : ℕ) : ∀ i, i ≤ max x y →
    Timed machine (max x y - i) (cfg 0 x y i) (cfg 0 x y (max x y)) := by
  intro i hi
  induction h : max x y - i generalizing i with
  | zero =>
    have : i = max x y := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (scan_step x y i (by omega))
    have t2 := ih (i + 1) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

theorem run (x y : ℕ) : Step machine (max x y + 1) ![0, 0, 0]
    ![List.replicate x true, List.replicate y true, []] ![max x y, max x y, max x y]
    ![List.replicate x true, List.replicate y true, List.replicate (max x y) true] := by
  have t1 := scan_timed x y 0 (by omega)
  have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (end_step x y)
  have t := t1.trans t2
  obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
  refine ⟨r, ?_, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩
  have hc : (⟨machine.start, ![0, 0, 0], ![List.replicate x true, List.replicate y true, []]⟩ :
      Configuration 3 2) = cfg 0 x y 0 := rfl
  rw [hc]
  simpa using hr

end MaxM

/-- **`max x y` in unary.** -/
def maxMap2 : UnaryMap2 (fun x y => max x y) where
  extra := 1
  states := 2 + 2
  machine := MaskedReset.machine MaxM.machine (fun _ => true)
  cost := fun x y => 2 * (max x y + 1) + 2
  run := by
    intro x y
    obtain ⟨k, hm⟩ := step_mask0 (MaxM.run x y) (fun _ => true) (by intro i _; fin_cases i <;> rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp only [Fin.addCases_right]
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn2]
    · rfl
    · rfl

/-! ## `(x+1)^2` -/

theorem sq_out_ne_zero : (UnaryCalc.outputTape 2).val ≠ 0 := by
  intro h
  exact UnaryCalc.output_ne_input 2 (Fin.ext (by rw [h]; rfl))

def sqMap : UnaryMap (fun x => 1 * (x + 1) ^ 2) :=
  UnaryMap.ofSwap (e := 16) (PCPSerializerCapacity.Power.machine 2 1) (UnaryCalc.outputTape 2)
    sq_out_ne_zero (PCPSerializerCapacity.Power.budget 2 1) (fun x => by
      obtain ⟨out, h, _, h1⟩ := UnaryCalc.poly_step 2 1 x
      exact ⟨out, h, h1⟩)

theorem sq_budget_le (x : ℕ) :
    PCPSerializerCapacity.Power.budget 2 1 x ≤ UnaryCalc.polyCoefficient 2 1 * (x + 1) ^ 3 :=
  UnaryCalc.poly_cost_polyBounded 2 1 x

/-! ## `rank` and `codeBound` -/

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem pop_le_small (a : DecompositionAlgorithm) (r : Request) : pop a r + 1 ≤ r.smallSize a := by
  have h1 := pop_le_input a r
  have h2 := input_le_small a r
  omega

theorem depth_le_small (a : DecompositionAlgorithm) (r : Request) : depth a r ≤ 256 * r.smallSize a := by
  rw [depth_eq]
  have h1 := clog_le_self (touch a r * 256)
  have h2 := touch_le_pop a r
  have h3 := pop_le_small a r
  omega

theorem rank_eq (a : DecompositionAlgorithm) (r : Request) :
    rank a r = max (depth a r) (Nat.clog 2 (pop a r)) := rfl

/-- **`rank` stage** (`max depth (clog₂ pop)`). -/
def rankStage (a : DecompositionAlgorithm) : UnaryStage a (rank a) := by
  have h : rank a = fun r => max (depth a r) (Nat.clog 2 (pop a r)) := funext (rank_eq a)
  rw [h]
  exact (depthStage a).pair ((popStage a).thenMap clogMap 70 1 (by
      intro r
      have h1 := pop_le_small a r
      have hs := one_le_small a r
      change 2 * (30 * (pop a r + 1)) + 2 ≤ _
      rw [pow_one]
      omega)) maxMap2 600 1 (by
      intro r
      have h1 := depth_le_small a r
      have h2 := clog_le_self (pop a r)
      have h3 := pop_le_small a r
      have hs := one_le_small a r
      change 2 * (max (depth a r) (Nat.clog 2 (pop a r)) + 1) + 2 ≤ _
      rw [pow_one]
      omega)

theorem codeBound_eq (a : DecompositionAlgorithm) (r : Request) :
    codeBound a r = 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r + childTotal a r + 1 := by
  unfold codeBound
  ring

theorem add_cost_le (x y s c1 c2 : ℕ) (hx : x ≤ c1 * s) (hy : y ≤ c2 * s) (hs : 1 ≤ s) :
    2 * (x + y) + 6 ≤ (2 * c1 + 2 * c2 + 6) * s ^ 1 := by
  rw [pow_one]
  have : 2 * (x + y) + 6 ≤ 2 * (c1 * s) + 2 * (c2 * s) + 6 * s := by omega
  calc 2 * (x + y) + 6 ≤ 2 * (c1 * s) + 2 * (c2 * s) + 6 * s := this
    _ = (2 * c1 + 2 * c2 + 6) * s := by ring

/-- **`codeBound` stage** (`(depth + 2·pop + 2)^2 + pop + N + 1`). -/
def codeBoundStage (a : DecompositionAlgorithm) : UnaryStage a (codeBound a) := by
  have h : codeBound a =
      fun r => 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r + childTotal a r + 1 :=
    funext (codeBound_eq a)
  rw [h]
  have s1 : UnaryStage a (fun r => depth a r + pop a r) :=
    (depthStage a).pair (popStage a) addMap2 (2 * 256 + 2 * 1 + 6) 1 (fun r =>
      add_cost_le _ _ _ 256 1 (depth_le_small a r) (by have := pop_le_small a r; omega) (one_le_small a r))
  have s2 : UnaryStage a (fun r => depth a r + pop a r + pop a r) :=
    s1.pair (popStage a) addMap2 (2 * 257 + 2 * 1 + 6) 1 (fun r =>
      add_cost_le _ _ _ 257 1 (by have := depth_le_small a r; have := pop_le_small a r; omega)
        (by have := pop_le_small a r; omega) (one_le_small a r))
  have s3 : UnaryStage a (fun r => depth a r + pop a r + pop a r + 1) :=
    s2.thenMap (plusMap 1) 600 1 (by
      intro r
      have := depth_le_small a r
      have := pop_le_small a r
      have hs := one_le_small a r
      change 2 * (depth a r + pop a r + pop a r + 1 + 1) + 2 ≤ _
      rw [pow_one]
      omega)
  have s4 : UnaryStage a (fun r => 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2) :=
    s3.thenMap sqMap (UnaryCalc.polyCoefficient 2 1 * 262 ^ 3) 3 (by
      intro r
      have h1 := depth_le_small a r
      have h2 := pop_le_small a r
      have hs := one_le_small a r
      change PCPSerializerCapacity.Power.budget 2 1 (depth a r + pop a r + pop a r + 1) ≤ _
      have hb := sq_budget_le (depth a r + pop a r + pop a r + 1)
      have hx : depth a r + pop a r + pop a r + 1 + 1 ≤ 262 * r.smallSize a := by omega
      have hp : (depth a r + pop a r + pop a r + 1 + 1) ^ 3 ≤ (262 * r.smallSize a) ^ 3 :=
        Nat.pow_le_pow_left hx 3
      calc PCPSerializerCapacity.Power.budget 2 1 (depth a r + pop a r + pop a r + 1)
          ≤ UnaryCalc.polyCoefficient 2 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 3 := hb
        _ ≤ UnaryCalc.polyCoefficient 2 1 * (262 * r.smallSize a) ^ 3 := Nat.mul_le_mul_left _ hp
        _ = UnaryCalc.polyCoefficient 2 1 * 262 ^ 3 * r.smallSize a ^ 3 := by ring)
  have hsq : ∀ r, 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 ≤ 262 ^ 2 * (r.smallSize a) ^ 2 := by
    intro r
    have h1 := depth_le_small a r
    have h2 := pop_le_small a r
    have hs := one_le_small a r
    have hx : depth a r + pop a r + pop a r + 1 + 1 ≤ 262 * r.smallSize a := by omega
    have hp := Nat.pow_le_pow_left hx 2
    calc 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 = (depth a r + pop a r + pop a r + 1 + 1) ^ 2 := by
          ring
      _ ≤ (262 * r.smallSize a) ^ 2 := hp
      _ = 262 ^ 2 * (r.smallSize a) ^ 2 := by ring
  have s5 : UnaryStage a (fun r => 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r) :=
    s4.pair (popStage a) addMap2 (2 * 262 ^ 2 + 2 + 6) 2 (by
      intro r
      have h1 := hsq r
      have h2 := pop_le_small a r
      have hs := one_le_small a r
      have hs2 : r.smallSize a ≤ (r.smallSize a) ^ 2 := Nat.le_self_pow (by norm_num) _
      have hs1 : 1 ≤ (r.smallSize a) ^ 2 := Nat.one_le_pow _ _ hs
      change 2 * (1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r) + 6 ≤ _
      nlinarith)
  have hchild : ∀ r, childTotal a r ≤ r.smallSize a := fun r => by
    have := child_le_small a r
    omega
  have s6 : UnaryStage a
      (fun r => 1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r + childTotal a r) :=
    s5.pair (childStage a) addMap2 (2 * 262 ^ 2 + 4 + 6) 2 (by
      intro r
      have h1 := hsq r
      have h2 := pop_le_small a r
      have h3 := hchild r
      have hs := one_le_small a r
      have hs2 : r.smallSize a ≤ (r.smallSize a) ^ 2 := Nat.le_self_pow (by norm_num) _
      have hs1 : 1 ≤ (r.smallSize a) ^ 2 := Nat.one_le_pow _ _ hs
      change 2 * (1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r + childTotal a r) + 6 ≤ _
      nlinarith)
  exact s6.thenMap (plusMap 1) (4 * 262 ^ 2 + 10) 2 (by
    intro r
    have h1 := hsq r
    have h2 := pop_le_small a r
    have h3 := hchild r
    have hs := one_le_small a r
    have hs2 : r.smallSize a ≤ (r.smallSize a) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hs1 : 1 ≤ (r.smallSize a) ^ 2 := Nat.one_le_pow _ _ hs
    change 2 * (1 * (depth a r + pop a r + pop a r + 1 + 1) ^ 2 + pop a r + childTotal a r + 1 + 1) + 2 ≤ _
    nlinarith)

end
end NearCubicWires.PacketsGlue.RequestMeta

