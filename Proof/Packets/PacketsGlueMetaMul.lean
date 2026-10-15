import Proof.Packets.PacketsMetaPrime
import Proof.PCP.ProjectionDimensionTemplate

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

/-! ## Padding -/

theorem step_pad {t s n : ℕ} {p : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p n H A H' A') (cap : Fin t → ℕ) :
    Step p n H (fun i => ZeroPadding.pad (cap i) (A i)) H' (fun i => ZeroPadding.pad (cap i) (A' i)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨u, hu, hf, hsteps, _⟩ := ZeroPadding.run_config p cap n _ r hr
  refine ⟨u, hu, ?_, ?_, by omega⟩
  · rw [hf]; exact hh
  · rw [hf]; funext i; simp only [ZeroPadding.config, ht]

/-! ## Unary product -/

theorem tpl_step (n : ℕ) :
    Step (RepairSource.ProjectionNormalization.DimensionTemplate.machine false) (2 * n + 8) (fun _ => 0)
      ![List.replicate n true, [], []] (fun _ => 0)
      ![List.replicate n true, UnaryTemplate.tape n, List.replicate (n + 3) false] := by
  have h := CloseoutFinalSelector.step_of_clock (RepairSource.ProjectionNormalization.DimensionTemplate.ready false n)
  simpa [RepairSource.ProjectionNormalization.DimensionTemplate.input,
    RepairSource.ProjectionNormalization.DimensionTemplate.output] using h

theorem pad_tpl (y : ℕ) : ZeroPadding.pad (y + 2) (false :: List.replicate y true) = UnaryTemplate.tape y := by
  simp [ZeroPadding.pad, UnaryTemplate.tape]

theorem prod_step (x y : ℕ) :
    Step ClockUnaryProduct.machine (2 * (x * (2 * y + 3) + 2) + 2) (fun _ => 0)
      ![List.replicate x true, UnaryTemplate.tape y, [], []] (fun _ => 0)
      ![List.replicate x true, UnaryTemplate.tape y, List.replicate (x * y) true,
        List.replicate (x * (2 * y + 3) + 2) false] := by
  have h0 := UnaryCalc.product_step x y
  have hi : (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      ![List.replicate x true, false :: List.replicate y true, []] (fun _ : Fin 1 => [])) =
      ![List.replicate x true, false :: List.replicate y true, [], []] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at h0
  have h := step_pad h0 ![0, y + 2, 0, 0]
  have e1 : (fun i => ZeroPadding.pad (![0, y + 2, 0, 0] i)
      (![List.replicate x true, false :: List.replicate y true, [], []] i)) =
      ![List.replicate x true, UnaryTemplate.tape y, [], []] := by
    funext i; fin_cases i <;> simp [pad_tpl]
  have e2 : (fun i => ZeroPadding.pad (![0, y + 2, 0, 0] i)
      (![List.replicate x true, false :: List.replicate y true, List.replicate (x * y) true,
        List.replicate (x * (2 * y + 3) + 2) false] i)) =
      ![List.replicate x true, UnaryTemplate.tape y, List.replicate (x * y) true,
        List.replicate (x * (2 * y + 3) + 2) false] := by
    funext i; fin_cases i <;> simp [pad_tpl]
  rw [e1, e2] at h
  exact h

theorem dockH_zero {t u : ℕ} (sl : Fin t → Fin u) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => (0 : ℕ) := by
  funext i; unfold dockH; split <;> rfl

def slA : Fin 3 → Fin 6 := ![1, 3, 5]
def slB : Fin 4 → Fin 6 := ![0, 3, 2, 4]

theorem slA_inj : Function.Injective slA := by decide
theorem slB_inj : Function.Injective slB := by decide

def mulMachine :=
  Composition.machine
    (RecoveryFocus.machine slA (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
    (RecoveryFocus.machine slB ClockUnaryProduct.machine)

theorem mul_step (x y : ℕ) : ∃ A' : Fin 6 → List Bool,
    Step mulMachine (2 * y + 8 + 1 + (2 * (x * (2 * y + 3) + 2) + 2)) (fun _ => 0) (unIn2 6 x y) (fun _ => 0) A' ∧
      A' 2 = List.replicate (x * y) true := by
  have d1 := (tpl_step y).dock slA slA_inj (fun _ => 0) (unIn2 6 x y) (fun _ => rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [dockH_zero] at d1
  set A1 := install slA (unIn2 6 x y)
    ![List.replicate y true, UnaryTemplate.tape y, List.replicate (y + 3) false] with hA1
  have a0 : A1 0 = List.replicate x true := by
    rw [hA1, install_other _ _ _ _ (by decide)]; rfl
  have a3 : A1 3 = UnaryTemplate.tape y := by
    rw [hA1, show (3 : Fin 6) = slA 1 from rfl, install_slot _ slA_inj]; rfl
  have a2 : A1 2 = [] := by
    rw [hA1, install_other _ _ _ _ (by decide)]; rfl
  have a4 : A1 4 = [] := by
    rw [hA1, install_other _ _ _ _ (by decide)]; rfl
  have d2 := (prod_step x y).dock slB slB_inj (fun _ => 0) A1 (fun _ => rfl)
    (by
      intro k; fin_cases k
      · exact a0
      · exact a3
      · exact a2
      · exact a4)
  rw [dockH_zero] at d2
  refine ⟨_, d1.seq d2, ?_⟩
  rw [show (2 : Fin 6) = slB 2 from rfl, install_slot _ slB_inj]
  rfl

/-- **`x * y` in unary.** -/
def mulMap2 : UnaryMap2 (fun x y => x * y) where
  extra := 3
  states := _
  machine := mulMachine
  cost := fun x y => 2 * y + 8 + 1 + (2 * (x * (2 * y + 3) + 2) + 2)
  run := by
    intro x y
    obtain ⟨A', h, h2⟩ := mul_step x y
    exact ⟨fun _ => 0, A', h, h2, rfl⟩

theorem mul_cost (x y : ℕ) : mulMap2.cost x y ≤ 8 * (x + y + 3) ^ 2 := by
  change 2 * y + 8 + 1 + (2 * (x * (2 * y + 3) + 2) + 2) ≤ _
  nlinarith

/-! ## Polynomially costed composition -/

theorem pow_le_pow_small (a : DecompositionAlgorithm) (r : Request) (d e : ℕ) (h : d ≤ e) :
    (r.smallSize a) ^ d ≤ (r.smallSize a) ^ e := Nat.pow_le_pow_right (one_le_small a r) h

/-- `thenMap`, with the side condition discharged from a polynomial cost of the map. -/
def UnaryStage.thenMapP {a : DecompositionAlgorithm} {v : Request → ℕ} {f : ℕ → ℕ}
    (s : UnaryStage a v) (m : UnaryMap f) (cm dm : ℕ) (hm : ∀ x, m.cost x ≤ cm * (x + 3) ^ dm) :
    UnaryStage a (fun r => f (v r)) :=
  s.thenMap m (cm * (s.coefficient + 7) ^ dm) ((s.degree + 1) * dm) (by
    intro r
    have hb := s.value_bound r
    have hp : (v r + 3) ^ dm ≤ ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) ^ dm :=
      Nat.pow_le_pow_left hb dm
    have e : ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) ^ dm =
        (s.coefficient + 7) ^ dm * (r.smallSize a) ^ ((s.degree + 1) * dm) := by
      rw [mul_pow, ← pow_mul]
    rw [e] at hp
    calc m.cost (v r) ≤ cm * (v r + 3) ^ dm := hm (v r)
      _ ≤ cm * ((s.coefficient + 7) ^ dm * (r.smallSize a) ^ ((s.degree + 1) * dm)) :=
          Nat.mul_le_mul_left _ hp
      _ = cm * (s.coefficient + 7) ^ dm * (r.smallSize a) ^ ((s.degree + 1) * dm) := by
          rw [Nat.mul_assoc])

/-- `pair`, with the side condition discharged from a polynomial cost of the map. -/
def UnaryStage.pairP {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {f : ℕ → ℕ → ℕ}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : UnaryMap2 f) (cm dm : ℕ)
    (hm : ∀ x y, m.cost x y ≤ cm * (x + y + 3) ^ dm) : UnaryStage a (fun r => f (v1 r) (v2 r)) :=
  s1.pair s2 m (cm * (s1.coefficient + s2.coefficient + 14) ^ dm) ((s1.degree + s2.degree + 2) * dm) (by
    intro r
    have b1 := s1.value_bound r
    have b2 := s2.value_bound r
    set D := s1.degree + s2.degree + 2
    have p1 := pow_le_pow_small a r (s1.degree + 1) D (by omega)
    have p2 := pow_le_pow_small a r (s2.degree + 1) D (by omega)
    have q1 := Nat.mul_le_mul_left (s1.coefficient + 7) p1
    have q2 := Nat.mul_le_mul_left (s2.coefficient + 7) p2
    have hb : v1 r + v2 r + 3 ≤ (s1.coefficient + s2.coefficient + 14) * (r.smallSize a) ^ D := by
      have e : (s1.coefficient + s2.coefficient + 14) * (r.smallSize a) ^ D =
          (s1.coefficient + 7) * (r.smallSize a) ^ D + (s2.coefficient + 7) * (r.smallSize a) ^ D := by ring
      rw [e]; omega
    have hp := Nat.pow_le_pow_left hb dm
    have e : ((s1.coefficient + s2.coefficient + 14) * (r.smallSize a) ^ D) ^ dm =
        (s1.coefficient + s2.coefficient + 14) ^ dm * (r.smallSize a) ^ (D * dm) := by
      rw [mul_pow, ← pow_mul]
    rw [e] at hp
    calc m.cost (v1 r) (v2 r) ≤ cm * (v1 r + v2 r + 3) ^ dm := hm _ _
      _ ≤ cm * ((s1.coefficient + s2.coefficient + 14) ^ dm * (r.smallSize a) ^ (D * dm)) :=
          Nat.mul_le_mul_left _ hp
      _ = cm * (s1.coefficient + s2.coefficient + 14) ^ dm * (r.smallSize a) ^ (D * dm) := by
          rw [Nat.mul_assoc])

theorem add_cost (x y : ℕ) : addMap2.cost x y ≤ 6 * (x + y + 3) ^ 1 := by
  change 2 * (x + y) + 6 ≤ _
  rw [pow_one]; omega

theorem plus_cost (c x : ℕ) : (plusMap c).cost x ≤ (2 * c + 4) * (x + 3) ^ 1 := by
  change 2 * (x + 1 + c) + 2 ≤ _
  rw [pow_one]; nlinarith

theorem clog_cost (x : ℕ) : clogMap.cost x ≤ 62 * (x + 3) ^ 1 := by
  change 2 * (30 * (x + 1)) + 2 ≤ _
  rw [pow_one]; omega

theorem scale_cost (c x : ℕ) : (scaleMap c).cost x ≤ (4 * c + 12) * (x + 3) ^ 2 := by
  change scaleCost c x ≤ _
  unfold scaleCost
  have e : (4 * c + 12) * (x + 3) ^ 2 = 4 * (c * x * x) + 24 * (c * x) + 36 * c + 12 * (x * x) + 72 * x + 108 := by
    ring
  have e2 : 2 * c + 3 + 1 + (2 * (x * (2 * c + 3) + 2) + 2) = 4 * (c * x) + 6 * x + 2 * c + 10 := by ring
  rw [e, e2]
  omega

/-! ## The input length -/

namespace LenM

/-- Tape 0 a framed word, tape 1 the output: one output `true` per marker. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then some (if b 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, none], ![.stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, none], ![.right, .stay]⟩
    else none

def cfg (q : Fin 3) (w : List Bool) (i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, o], ![RepairOrdinary.frame w, List.replicate o true]⟩

theorem s0t (w : List Bool) (i : ℕ) (hi : i < w.length) :
    step machine (cfg 0 w (2 * i) i) = some (cfg 1 w (2 * i + 1) (i + 1)) := by
  have hr := NatSum.read_marker w i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate]

theorem s1 (w : List Bool) (i o : ℕ) : step machine (cfg 1 w i o) = some (cfg 0 w (i + 1) o) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s0f (w : List Bool) :
    step machine (cfg 0 w (2 * w.length) w.length) = some (cfg 2 w (2 * w.length) w.length) := by
  have hr := NatSum.read_end w
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem loop (w : List Bool) : ∀ i, i ≤ w.length →
    Timed machine (2 * (w.length - i)) (cfg 0 w (2 * i) i) (cfg 0 w (2 * w.length) w.length) := by
  intro i hi
  induction h : w.length - i generalizing i with
  | zero =>
    have : i = w.length := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s0t w i (by omega))
    have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s1 w (2 * i + 1) (i + 1))
    have t3 := ih (i + 1) (by omega) (by omega)
    have e : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [e] at t2
    have t := (t1.trans t2).trans t3
    rw [show 1 + 1 + 2 * k = 2 * (k + 1) by omega] at t
    exact t

theorem run (w : List Bool) : Step machine (2 * w.length + 1) ![0, 0] ![RepairOrdinary.frame w, []]
    ![2 * w.length, w.length] ![RepairOrdinary.frame w, List.replicate w.length true] := by
  have t1 := loop w 0 (by omega)
  have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s0f w)
  have t := t1.trans t2
  obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
  refine ⟨r, ?_, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩
  have hc : (⟨machine.start, ![0, 0], ![RepairOrdinary.frame w, []]⟩ : Configuration 2 3) = cfg 0 w (2 * 0) 0 := rfl
  rw [hc]
  simpa using hr

end LenM

/-- **`|input|` stage.** -/
def inputLenStage (a : DecompositionAlgorithm) : UnaryStage a (fun r => (Request.input a r).length) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine LenM.machine (fun _ => true)
  cost := fun r => 2 * (2 * (Request.input a r).length + 1) + 2
  coefficient := 6
  degree := 1
  cost_le := by
    intro r
    have h := input_le_small a r
    rw [pow_one]; omega
  run := by
    intro r
    obtain ⟨k, hm⟩ := step_mask0 (LenM.run (Request.input a r)) (fun _ => true) (by intro i _; fin_cases i <;> rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp only [Fin.addCases_right]
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [inBank]
    · rfl
    · rfl
    · rfl
    · rfl

end
end NearCubicWires.PacketsGlue.RequestMeta

