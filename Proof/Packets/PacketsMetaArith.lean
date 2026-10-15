import Proof.Packets.PacketsClog
import Proof.Packets.PacketsTouch
import Proof.MachineModel.BlockUnaryCalc

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

/-! ## `⌈log₂⌉` -/

/-- **`⌈log₂ x⌉` in unary.** -/
def clogMap : UnaryMap (fun x => Nat.clog 2 x) where
  extra := 3
  states := 11 + 2
  machine := MaskedReset.machine PacketsGlue.Clog.machine (fun _ => true)
  cost := fun x => 2 * (30 * (x + 1)) + 2
  run := by
    intro x
    obtain ⟨n, H1, A1, hs, hv, hn⟩ := PacketsGlue.Clog.run x
    obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hn) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 3)) = Fin.castAdd 1 (1 : Fin 4) := rfl
      rw [hc, Fin.addCases_left, hv]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 3)) = Fin.castAdd 1 (1 : Fin 4) := rfl
      rw [hc, Fin.addCases_left]
      rfl

/-! ## The template writer -/

namespace WriteTemplate

/-- One tape. State 0 writes the sentinel, `1..c` write ones, `c+1` steps back, `c+2` rewinds, `c+3`
halts. -/
def machine (c : ℕ) : Machine 1 (c + 4) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == c + 3
  rule := fun q b =>
    if q.val = 0 then some ⟨⟨1, by omega⟩, fun _ => some false, fun _ => .right⟩
    else if h : q.val ≤ c then some ⟨⟨q.val + 1, by omega⟩, fun _ => some true, fun _ => .right⟩
    else if q.val = c + 1 then some ⟨⟨c + 2, by omega⟩, fun _ => none, fun _ => .left⟩
    else if q.val = c + 2 then
      (if b 0 then some ⟨⟨c + 2, by omega⟩, fun _ => none, fun _ => .left⟩
       else some ⟨⟨c + 3, by omega⟩, fun _ => none, fun _ => .stay⟩)
    else none

def cfg (c : ℕ) (q : Fin (c + 4)) (T : List Bool) (h : ℕ) : Configuration 1 (c + 4) :=
  ⟨q, fun _ => h, fun _ => T⟩

theorem w0 (c : ℕ) : step (machine c) (cfg c 0 [] 0) = some (cfg c ⟨1, by omega⟩ [false] 1) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction, writeTapeBit]

theorem write_template (m : ℕ) :
    writeTapeBit (false :: List.replicate m true) (m + 1) true = false :: List.replicate (m + 1) true := by
  have h := write_end (false :: List.replicate m true) true
  simp only [List.length_cons, List.length_replicate] at h
  rw [h, List.replicate_succ']
  simp

theorem w1 (c m : ℕ) (hm : m + 1 ≤ c) :
    step (machine c) (cfg c ⟨m + 1, by omega⟩ (false :: List.replicate m true) (m + 1)) =
      some (cfg c ⟨m + 2, by omega⟩ (false :: List.replicate (m + 1) true) (m + 2)) := by
  have hj0 : ¬ m + 1 = 0 := by omega
  simp [step, machine, cfg, hj0, hm]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction, write_template]

theorem w2 (c : ℕ) : step (machine c) (cfg c ⟨c + 1, by omega⟩ (false :: List.replicate c true) (c + 1)) =
    some (cfg c ⟨c + 2, by omega⟩ (false :: List.replicate c true) c) := by
  have h1 : ¬ c + 1 = 0 := by omega
  have h2 : ¬ c + 1 ≤ c := by omega
  simp [step, machine, cfg, h1, h2]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem w3t (c p : ℕ) (hp : 1 ≤ p) (hpc : p ≤ c) :
    step (machine c) (cfg c ⟨c + 2, by omega⟩ (false :: List.replicate c true) p) =
      some (cfg c ⟨c + 2, by omega⟩ (false :: List.replicate c true) (p - 1)) := by
  have h1 : ¬ c + 2 = 0 := by omega
  have h2 : ¬ c + 2 ≤ c := by omega
  have h3 : ¬ c + 2 = c + 1 := by omega
  have hr : readTapeBit (false :: List.replicate c true) p = true := by
    rw [show p = (p - 1) + 1 by omega]
    exact read_replicate_true c (p - 1) (by omega)
  simp [step, machine, cfg, Configuration.scanned, h1, h2, h3, hr]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem w3f (c : ℕ) :
    step (machine c) (cfg c ⟨c + 2, by omega⟩ (false :: List.replicate c true) 0) =
      some (cfg c ⟨c + 3, by omega⟩ (false :: List.replicate c true) 0) := by
  have h1 : ¬ c + 2 = 0 := by omega
  have h2 : ¬ c + 2 ≤ c := by omega
  have h3 : ¬ c + 2 = c + 1 := by omega
  have hr : readTapeBit (false :: List.replicate c true) 0 = false := rfl
  simp [step, machine, cfg, Configuration.scanned, h1, h2, h3, hr]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem fill (c : ℕ) : ∀ (m : ℕ) (_hm : m ≤ c),
    Timed (machine c) (c - m) (cfg c ⟨m + 1, by omega⟩ (false :: List.replicate m true) (m + 1))
      (cfg c ⟨c + 1, by omega⟩ (false :: List.replicate c true) (c + 1)) := by
  intro m hm
  induction h : c - m generalizing m with
  | zero =>
    have : m = c := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have hne : ¬ m = c + 2 := by omega
    have t1 := Timed.single (p := machine c) (by simp [machine, cfg, hne]) (w1 c m (by omega))
    have t2 := ih (m + 1) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

theorem back (c : ℕ) : ∀ p : ℕ, p ≤ c →
    Timed (machine c) (p + 1) (cfg c ⟨c + 2, by omega⟩ (false :: List.replicate c true) p)
      (cfg c ⟨c + 3, by omega⟩ (false :: List.replicate c true) 0) := by
  intro p
  induction p with
  | zero => intro _; exact Timed.single (p := machine c) (by simp [machine, cfg]) (w3f c)
  | succ p ih =>
    intro hp
    have t1 := Timed.single (p := machine c) (by simp [machine, cfg]) (w3t c (p + 1) (by omega) hp)
    rw [show p + 1 - 1 = p by omega] at t1
    have t := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at t
    exact t

/-- **The template.** `[] → false :: 1^c`, head back at 0, in `2c + 3` steps. -/
theorem run (c : ℕ) : Step (machine c) (2 * c + 3) (fun _ => 0) (fun _ => []) (fun _ => 0)
    (fun _ => false :: List.replicate c true) := by
  have t1 := Timed.single (p := machine c) (by simp [machine, cfg]) (w0 c)
  have t2 := fill c 0 (by omega)
  have t3 := Timed.single (p := machine c) (by simp [machine, cfg]) (w2 c)
  have t4 := back c c (le_refl _)
  have t := ((t1.trans t2).trans t3).trans t4
  obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
  refine ⟨r, ?_, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩
  have e : 1 + (c - 0) + 1 + (c + 1) = 2 * c + 3 := by omega
  rw [e] at hr
  exact hr

end WriteTemplate

/-! ## `x ↦ x·c` -/

def scaleSlots : Fin 1 → Fin 4 := fun _ => 1

def scaleMachine (c : ℕ) :=
  Composition.machine (RecoveryFocus.machine scaleSlots (WriteTemplate.machine c))
    ClockUnaryProduct.machine

def scaleCost (c x : ℕ) : ℕ := (2 * c + 3) + 1 + (2 * (x * (2 * c + 3) + 2) + 2)

theorem scale_step (c x : ℕ) : ∃ A' : Fin (2 + 2) → List Bool,
    Step (scaleMachine c) (scaleCost c x) (fun _ => 0) (unIn (2 + 2) x) (fun _ => 0) A' ∧
      A' ⟨2, by omega⟩ = List.replicate (x * c) true := by
  have hw := (WriteTemplate.run c).dock scaleSlots (by intro a b _; exact Subsingleton.elim a b)
    (fun _ => 0) (unIn (2 + 2) x) (fun _ => rfl) (fun _ => rfl)
  have hp := UnaryCalc.product_step x c
  refine ⟨_, hw.seq (hp.congr_in ?_ ?_), rfl⟩
  · funext i; fin_cases i <;> simp [dockH, RecoveryFocus.pick, scaleSlots] <;> rfl
  · funext i; fin_cases i <;> simp [install, RecoveryFocus.pick, scaleSlots, unIn] <;> rfl

/-- **`x ↦ x·c` in unary.** -/
def scaleMap (c : ℕ) : UnaryMap (fun x => x * c) :=
  UnaryMap.ofSwap (e := 2) (scaleMachine c) ⟨2, by omega⟩ (by simp) (scaleCost c) (scale_step c)

/-! ## `depth` -/

theorem pop_le_input (a : DecompositionAlgorithm) (r : Request) : pop a r ≤ (r.input a).length := by
  have h := field_le_input a r 1
  have hs : fields a r 1 = CountFrames.frames ((occ a r).map
      (fun g => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support)))) := support_frames a r
  have hlen : ∀ xs : List (List Bool), xs.length ≤ (CountFrames.frames xs).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => rw [CountFrames.frames_cons, List.length_append, frame_length]; simp; omega
  have := hlen ((occ a r).map (fun g => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support))))
  rw [List.length_map, ← hs] at this
  rw [frame_length] at h
  unfold pop
  omega

theorem touch_le_pop (a : DecompositionAlgorithm) (r : Request) : touch a r ≤ pop a r := by
  unfold touch LiveRows.bound SupplierTouching.touchingCost pop
  calc ∑ gate, SupplierTouching.touchIndicator (live a r) (SupplierEstimator.occurrenceSupport (occ a r) gate)
      ≤ ∑ _gate : Fin (occ a r).length, 1 := by
        apply Finset.sum_le_sum; intro i _
        unfold SupplierTouching.touchIndicator; split_ifs <;> omega
    _ = (occ a r).length := by simp

theorem depth_eq (a : DecompositionAlgorithm) (r : Request) : depth a r = Nat.clog 2 (touch a r * 256) := by
  unfold depth SupplierWalkBridge.canonicalGradedDepth
  rw [Nat.mul_comm]

/-- **`depth` stage.** -/
def depthStage (a : DecompositionAlgorithm) : UnaryStage a (depth a) := by
  have h : depth a = fun r => Nat.clog 2 (touch a r * 256) := funext (depth_eq a)
  rw [h]
  exact ((touchStage a).thenMap (scaleMap 256) 2000 1 (by
      intro r
      have h1 := touch_le_pop a r
      have h2 := pop_le_input a r
      have h3 := input_le_small a r
      change scaleCost 256 (touch a r) ≤ _
      unfold scaleCost
      rw [pow_one]
      omega)).thenMap clogMap 20000 1 (by
      intro r
      have h1 := touch_le_pop a r
      have h2 := pop_le_input a r
      have h3 := input_le_small a r
      change 2 * (30 * (touch a r * 256 + 1)) + 2 ≤ _
      rw [pow_one]
      omega)

end
end NearCubicWires.PacketsGlue.RequestMeta

