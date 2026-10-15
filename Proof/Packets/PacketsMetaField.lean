import Proof.Packets.PacketsMetaContract
import Proof.Packets.PacketsScan
import Proof.Rows.RequestFields

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## Masked reset from an empty log -/

/-- `Step.mask` with the log entering empty; the log's exit length is existential. -/
theorem step_mask0 {t s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (selected : Fin t → Bool)
    (hstart : ∀ i, selected i = true → hin i = 0) :
    ∃ k, Step (MaskedReset.machine p selected) (2*n+2)
      (Fin.addCases hin (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool)))
      (Fin.addCases (fun i => if selected i then 0 else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate k false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hhead : ∀ i, selected i = true → r.final.heads i ≤ r.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
    have h0 : (⟨p.start, hin, tin⟩ : Configuration t s).heads i = 0 := hstart i hi
    omega
  obtain ⟨result, hres, hfinal, hsteps, _⟩ := MaskedReset.reset_run p selected n _ r hr hhead
  have hentry : Rewind.recording (⟨p.start, hin, tin⟩ : Configuration t s) 0 =
      (⟨(MaskedReset.machine p selected).start, Fin.addCases hin (fun _ : Fin 1 => 0),
        Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool))⟩ : Configuration (t+1) (s+2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [Rewind.recording, Rewind.config, Fin.addCases_left]
      · have hj : j = 0 := Fin.eq_zero j
        subst hj
        simp only [Rewind.recording, Rewind.config, Fin.addCases_right, List.replicate_zero]
  rw [hentry] at hres
  have hfuel : 2*r.steps+2 ≤ 2*n+2 := by omega
  have hmore := runFrom_moreFuel (MaskedReset.machine p selected) (2*r.steps+2)
    (2*n+2-(2*r.steps+2)) _ result hres
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨r.steps, result, hmore, ?_, ?_, by omega⟩
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, hh]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, ht]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]

/-! ## The field-scan stage -/

/-- The splitter's 13 tapes inside the stage's 15: tape 0 stays 0, the rest shift past tape 1. -/
def rfSlots : Fin 13 → Fin 15 := fun i => if i.val = 0 then 0 else ⟨i.val + 1, by omega⟩

theorem rfSlots_injective : Function.Injective rfSlots := by decide

/-- The masked scanner: field `j` (splitter tape `j+3`, stage tape `j+4`), output tape 1, log 14. -/
def scanSlots (j : Fin 5) : Fin 3 → Fin 15 := ![⟨j.val + 4, by omega⟩, 1, 14]

theorem scanSlots_injective (j : Fin 5) : Function.Injective (scanSlots j) := by
  fin_cases j <;> decide

/-- One fixed machine per `(scanner, field)`. -/
def fieldMachine {s : ℕ} (M : Machine 2 s) (j : Fin 5) :=
  Composition.machine (RecoveryFocus.machine rfSlots RequestInputFields.machine)
    (RecoveryFocus.machine (scanSlots j) (MaskedReset.machine M (fun _ => true)))

/-- The request's five fields, as the splitter names them. -/
abbrev fields (a : DecompositionAlgorithm) (r : Request) := RequestInputFields.values a r

theorem field_le_input (a : DecompositionAlgorithm) (r : Request) (j : Fin 5) :
    (frame (fields a r j)).length ≤ (r.input a).length := by
  rw [← RequestInputFields.word_values]
  fin_cases j <;>
    simp [fields, RequestInputFields.word, RequestInputFields.chunks] <;> omega

theorem input_le_small (a : DecompositionAlgorithm) (r : Request) :
    (r.input a).length + 1 ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, n + 1 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem scan_zero (j : Fin 5) (h : 0 < 2 + 1) : scanSlots j ⟨0, h⟩ = rfSlots ⟨j.val + 3, by omega⟩ := by
  fin_cases j <;> rfl

theorem scan_one (j : Fin 5) (h : 1 < 2 + 1) : scanSlots j ⟨1, h⟩ = 1 := rfl

theorem scan_two (j : Fin 5) (h : 2 < 2 + 1) : scanSlots j ⟨2, h⟩ = 14 := rfl

theorem rf_ne_one (i : Fin 13) : rfSlots i ≠ 1 := by
  revert i; decide

theorem rf_ne_fourteen (i : Fin 13) : rfSlots i ≠ 14 := by
  revert i; decide

theorem scan_ne_zero (j : Fin 5) (i : Fin 3) : scanSlots j i ≠ rfSlots 0 := by
  revert i; fin_cases j <;> decide

theorem bank_field (ws : Fin 5 → List Bool) (j : Fin 5) :
    RequestInputFields.bank ws 5 ⟨j.val + 3, by omega⟩ = frame (ws j) := by
  fin_cases j <;> rfl

theorem heads_field (ws : Fin 5 → List Bool) (j : Fin 5) :
    RequestInputFields.heads ws 5 ⟨j.val + 3, by omega⟩ = 0 := by
  fin_cases j <;> rfl

/-- **The field-scan run.** Any scanner that turns field `j` into `replicate v true` (in `n` steps,
field preserved) gives a stage run: tape 0 the framed input, tape 1 the value, heads `0`. -/
theorem field_run {s : ℕ} (M : Machine 2 s) (j : Fin 5) (a : DecompositionAlgorithm) (r : Request)
    (v n : ℕ) (H1 : Fin 2 → ℕ)
    (hM : Step M n ![0, 0] ![frame (fields a r j), []] H1 ![frame (fields a r j), List.replicate v true]) :
    ∃ (H' : Fin (2 + 13) → ℕ) (A' : Fin (2 + 13) → List Bool),
      Step (fieldMachine M j) (6*(r.input a).length+17 + 1 + (2*n+2)) (fun _ => 0)
        (inBank (2 + 13) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate v true ∧ H' ⟨1, by omega⟩ = 0 := by
  have hA := RequestInputFields.request_run a r
  have d1 := hA.dock rfSlots rfSlots_injective (fun _ => 0) (inBank (2 + 13) (Request.input a r))
    (fun _ => rfl)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨k, hm⟩ := step_mask0 hM (fun _ => true) (by intro i _; fin_cases i <;> rfl)
  set ws := RequestInputFields.values a r with hws
  set H1' := dockH rfSlots (fun _ => 0) (RequestInputFields.heads ws 5) with hH1'
  set A1' := install rfSlots (inBank (2 + 13) (Request.input a r))
    (RequestInputFields.bank ws 5) with hA1'
  have hHd : ∀ i : Fin (2 + 1), H1' (scanSlots j i) = Fin.addCases ![0, 0] (fun _ : Fin 1 => 0) i := by
    intro i
    fin_cases i <;> dsimp only
    · rw [scan_zero, hH1', dockH_slot _ rfSlots_injective, heads_field]; rfl
    · rw [scan_one, hH1', dockH_other _ _ _ _ rf_ne_one]; rfl
    · rw [scan_two, hH1', dockH_other _ _ _ _ rf_ne_fourteen]; rfl
  have hAd : ∀ i : Fin (2 + 1), A1' (scanSlots j i) =
      Fin.addCases ![frame (fields a r j), []] (fun _ : Fin 1 => ([] : List Bool)) i := by
    intro i
    fin_cases i <;> dsimp only
    · rw [scan_zero, hA1', install_slot _ rfSlots_injective, bank_field]; rfl
    · rw [scan_one, hA1', install_other _ _ _ _ rf_ne_one]; rfl
    · rw [scan_two, hA1', install_other _ _ _ _ rf_ne_fourteen]; rfl
  have d2 := hm.dock (scanSlots j) (scanSlots_injective j) H1' A1' hHd hAd
  have hall := d1.seq d2
  have h0 : (⟨0, by omega⟩ : Fin (2 + 13)) = rfSlots 0 := rfl
  have h1 : (⟨1, by omega⟩ : Fin (2 + 13)) = scanSlots j 1 := rfl
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_⟩
  · rw [h0, install_other _ _ _ _ (scan_ne_zero j), hA1', install_slot _ rfSlots_injective]
    change RepairOrdinary.frame (RequestInputFields.word ws) = _
    rw [hws, RequestInputFields.word_values]
  · rw [h0, dockH_other _ _ _ _ (scan_ne_zero j), hH1', dockH_slot _ rfSlots_injective]
    rfl
  · rw [h1, install_slot _ (scanSlots_injective j)]
    rfl
  · rw [h1, dockH_slot _ (scanSlots_injective j)]
    rfl

/-! ## The two stages -/

theorem count_toNat (l : List Bool) : l.count true = (l.map Bool.toNat).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp [ih]
    · simp [ih]
      omega

theorem count_ofFn_mem {q : ℕ} (S : Finset (Fin q)) :
    (List.ofFn (fun x : Fin q => decide (x ∈ S))).count true = S.card := by
  rw [count_toNat, List.map_ofFn, List.sum_ofFn]
  have h : (∑ x : Fin q, (Bool.toNat ∘ fun x => decide (x ∈ S)) x) = ∑ x : Fin q, if x ∈ S then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]
  rw [h, Finset.sum_boole]
  simp

/-- `K` is the number of `true`s of the mask field. -/
theorem count_mask (a : DecompositionAlgorithm) (r : Request) :
    (fields a r 2).count true = liveCount a r := by
  change (CyclicChoice.mask (r.family a).occurrences r.liveScale).count true = _
  unfold CyclicChoice.mask
  rw [count_ofFn_mem]
  rfl

theorem cost_bound (a : DecompositionAlgorithm) (r : Request) (j : Fin 5) :
    6*(r.input a).length+17 + 1 + (2*(frame (fields a r j)).length+2) ≤ 28 * (r.smallSize a) ^ 1 := by
  have h1 := field_le_input a r j
  have h2 := input_le_small a r
  rw [pow_one]
  omega

theorem countTrue_step (w : List Bool) :
    Step PacketsGlue.CountTrue.machine (frame w).length ![0, 0] ![frame w, []]
      ![2 * w.length, w.count true] ![frame w, List.replicate (w.count true) true] := by
  have h := PacketsGlue.CountTrue.run [] w []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, _⟩ := h
  exact Step.of_run (hin := ![0, 0]) (tin := ![frame w, []]) hr
    (by rw [hf]; rfl) (by rw [hf]; rfl)

/-- **`liveCount` (K) stage.** -/
def liveStage (a : DecompositionAlgorithm) : UnaryStage a (liveCount a) where
  extra := 13
  states := _
  machine := fieldMachine PacketsGlue.CountTrue.machine 2
  cost := fun r => 6*(r.input a).length+17 + 1 + (2*(frame (fields a r 2)).length+2)
  coefficient := 28
  degree := 1
  cost_le := fun r => cost_bound a r 2
  run := by
    intro r
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := field_run PacketsGlue.CountTrue.machine 2 a r
      ((fields a r 2).count true) _ _ (countTrue_step (fields a r 2))
    exact ⟨H', A', hs, h0, hh0, by rw [h1, count_mask], hh1⟩

/-- The support field is the concatenation of one frame per occurrence. -/
theorem support_frames (a : DecompositionAlgorithm) (r : Request) :
    fields a r 1 = PacketsGlue.CountFrames.frames ((occ a r).map
      (fun g => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support)))) := by
  change r.supportWord a = _
  unfold Request.supportWord PacketsGlue.CountFrames.frames
  rw [List.map_map]
  rfl

theorem countFrames_step (xs : List (List Bool)) :
    Step PacketsGlue.CountFrames.machine (frame (PacketsGlue.CountFrames.frames xs)).length ![0, 0]
      ![frame (PacketsGlue.CountFrames.frames xs), []]
      ![(PacketsGlue.dbl (PacketsGlue.CountFrames.frames xs)).length, xs.length]
      ![frame (PacketsGlue.CountFrames.frames xs), List.replicate xs.length true] := by
  have h := PacketsGlue.CountFrames.run [] [] xs
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, _⟩ := h
  exact Step.of_run (hin := ![0, 0]) (tin := ![frame (PacketsGlue.CountFrames.frames xs), []]) hr
    (by rw [hf]; rfl) (by rw [hf]; rfl)

/-- **`pop` stage.** -/
def popStage (a : DecompositionAlgorithm) : UnaryStage a (pop a) where
  extra := 13
  states := _
  machine := fieldMachine PacketsGlue.CountFrames.machine 1
  cost := fun r => 6*(r.input a).length+17 + 1 + (2*(frame (fields a r 1)).length+2)
  coefficient := 28
  degree := 1
  cost_le := fun r => cost_bound a r 1
  run := by
    intro r
    have hs := countFrames_step ((occ a r).map
      (fun g => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support))))
    rw [← support_frames, List.length_map] at hs
    obtain ⟨H', A', hrun, h0, hh0, h1, hh1⟩ := field_run PacketsGlue.CountFrames.machine 1 a r
      (occ a r).length _ _ hs
    exact ⟨H', A', hrun, h0, hh0, h1, hh1⟩

end
end NearCubicWires.PacketsGlue.RequestMeta

