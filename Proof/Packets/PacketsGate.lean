import Proof.Packets.PacketsNatAt
import Proof.Packets.PacketsFieldWidth
import Proof.CaseAnalysis.RowsOriginalSwitch

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## Gated stages -/

/-- **A stage owed only where the gate is nonzero** (same entry/exit shape as `UnaryStage`). -/
structure GatedStage (a : DecompositionAlgorithm) (g v : Request → ℕ) where
  extra : ℕ
  states : ℕ
  machine : Machine (2 + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, g r ≠ 0 → cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ r, g r ≠ 0 → ∃ (H' : Fin (2 + extra) → ℕ) (A' : Fin (2 + extra) → List Bool),
    Step machine (cost r) (fun _ => 0) (inBank (2 + extra) (Request.input a r)) H' A' ∧
    A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
    A' ⟨1, by omega⟩ = List.replicate (v r) true ∧ H' ⟨1, by omega⟩ = 0

/-- The gated stage's slots: input `0` and output `1` stay, private tapes after the gate stage's. -/
def gM (es em : ℕ) : Fin (2 + em) → Fin (2 + (es + 1 + em)) :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else if k.val = 1 then ⟨1, by omega⟩
    else ⟨k.val + es + 1, by omega⟩

theorem gM_val (es em : ℕ) (k : Fin (2 + em)) :
    (gM es em k).val = if k.val = 0 then 0 else if k.val = 1 then 1 else k.val + es + 1 := by
  unfold gM; split_ifs <;> rfl

theorem gM_injective (es em : ℕ) : Function.Injective (gM es em) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [gM_val, gM_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem gM_off (es em : ℕ) (k : Fin (2 + em)) (hk : k.val ≠ 0) (j : Fin (2 + es)) :
    thS es em j ≠ gM es em k := by
  intro h
  have hv := congrArg Fin.val h
  rw [thS_val, gM_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

theorem gM_val_ne_zero (es em : ℕ) (k : Fin (2 + em)) (hk : k.val ≠ 0) : (gM es em k).val ≠ 0 := by
  rw [gM_val, if_neg hk]
  split_ifs <;> omega

/-- The gate cell: the gate stage's value tape. -/
def slotG (es em : ℕ) : Fin (2 + (es + 1 + em)) := ⟨2, by omega⟩

/-- The gated composite: the gate stage, then the one-bit switch on its first cell. -/
def gateMachine {a : DecompositionAlgorithm} {gv v : Request → ℕ} (g : UnaryStage a gv) (s : GatedStage a gv v) :=
  Composition.machine (RecoveryFocus.machine (thS g.extra s.extra) g.machine)
    (CloseoutRowsOriginalSwitch.machine (RecoveryFocus.machine (gM g.extra s.extra) s.machine)
      (CloseoutRowsOriginalSwitch.stop (2 + (g.extra + 1 + s.extra))) (slotG g.extra s.extra))

theorem stop_step (t : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop t) 0 H A H A :=
  ⟨⟨⟨0, H, A⟩, 0, (⟨0, H, A⟩ : Configuration t 1).tapeCells⟩, rfl, rfl, rfl, le_refl 0⟩

/-- The gated composite's cost. -/
def gateCost {a : DecompositionAlgorithm} {gv v : Request → ℕ} (g : UnaryStage a gv) (s : GatedStage a gv v)
    (r : Request) : ℕ :=
  g.cost r + 1 + ((if gv r = 0 then 0 else s.cost r) + 2)

theorem gate_run {a : DecompositionAlgorithm} {gv v : Request → ℕ} (g : UnaryStage a gv) (s : GatedStage a gv v)
    (r : Request) :
    ∃ (H' : Fin (2 + (g.extra + 1 + s.extra)) → ℕ) (A' : Fin (2 + (g.extra + 1 + s.extra)) → List Bool),
      Step (gateMachine g s) (gateCost g s r) (fun _ => 0)
        (inBank (2 + (g.extra + 1 + s.extra)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate (if gv r = 0 then 0 else v r) true ∧ H' ⟨1, by omega⟩ = 0 := by
  obtain ⟨H1, A1, hs, h0, hh0, h1, hh1⟩ := g.run r
  have d1 := hs.dock (thS g.extra s.extra) (thS_injective _ _) (fun _ => 0)
    (inBank (2 + (g.extra + 1 + s.extra)) (Request.input a r)) (fun _ => rfl)
    (by
      intro k
      rw [inBank_val, inBank_val]
      by_cases hk : k.val = 0
      · rw [if_pos (by rw [thS_val, if_pos hk]), if_pos hk]
      · rw [if_neg (thS_val_ne_zero _ _ k hk), if_neg hk])
  set H1' := dockH (thS g.extra s.extra) (fun _ => 0) H1 with hH1'
  set A1' := install (thS g.extra s.extra) (inBank (2 + (g.extra + 1 + s.extra)) (Request.input a r)) A1
    with hA1'
  have e0 : (⟨0, by omega⟩ : Fin (2 + (g.extra + 1 + s.extra))) = thS g.extra s.extra ⟨0, by omega⟩ := by
    apply Fin.ext; rw [thS_val]; simp
  have e2 : slotG g.extra s.extra = thS g.extra s.extra ⟨1, by omega⟩ := by
    apply Fin.ext; rw [thS_val]; simp [slotG]
  have hA0 : A1' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) := by
    rw [e0, hA1', install_slot _ (thS_injective _ _)]; exact h0
  have hH0 : H1' ⟨0, by omega⟩ = 0 := by
    rw [e0, hH1', dockH_slot _ (thS_injective _ _)]; exact hh0
  have hA1 : A1' ⟨1, by omega⟩ = [] := by
    rw [hA1', install_other _ _ _ _ (fun j => thS_ne_one _ _ j), inBank_val]
    simp
  have hH1 : H1' ⟨1, by omega⟩ = 0 := by
    rw [hH1', dockH_other _ _ _ _ (fun j => thS_ne_one _ _ j)]
  have hA2 : A1' (slotG g.extra s.extra) = List.replicate (gv r) true := by
    rw [e2, hA1', install_slot _ (thS_injective _ _)]; exact h1
  have hH2 : H1' (slotG g.extra s.extra) = 0 := by
    rw [e2, hH1', dockH_slot _ (thS_injective _ _)]; exact hh1
  by_cases hg : gv r = 0
  · have hread : readTapeBit (A1' (slotG g.extra s.extra)) (H1' (slotG g.extra s.extra)) = false := by
      rw [hA2, hH2, hg]; rfl
    have d2 := CloseoutRowsOriginalSwitch.false_run (RecoveryFocus.machine (gM g.extra s.extra) s.machine)
      (CloseoutRowsOriginalSwitch.stop (2 + (g.extra + 1 + s.extra))) (slotG g.extra s.extra)
      (stop_step _ H1' A1') hread
    have hall := d1.seq d2
    refine ⟨H1', A1', ?_, hA0, hH0, ?_, hH1⟩
    · have hc : gateCost g s r = g.cost r + 1 + (0 + 2) := by
        unfold gateCost; rw [if_pos hg]
      rw [hc]; exact hall
    · rw [if_pos hg, hA1]; rfl
  · obtain ⟨H2, A2, hs2, g0, gh0, g1, gh1⟩ := s.run r hg
    have d2 := hs2.dock (gM g.extra s.extra) (gM_injective _ _) H1' A1'
      (by
        intro k
        by_cases hk : k.val = 0
        · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
          have e : gM g.extra s.extra ⟨0, by omega⟩ = ⟨0, by omega⟩ := by apply Fin.ext; rw [gM_val]; simp
          rw [hk', e, hH0]
        · rw [hH1', dockH_other _ _ _ _ (fun j => gM_off _ _ k hk j)])
      (by
        intro k
        by_cases hk : k.val = 0
        · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
          have e : gM g.extra s.extra ⟨0, by omega⟩ = ⟨0, by omega⟩ := by apply Fin.ext; rw [gM_val]; simp
          rw [hk', e, hA0]
          rfl
        · rw [hA1', install_other _ _ _ _ (fun j => gM_off _ _ k hk j), inBank_val, inBank_val,
            if_neg (gM_val_ne_zero _ _ k hk), if_neg hk])
    have hread : readTapeBit (A1' (slotG g.extra s.extra)) (H1' (slotG g.extra s.extra)) = true := by
      rw [hA2, hH2]
      have hpos : 0 < gv r := Nat.pos_of_ne_zero hg
      simp [readTapeBit, hpos]
    have d3 := CloseoutRowsOriginalSwitch.true_run _
      (CloseoutRowsOriginalSwitch.stop (2 + (g.extra + 1 + s.extra))) (slotG g.extra s.extra) d2 hread
    have hall := d1.seq d3
    have f0 : (⟨0, by omega⟩ : Fin (2 + (g.extra + 1 + s.extra))) = gM g.extra s.extra ⟨0, by omega⟩ := by
      apply Fin.ext; rw [gM_val]; simp
    have f1 : (⟨1, by omega⟩ : Fin (2 + (g.extra + 1 + s.extra))) = gM g.extra s.extra ⟨1, by omega⟩ := by
      apply Fin.ext; rw [gM_val]; simp
    refine ⟨dockH (gM g.extra s.extra) H1' H2, install (gM g.extra s.extra) A1' A2, ?_, ?_, ?_, ?_, ?_⟩
    · have hc : gateCost g s r = g.cost r + 1 + (s.cost r + 2) := by
        unfold gateCost; rw [if_neg hg]
      rw [hc]; exact hall
    · rw [f0, install_slot _ (gM_injective _ _)]; exact g0
    · rw [f0, dockH_slot _ (gM_injective _ _)]; exact gh0
    · rw [f1, install_slot _ (gM_injective _ _), if_neg hg]; exact g1
    · rw [f1, dockH_slot _ (gM_injective _ _)]; exact gh1

/-- **The gated stage**: value `if g r = 0 then 0 else v r`, one fixed machine. -/
def UnaryStage.gate {a : DecompositionAlgorithm} {gv v : Request → ℕ} (g : UnaryStage a gv)
    (s : GatedStage a gv v) : UnaryStage a (fun r => if gv r = 0 then 0 else v r) where
  extra := g.extra + 1 + s.extra
  states := _
  machine := gateMachine g s
  cost := gateCost g s
  coefficient := g.coefficient + s.coefficient + 3
  degree := g.degree + s.degree
  cost_le := by
    intro r
    have h1 := g.cost_le r
    have hS := one_le_small a r
    have p1 : (r.smallSize a) ^ g.degree ≤ (r.smallSize a) ^ (g.degree + s.degree) :=
      pow_le_pow_small a r _ _ (by omega)
    have p2 : (r.smallSize a) ^ s.degree ≤ (r.smallSize a) ^ (g.degree + s.degree) :=
      pow_le_pow_small a r _ _ (by omega)
    have p0 : 1 ≤ (r.smallSize a) ^ (g.degree + s.degree) := Nat.one_le_pow _ _ hS
    have q1 := Nat.mul_le_mul_left g.coefficient p1
    have q2 := Nat.mul_le_mul_left s.coefficient p2
    have h2 : (if gv r = 0 then 0 else s.cost r) ≤ s.coefficient * (r.smallSize a) ^ s.degree := by
      split_ifs with hg
      · exact Nat.zero_le _
      · exact s.cost_le r hg
    have e : (g.coefficient + s.coefficient + 3) * (r.smallSize a) ^ (g.degree + s.degree) =
        g.coefficient * (r.smallSize a) ^ (g.degree + s.degree) +
          s.coefficient * (r.smallSize a) ^ (g.degree + s.degree) + 3 * (r.smallSize a) ^ (g.degree + s.degree) := by
      ring
    unfold gateCost
    rw [e]
    omega
  run := gate_run g s

/-- Transport a stage along a pointwise equality of values. -/
def UnaryStage.ofEq {a : DecompositionAlgorithm} {v w : Request → ℕ} (s : UnaryStage a v)
    (h : ∀ r, v r = w r) : UnaryStage a w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  run := fun r => by
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := s.run r
    exact ⟨H', A', hs, h0, hh0, by rw [h1, h r], hh1⟩

/-! ## The header-scalar parser -/

/-- Its step bound: `k` skips and one decode on field 0. -/
def natAtBound (k : ℕ) (v : Request → ℕ) (r : Request) : ℕ :=
  2 * r.nativeWord.length + 2 * k +
    (8 * 2 ^ natBitLength (v r) + 10 * natBitLength (v r) + 6)

theorem native_le_input (a : DecompositionAlgorithm) (r : Request) :
    2 * r.nativeWord.length + 1 ≤ (r.input a).length := by
  have h := field_le_input a r 0
  have e : fields a r 0 = r.nativeWord := rfl
  rw [e, frame_length] at h
  exact h

/-- **The `k`-th natWord of `nativeWord`, where the gate is nonzero.** -/
def natAtGated (a : DecompositionAlgorithm) (k : ℕ) (gv v : Request → ℕ)
    (hdec : ∀ r, gv r ≠ 0 → ∃ (xs : List ℕ) (post : List Bool), xs.length = k ∧
      r.nativeWord = xs.flatMap natWord ++ natWord (v r) ++ post)
    (c d : ℕ) (hv : ∀ r, gv r ≠ 0 → v r ≤ c * (r.smallSize a) ^ d) : GatedStage a gv v where
  extra := 13 + 3 + 1
  states := _
  machine := fieldMachineE (NatAt.machineAt k) 0
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (2 * natAtBound k v r + 2)
  coefficient := 94 + 4 * k + 32 * c
  degree := d + 1
  cost_le := by
    intro r hg
    have hin := native_le_input a r
    have hS := input_le_small a r
    have hvr := hv r hg
    have hb := NatSum.two_pow_bitLength (v r)
    have hl := NatSum.natWord_length (v r)
    obtain ⟨xs, post, _, hw⟩ := hdec r hg
    have hnl : (natWord (v r)).length ≤ r.nativeWord.length := by rw [hw]; simp; omega
    have hs1 : 1 ≤ r.smallSize a := one_le_small a r
    have pA : r.smallSize a ≤ (r.smallSize a) ^ (d + 1) := by
      calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
        _ ≤ (r.smallSize a) ^ (d + 1) := pow_le_pow_small a r _ _ (by omega)
    have pB : (r.smallSize a) ^ d ≤ (r.smallSize a) ^ (d + 1) := pow_le_pow_small a r _ _ (by omega)
    have p0 : 1 ≤ (r.smallSize a) ^ (d + 1) := Nat.one_le_pow _ _ hs1
    have qc := Nat.mul_le_mul_left c pB
    have qk : k ≤ k * (r.smallSize a) ^ (d + 1) := Nat.le_mul_of_pos_right _ p0
    have e : (94 + 4 * k + 32 * c) * (r.smallSize a) ^ (d + 1) =
        94 * (r.smallSize a) ^ (d + 1) + 4 * (k * (r.smallSize a) ^ (d + 1)) +
          32 * (c * (r.smallSize a) ^ (d + 1)) := by ring
    unfold natAtBound
    rw [e]
    omega
  run := by
    intro r hg
    obtain ⟨xs, post, hk, hw⟩ := hdec r hg
    subst hk
    obtain ⟨T, H1, A1, hs, hv1, hT⟩ := NatAt.run_at xs [] post (v r) 0 0 0
    have hnl : (xs.flatMap natWord).length ≤ r.nativeWord.length := by rw [hw]; simp
    rw [List.nil_append, ← hw] at hs
    have e1 : NatAt.hd0 ([] : List Bool).length = fun _ => 0 := by
      funext j; fin_cases j <;> rfl
    have e2 : NatAt.tp0 (frame r.nativeWord) 0 0 0 = scanIn 3 (frame (fields a r 0)) := by
      funext j; fin_cases j <;> rfl
    rw [e1, e2] at hs
    have hs' := hs.enlarge (show T ≤ natAtBound xs.length v r by unfold natAtBound; omega)
    exact field_runE (e := 3) (NatAt.machineAt xs.length) 0 a r (v r) _ H1 A1 hs' hv1

end
end NearCubicWires.PacketsGlue.RequestMeta

