import Proof.Packets.PacketsMetaContract

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-- The input bank of a unary map: `replicate x true` on tape 0. -/
def unIn (n x : ℕ) : Fin n → List Bool := fun i => if i.val = 0 then List.replicate x true else []

/-- **A unary map**: one fixed machine, `x ↦ f x` in unary. -/
structure UnaryMap (f : ℕ → ℕ) where
  extra : ℕ
  states : ℕ
  machine : Machine (2 + extra) states
  cost : ℕ → ℕ
  run : ∀ x, ∃ (H' : Fin (2 + extra) → ℕ) (A' : Fin (2 + extra) → List Bool),
    Step machine (cost x) (fun _ => 0) (unIn (2 + extra) x) H' A' ∧
    A' ⟨1, by omega⟩ = List.replicate (f x) true ∧ H' ⟨1, by omega⟩ = 0

/-! ## Slots of `thenMap` -/

/-- The stage: input stays on 0, its value moves to 2, its private tapes follow. -/
def thS (es em : ℕ) : Fin (2 + es) → Fin (2 + (es + 1 + em)) :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else if k.val = 1 then ⟨2, by omega⟩
    else ⟨k.val + 1, by omega⟩

/-- The map: input from 2, output to 1, private tapes after the stage's. -/
def thM (es em : ℕ) : Fin (2 + em) → Fin (2 + (es + 1 + em)) :=
  fun k => if k.val = 0 then ⟨2, by omega⟩ else if k.val = 1 then ⟨1, by omega⟩
    else ⟨k.val + es + 1, by omega⟩

theorem thS_val (es em : ℕ) (k : Fin (2 + es)) :
    (thS es em k).val = if k.val = 0 then 0 else if k.val = 1 then 2 else k.val + 1 := by
  unfold thS; split_ifs <;> rfl

theorem thM_val (es em : ℕ) (k : Fin (2 + em)) :
    (thM es em k).val = if k.val = 0 then 2 else if k.val = 1 then 1 else k.val + es + 1 := by
  unfold thM; split_ifs <;> rfl

theorem thS_injective (es em : ℕ) : Function.Injective (thS es em) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [thS_val, thS_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem thM_injective (es em : ℕ) : Function.Injective (thM es em) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [thM_val, thM_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem thM_zero (es em : ℕ) (h : 0 < 2 + em) (h' : 1 < 2 + es) :
    thM es em ⟨0, h⟩ = thS es em ⟨1, h'⟩ := by
  apply Fin.ext; rw [thM_val, thS_val]; simp

theorem thM_off (es em : ℕ) (k : Fin (2 + em)) (hk : k.val ≠ 0) (j : Fin (2 + es)) :
    thS es em j ≠ thM es em k := by
  intro h
  have hv := congrArg Fin.val h
  rw [thS_val, thM_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

theorem thM_val_ne_zero (es em : ℕ) (k : Fin (2 + em)) : (thM es em k).val ≠ 0 := by
  rw [thM_val]
  split_ifs <;> omega

theorem thS_val_ne_zero (es em : ℕ) (k : Fin (2 + es)) (hk : k.val ≠ 0) : (thS es em k).val ≠ 0 := by
  rw [thS_val, if_neg hk]
  split_ifs <;> omega

theorem thM_ne_zero (es em : ℕ) (k : Fin (2 + em)) : thM es em k ≠ ⟨0, by omega⟩ := by
  intro h
  have hv : (thM es em k).val = 0 := by rw [h]
  exact thM_val_ne_zero es em k hv

theorem thS_ne_one (es em : ℕ) (j : Fin (2 + es)) : thS es em j ≠ ⟨1, by omega⟩ := by
  intro h
  have hv : (thS es em j).val = 1 := by rw [h]
  rw [thS_val] at hv
  split_ifs at hv <;> omega

theorem inBank_val (n : ℕ) (w : List Bool) (i : Fin n) :
    inBank n w i = if i.val = 0 then RepairOrdinary.frame w else [] := rfl

/-! ## `thenMap` -/

/-- The composite machine. -/
def thenMachine {a : DecompositionAlgorithm} {v : Request → ℕ} {f : ℕ → ℕ}
    (s : UnaryStage a v) (m : UnaryMap f) :=
  Composition.machine (RecoveryFocus.machine (thS s.extra m.extra) s.machine)
    (RecoveryFocus.machine (thM s.extra m.extra) m.machine)

theorem then_run {a : DecompositionAlgorithm} {v : Request → ℕ} {f : ℕ → ℕ}
    (s : UnaryStage a v) (m : UnaryMap f) (r : Request) :
    ∃ (H' : Fin (2 + (s.extra + 1 + m.extra)) → ℕ) (A' : Fin (2 + (s.extra + 1 + m.extra)) → List Bool),
      Step (thenMachine s m) (s.cost r + 1 + m.cost (v r)) (fun _ => 0)
        (inBank (2 + (s.extra + 1 + m.extra)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate (f (v r)) true ∧ H' ⟨1, by omega⟩ = 0 := by
  obtain ⟨H1, A1, hs, h0, hh0, h1, hh1⟩ := s.run r
  have d1 := hs.dock (thS s.extra m.extra) (thS_injective _ _) (fun _ => 0)
    (inBank (2 + (s.extra + 1 + m.extra)) (Request.input a r)) (fun _ => rfl)
    (by
      intro k
      rw [inBank_val, inBank_val]
      by_cases hk : k.val = 0
      · rw [if_pos (by rw [thS_val, if_pos hk]), if_pos hk]
      · rw [if_neg (thS_val_ne_zero _ _ k hk), if_neg hk])
  obtain ⟨H2, A2, hm, hv, hhv⟩ := m.run (v r)
  set H1' := dockH (thS s.extra m.extra) (fun _ => 0) H1 with hH1'
  set A1' := install (thS s.extra m.extra) (inBank (2 + (s.extra + 1 + m.extra)) (Request.input a r)) A1
    with hA1'
  have d2 := hm.dock (thM s.extra m.extra) (thM_injective _ _) H1' A1'
    (by
      intro k
      by_cases hk : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hk', thM_zero _ _ _ (by omega), hH1', dockH_slot _ (thS_injective _ _)]
        exact hh1
      · rw [hH1', dockH_other _ _ _ _ (fun j => thM_off _ _ k hk j)])
    (by
      intro k
      by_cases hk : k.val = 0
      · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hk', thM_zero _ _ _ (by omega), hA1', install_slot _ (thS_injective _ _), h1]
        rfl
      · rw [hA1', install_other _ _ _ _ (fun j => thM_off _ _ k hk j), inBank_val,
          if_neg (thM_val_ne_zero _ _ k)]
        simp [unIn, hk])
  have hall := d1.seq d2
  have e0 : (⟨0, by omega⟩ : Fin (2 + (s.extra + 1 + m.extra))) = thS s.extra m.extra ⟨0, by omega⟩ := by
    apply Fin.ext; rw [thS_val]; simp
  have e1 : (⟨1, by omega⟩ : Fin (2 + (s.extra + 1 + m.extra))) = thM s.extra m.extra ⟨1, by omega⟩ := by
    apply Fin.ext; rw [thM_val]; simp
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_⟩
  · rw [install_other _ _ _ _ (fun k => thM_ne_zero _ _ k), e0, hA1',
      install_slot _ (thS_injective _ _)]
    exact h0
  · rw [dockH_other _ _ _ _ (fun k => (thM_ne_zero _ _ k)), e0, hH1', dockH_slot _ (thS_injective _ _)]
    exact hh0
  · rw [e1, install_slot _ (thM_injective _ _)]
    exact hv
  · rw [e1, dockH_slot _ (thM_injective _ _)]
    exact hhv

theorem pow_mono_small (a : DecompositionAlgorithm) (r : Request) (d e : ℕ) :
    (r.smallSize a) ^ d ≤ (r.smallSize a) ^ (d + e) := by
  have h : 1 ≤ r.smallSize a := by
    unfold Request.smallSize
    exact Nat.le_add_left 1 _
  exact Nat.pow_le_pow_right h (by omega)

/-- **A stage followed by a unary map.** -/
def UnaryStage.thenMap {a : DecompositionAlgorithm} {v : Request → ℕ} {f : ℕ → ℕ}
    (s : UnaryStage a v) (m : UnaryMap f) (c d : ℕ)
    (hc : ∀ r, m.cost (v r) ≤ c * (r.smallSize a) ^ d) : UnaryStage a (fun r => f (v r)) where
  extra := s.extra + 1 + m.extra
  states := _
  machine := thenMachine s m
  cost := fun r => s.cost r + 1 + m.cost (v r)
  coefficient := s.coefficient + 1 + c
  degree := s.degree + d
  cost_le := by
    intro r
    have h1 := s.cost_le r
    have h2 := hc r
    have p1 := pow_mono_small a r s.degree d
    have p2 : (r.smallSize a) ^ d ≤ (r.smallSize a) ^ (s.degree + d) := by
      rw [Nat.add_comm]; exact pow_mono_small a r d s.degree
    have p0 : 1 ≤ (r.smallSize a) ^ (s.degree + d) := Nat.one_le_pow _ _ (by
      unfold Request.smallSize; exact Nat.succ_pos _)
    have q1 := Nat.mul_le_mul_left s.coefficient p1
    have q2 := Nat.mul_le_mul_left c p2
    calc s.cost r + 1 + m.cost (v r)
        ≤ s.coefficient * (r.smallSize a) ^ s.degree + (r.smallSize a) ^ (s.degree + d) +
            c * (r.smallSize a) ^ d := Nat.add_le_add (Nat.add_le_add h1 p0) h2
      _ ≤ s.coefficient * (r.smallSize a) ^ (s.degree + d) + (r.smallSize a) ^ (s.degree + d) +
            c * (r.smallSize a) ^ (s.degree + d) := Nat.add_le_add (Nat.add_le_add q1 le_rfl) q2
      _ = (s.coefficient + 1 + c) * (r.smallSize a) ^ (s.degree + d) := by ring
  run := then_run s m

end
end NearCubicWires.PacketsGlue.RequestMeta

