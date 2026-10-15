import Proof.Packets.PacketsMetaBig

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

/-! ## Word stages -/

/-- **One word, one fixed machine** (the `UnaryStage` shape with an arbitrary output word). -/
structure WordStage (a : DecompositionAlgorithm) (w : Request → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (2 + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ r, ∃ (H' : Fin (2 + extra) → ℕ) (A' : Fin (2 + extra) → List Bool),
    Step machine (cost r) (fun _ => 0) (inBank (2 + extra) (Request.input a r)) H' A' ∧
    A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
    A' ⟨1, by omega⟩ = w r ∧ H' ⟨1, by omega⟩ = 0

/-- A unary stage is a word stage. -/
def UnaryStage.toWord {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v) :
    WordStage a (fun r => List.replicate (v r) true) where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  run := s.run

/-- **A word-valued map**: `replicate x true` on tape 0 ↦ `g x` on tape 1 (head 0). -/
structure WordMap (g : ℕ → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (2 + extra) states
  cost : ℕ → ℕ
  run : ∀ x, ∃ (H' : Fin (2 + extra) → ℕ) (A' : Fin (2 + extra) → List Bool),
    Step machine (cost x) (fun _ => 0) (unIn (2 + extra) x) H' A' ∧
    A' ⟨1, by omega⟩ = g x ∧ H' ⟨1, by omega⟩ = 0

def tplMap : WordMap UnaryTemplate.tape where
  extra := 1
  states := _
  machine := RepairSource.ProjectionNormalization.DimensionTemplate.machine false
  cost := fun x => 2 * x + 8
  run := by
    intro x
    refine ⟨_, _, (tpl_step x).congr_in rfl ?_, rfl, rfl⟩
    funext i; fin_cases i <;> rfl

theorem thenWord_run {a : DecompositionAlgorithm} {v : Request → ℕ} {g : ℕ → List Bool}
    (s : UnaryStage a v) (m : WordMap g) (r : Request) :
    ∃ (H' : Fin (2 + (s.extra + 1 + m.extra)) → ℕ) (A' : Fin (2 + (s.extra + 1 + m.extra)) → List Bool),
      Step (Composition.machine (RecoveryFocus.machine (thS s.extra m.extra) s.machine)
        (RecoveryFocus.machine (thM s.extra m.extra) m.machine)) (s.cost r + 1 + m.cost (v r)) (fun _ => 0)
        (inBank (2 + (s.extra + 1 + m.extra)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = g (v r) ∧ H' ⟨1, by omega⟩ = 0 := by
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

/-- **A stage followed by a word-valued map.** -/
def UnaryStage.thenWord {a : DecompositionAlgorithm} {v : Request → ℕ} {g : ℕ → List Bool}
    (s : UnaryStage a v) (m : WordMap g) (c d : ℕ)
    (hc : ∀ r, m.cost (v r) ≤ c * (r.smallSize a) ^ d) : WordStage a (fun r => g (v r)) where
  extra := s.extra + 1 + m.extra
  states := _
  machine := Composition.machine (RecoveryFocus.machine (thS s.extra m.extra) s.machine)
    (RecoveryFocus.machine (thM s.extra m.extra) m.machine)
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
    have p0 : 1 ≤ (r.smallSize a) ^ (s.degree + d) := Nat.one_le_pow _ _ (one_le_small a r)
    have q1 := Nat.mul_le_mul_left s.coefficient p1
    have q2 := Nat.mul_le_mul_left c p2
    calc s.cost r + 1 + m.cost (v r)
        ≤ s.coefficient * (r.smallSize a) ^ s.degree + (r.smallSize a) ^ (s.degree + d) +
            c * (r.smallSize a) ^ d := Nat.add_le_add (Nat.add_le_add h1 p0) h2
      _ ≤ s.coefficient * (r.smallSize a) ^ (s.degree + d) + (r.smallSize a) ^ (s.degree + d) +
            c * (r.smallSize a) ^ (s.degree + d) := Nat.add_le_add (Nat.add_le_add q1 le_rfl) q2
      _ = (s.coefficient + 1 + c) * (r.smallSize a) ^ (s.degree + d) := by ring
  run := thenWord_run s m

/-! ## Vector stages -/

/-- **Several words, one fixed machine**: `outs j r` on tape `j + 1` for `j < n`, all heads `0`, the input kept
on tape 0; private tapes existential. -/
structure VecStage (a : DecompositionAlgorithm) (n : ℕ) (outs : ℕ → Request → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (1 + n + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ r, ∃ (H' : Fin (1 + n + extra) → ℕ) (A' : Fin (1 + n + extra) → List Bool),
    Step machine (cost r) (fun _ => 0) (inBank (1 + n + extra) (Request.input a r)) H' A' ∧
    A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
    ∀ j (hj : j < n), A' ⟨j + 1, by omega⟩ = outs j r ∧ H' ⟨j + 1, by omega⟩ = 0

/-- The machine that halts at once. -/
def haltM : Machine 1 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

/-- No words. -/
def VecStage.nil (a : DecompositionAlgorithm) (outs : ℕ → Request → List Bool) : VecStage a 0 outs where
  extra := 0
  states := 1
  machine := haltM
  cost := fun _ => 0
  coefficient := 0
  degree := 0
  cost_le := fun _ => Nat.zero_le _
  run := by
    intro r
    refine ⟨fun _ => 0, inBank (1 + 0 + 0) (Request.input a r), ⟨_, runFrom_zero_of_halted haltM _ rfl, rfl, rfl,
      le_refl 0⟩, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- Slots of the vector so far: outputs keep their tapes, private tapes shift by one. -/
def vA (n eV es : ℕ) : Fin (1 + n + eV) → Fin (1 + (n + 1) + (eV + es)) :=
  fun k => if k.val ≤ n then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩

/-- Slots of the new word: input 0, output `n + 1`, private tapes last. -/
def vB (n eV es : ℕ) : Fin (2 + es) → Fin (1 + (n + 1) + (eV + es)) :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else if k.val = 1 then ⟨n + 1, by omega⟩
    else ⟨k.val + n + eV, by omega⟩

theorem vA_val (n eV es : ℕ) (k : Fin (1 + n + eV)) :
    (vA n eV es k).val = if k.val ≤ n then k.val else k.val + 1 := by
  unfold vA; split_ifs <;> rfl

theorem vB_val (n eV es : ℕ) (k : Fin (2 + es)) :
    (vB n eV es k).val = if k.val = 0 then 0 else if k.val = 1 then n + 1 else k.val + n + eV := by
  unfold vB; split_ifs <;> rfl

theorem vA_inj (n eV es : ℕ) : Function.Injective (vA n eV es) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [vA_val, vA_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem vB_inj (n eV es : ℕ) : Function.Injective (vB n eV es) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [vB_val, vB_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem vB_off (n eV es : ℕ) (k : Fin (2 + es)) (hk : k.val ≠ 0) (j : Fin (1 + n + eV)) :
    vA n eV es j ≠ vB n eV es k := by
  intro h
  have hv := congrArg Fin.val h
  rw [vA_val, vB_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega

theorem vB_zero (n eV es : ℕ) : vB n eV es ⟨0, by omega⟩ = vA n eV es ⟨0, by omega⟩ := by
  apply Fin.ext; rw [vA_val, vB_val]; simp

/-- **Append one word.** -/
def VecStage.snoc {a : DecompositionAlgorithm} {n : ℕ} {outs : ℕ → Request → List Bool}
    {w : Request → List Bool} (V : VecStage a n outs) (s : WordStage a w) :
    VecStage a (n + 1) (fun j => if j = n then w else outs j) where
  extra := V.extra + s.extra
  states := _
  machine := Composition.machine (RecoveryFocus.machine (vA n V.extra s.extra) V.machine)
    (RecoveryFocus.machine (vB n V.extra s.extra) s.machine)
  cost := fun r => V.cost r + 1 + s.cost r
  coefficient := V.coefficient + 1 + s.coefficient
  degree := V.degree + s.degree
  cost_le := by
    intro r
    have h1 := V.cost_le r
    have h2 := s.cost_le r
    have p1 := pow_mono_small a r V.degree s.degree
    have p2 : (r.smallSize a) ^ s.degree ≤ (r.smallSize a) ^ (V.degree + s.degree) := by
      rw [Nat.add_comm]; exact pow_mono_small a r s.degree V.degree
    have p0 : 1 ≤ (r.smallSize a) ^ (V.degree + s.degree) := Nat.one_le_pow _ _ (one_le_small a r)
    have q1 := Nat.mul_le_mul_left V.coefficient p1
    have q2 := Nat.mul_le_mul_left s.coefficient p2
    calc V.cost r + 1 + s.cost r
        ≤ V.coefficient * (r.smallSize a) ^ (V.degree + s.degree) + (r.smallSize a) ^ (V.degree + s.degree) +
            s.coefficient * (r.smallSize a) ^ (V.degree + s.degree) := by omega
      _ = (V.coefficient + 1 + s.coefficient) * (r.smallSize a) ^ (V.degree + s.degree) := by ring
  run := by
    intro r
    set T := 1 + (n + 1) + (V.extra + s.extra)
    obtain ⟨H1, A1, hV, a0, h0, hout⟩ := V.run r
    have d1 := hV.dock (vA n V.extra s.extra) (vA_inj _ _ _) (fun _ => 0) (inBank T (Request.input a r))
      (fun _ => rfl)
      (by
        intro k
        rw [inBank_val, inBank_val]
        by_cases hk : k.val = 0
        · have hv : (vA n V.extra s.extra k).val = 0 := by rw [vA_val]; split_ifs <;> omega
          rw [if_pos hv, if_pos hk]
        · have hv : ¬ (vA n V.extra s.extra k).val = 0 := by
            rw [vA_val]; split_ifs
            · exact hk
            · exact not_false
          rw [if_neg hv, if_neg hk])
    set H1' := dockH (vA n V.extra s.extra) (fun _ => 0) H1 with hH1'
    set A1' := install (vA n V.extra s.extra) (inBank T (Request.input a r)) A1 with hA1'
    obtain ⟨H2, A2, hs, b0, g0, b1, g1⟩ := s.run r
    have d2 := hs.dock (vB n V.extra s.extra) (vB_inj _ _ _) H1' A1'
      (by
        intro k
        by_cases hk : k.val = 0
        · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [hk', vB_zero, hH1', dockH_slot _ (vA_inj _ _ _)]
          exact h0
        · rw [hH1', dockH_other _ _ _ _ (fun j => vB_off _ _ _ k hk j)])
      (by
        intro k
        by_cases hk : k.val = 0
        · have hk' : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [hk', vB_zero, hA1', install_slot _ (vA_inj _ _ _), a0]
          rfl
        · have hv : ¬ (vB n V.extra s.extra k).val = 0 := by
            rw [vB_val, if_neg hk]; split_ifs <;> first | omega | exact not_false | simp
          rw [hA1', install_other _ _ _ _ (fun j => vB_off _ _ _ k hk j), inBank_val, inBank_val,
            if_neg hv, if_neg hk])
    have hall := d1.seq d2
    have nB : ∀ i : Fin T, 1 ≤ i.val → i.val ≤ n → ∀ k, vB n V.extra s.extra k ≠ i := by
      intro i hi1 hi2 k h
      have hv := congrArg Fin.val h
      rw [vB_val] at hv
      split_ifs at hv <;> omega
    refine ⟨_, _, hall, ?_, ?_, ?_⟩
    · have e0 : (⟨0, by omega⟩ : Fin T) = vB n V.extra s.extra ⟨0, by omega⟩ := by
        apply Fin.ext; rw [vB_val]; simp
      rw [e0, install_slot _ (vB_inj _ _ _)]
      exact b0
    · have e0 : (⟨0, by omega⟩ : Fin T) = vB n V.extra s.extra ⟨0, by omega⟩ := by
        apply Fin.ext; rw [vB_val]; simp
      rw [e0, dockH_slot _ (vB_inj _ _ _)]
      exact g0
    · intro j hj
      by_cases hjn : j = n
      · subst hjn
        have e1 : (⟨j + 1, by omega⟩ : Fin T) = vB j V.extra s.extra ⟨1, by omega⟩ := by
          apply Fin.ext; rw [vB_val]; simp
        simp only [if_pos rfl]
        rw [e1, install_slot _ (vB_inj _ _ _), dockH_slot _ (vB_inj _ _ _)]
        exact ⟨b1, g1⟩
      · have hjl : j < n := by omega
        simp only [if_neg hjn]
        have e1 : (⟨j + 1, by omega⟩ : Fin T) = vA n V.extra s.extra ⟨j + 1, by omega⟩ := by
          apply Fin.ext; rw [vA_val]; simp; omega
        obtain ⟨o1, o2⟩ := hout j hjl
        refine ⟨?_, ?_⟩
        · rw [install_other _ _ _ _ (nB _ (by simp) (by simp; omega)), e1, hA1', install_slot _ (vA_inj _ _ _)]
          exact o1
        · rw [dockH_other _ _ _ _ (nB _ (by simp) (by simp; omega)), e1, hH1', dockH_slot _ (vA_inj _ _ _)]
          exact o2

end
end NearCubicWires.PacketsGlue.RequestMeta

