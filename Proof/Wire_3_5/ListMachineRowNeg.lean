import Proof.Wire_3_5.ListMachineRowPopRow

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun)
open NearCubicWires.WireExponent3_5.ListMachine.Print

/-! ## The XOR of a cell with a flag -/

namespace XorCell
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

/-- Tape 0 the result cell (rewritten), tape 1 the flag cell. -/
def machine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc => if q.val = 0 then some (act 1 (some (xor (sc 0) (sc 1))) none .stay .stay) else none

theorem run0 (r f : Bool) : Step machine 1 ![0, 0] ![[r], [f]] ![0, 0] ![[xor r f], [f]] := by
  have s := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 0 1 [r] [f] 0 0 (some (xor r f)) none .stay .stay
    (by simp [machine, readTapeBit])
  simp only [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply] at s
  obtain ⟨res, hr, hf, _⟩ := (Timed.single (p := machine) rfl s).run rfl
  refine ⟨res, hr, ?_, ?_, by omega⟩
  · rw [hf]; rfl
  · rw [hf]; funext i; fin_cases i <;> rfl

theorem run (r f : Bool) : Step machine 1 (fun _ => 0) ![[r], [f]] (fun _ => 0) ![[xor r f], [f]] :=
  ((run0 r f).congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl

end XorCell

/-! ## The negation family -/

/-- The flag's slots: the result cell and the last tape. -/
def sXor (t : ℕ) : Fin 2 → Fin (2 + t + 1) := ![Fin.castAdd 1 (Fin.castAdd t 1), Fin.natAdd (2 + t) 0]

theorem sXor_inj (t : ℕ) : Function.Injective (sXor t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [sXor] at this; omega)

/-- **The negation family**: evaluate, then XOR the result with the flag data cell. -/
noncomputable def negFam (F : EvalFam) : EvalFam where
  t := F.t + 1
  s := F.s + 2
  machine := Composition.machine (RecoveryFocus.machine (Fin.castAdd 1) F.machine)
    (RecoveryFocus.machine (sXor F.t) XorCell.machine)

theorem addCases_assoc {α : Type} {t : ℕ} (a : Fin 2 → α) (d : Fin t → α) (x : α) :
    (Fin.addCases (m := 2) (n := t + 1) a (Fin.addCases (m := t) (n := 1) d (fun _ => x)) : Fin (2 + (t + 1)) → α) =
      (Fin.addCases (m := 2 + t) (n := 1) (Fin.addCases a d) (fun _ => x) : Fin (2 + t + 1) → α) := by
  funext i
  refine Fin.addCases (fun a' => ?_) (fun b' => ?_) i
  · rw [Fin.addCases_left]
    have e : (Fin.castAdd (t + 1) a' : Fin (2 + (t + 1))) = (Fin.castAdd 1 (Fin.castAdd t a') : Fin (2 + t + 1)) :=
      Fin.ext rfl
    rw [e, Fin.addCases_left, Fin.addCases_left]
  · rw [Fin.addCases_right]
    refine Fin.addCases (fun c => ?_) (fun c => ?_) b'
    · have e : (Fin.natAdd 2 (Fin.castAdd 1 c) : Fin (2 + (t + 1))) = (Fin.castAdd 1 (Fin.natAdd 2 c) : Fin (2 + t + 1)) :=
        Fin.ext rfl
      rw [e, Fin.addCases_left, Fin.addCases_left, Fin.addCases_right]
    · have e : (Fin.natAdd 2 (Fin.natAdd t c) : Fin (2 + (t + 1))) = (Fin.natAdd (2 + t) c : Fin (2 + t + 1)) :=
        Fin.ext (by simp)
      rw [e, Fin.addCases_right, Fin.addCases_right]

/-- **The complement of a member** (or the member itself, `neg = false`) is a member of the negation family. -/
noncomputable def negMember (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (neg : Bool) :
    Member (negFam F) L (fun Z => xor (f Z) neg) where
  data := Fin.addCases (m := F.t) (n := 1) m.data (fun _ => [neg])
  cost := m.cost + 1 + 1
  step := by
    intro Z b hZ
    have h1 := liftC (m.step Z b hZ) (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [neg])
    have h2 := Block.dockKeep (XorCell.run (f Z) neg) (sXor F.t) (sXor_inj F.t) (fun _ => 0)
      (Fin.addCases (Fin.addCases ![frame Z, [f Z]] m.data) (fun _ : Fin 1 => [neg]))
      (fun _ => rfl) (by intro j; fin_cases j <;> simp [sXor])
    have e1 : (Fin.addCases (m := 2 + F.t) (n := 1) (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (2 + F.t + 1) → ℕ) =
        fun _ => 0 := by funext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
    rw [e1] at h1
    have h := h1.seq h2
    have e2 : install (sXor F.t) (Fin.addCases (Fin.addCases ![frame Z, [f Z]] m.data) (fun _ : Fin 1 => [neg]))
        ![[xor (f Z) neg], [neg]] =
        Fin.addCases (Fin.addCases ![frame Z, [xor (f Z) neg]] m.data) (fun _ : Fin 1 => [neg]) := by
      apply install_eq_of _ (sXor_inj F.t)
      · intro j; fin_cases j <;> simp [sXor]
      · intro i hi
        revert hi
        refine Fin.addCases (fun a => ?_) (fun a => ?_) i
        · refine Fin.addCases (fun c => ?_) (fun c => ?_) a
          · intro hi
            have hc : c ≠ 1 := fun e => hi 0 (by rw [e]; rfl)
            fin_cases c
            · simp
            · exact absurd rfl hc
          · intro _; simp
        · intro hi
          exact absurd (by rw [Fin.eq_zero a]; rfl) (hi 1)
    rw [e2, ← addCases_assoc, ← addCases_assoc] at h
    exact h

end NearCubicWires.WireExponent3_5.ListMachine.Row
