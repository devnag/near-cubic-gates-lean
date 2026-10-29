import SourceAdapters.Refuter.ClockPrep
import SourceAdapters.Joins.CappedRun
import Proof.Gates.Succinct.Verifier

/-!
# The body under the clock (input 7, the clock, part 3: dock of the join `CappedRun`)

proof of `lem:multitape-refuter`, Step 1: "It accepts exactly when the first simulation and, when required, the second simulation
accept. … The clock rejects every branch whose steps after clock preparation exceed `(c_0+2)(T(N)+1)` …
Hence every branch halts within `O(T(N)+1)` steps on every input". The verdict is a control state: `bodyFull`
runs the body and then a three-state machine that reads the flag `ALL` and halts in control `1` (accept) or
`2`. The capped machine of the join `CappedMachineRun` (`Joins/CappedRun.lean`, sha 4d5fdf4c…) runs
`bodyFull` on its cold tapes with the clock tape `1^{cap}`; its final control is `bodyFull`'s on success and the
extra failure control otherwise (`CappedResultAgreement`).

`bodyFull_run`: on a genuine record the raw run of `bodyFull` from its cold tapes halts after `c + 2` steps,
`c` the body's cost, in control `body.size + 1` iff `ALL ≠ 0` (iff `BodyCond`).
-/

namespace NearCubicGates.Adapters.Refuter.Clock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Refuter.Mach
open NearCubicGates.Close.CheckedPCPP (coldBank ConfRel runFrom_rel coldBank_s coldBank_c coldBank_r)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_val cTape_val rTape_val wenc_A_c)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## A cold run that keeps every read -/

theorem runFrom_halted {t s : ℕ} (m : Machine t s) : ∀ (n : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s),
    runFrom m n c = some r → m.halted r.final.control = true := by
  intro n
  induction n with
  | zero =>
    intro c r h; simp only [runFrom] at h; split at h
    · next hh => cases h; exact hh
    · contradiction
  | succ n ih =>
    intro c r h; simp only [runFrom] at h; split at h
    · next hh => cases h; exact hh
    · cases hs : step m c with
      | none => simp [hs] at h
      | some d =>
        cases ht : runFrom m n d with
        | none => simp [hs, ht] at h
        | some tail => simp only [hs, ht, Option.some.injEq] at h; subst h; exact ih d tail ht

/-- `cold_run` (`Proof/Gates/Succinct/Verifier.lean`) with the reads of every tape and the control kept. -/
theorem cold_run' {ns nr cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hcell : σ.cell = false) :
    ∃ r, runFrom P.compile n (initialConfiguration P.compile (coldBank σ)) = some r ∧
      r.final.heads = (wenc cap τ).H ∧ (∀ i, r.final.tapes (sTape i) = τ.st i) ∧
      (∀ j, RdEq (r.final.tapes j) ((wenc cap τ).A j)) ∧ P.compile.halted r.final.control = true := by
  obtain ⟨r, hr, hh, ht, _⟩ := WXExec.run cap h hsh hval
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile (coldBank σ)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.wenc_A_s, coldBank_s]; exact RdEq.refl _
      · rw [wenc_A_c, coldBank_c, hcell]; exact rdEq_blank _ (by simp)
      · rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.wenc_A_r, coldBank_r, hval q, regTape_zero]
        exact rdEq_blank _ (by simp)
    · rintro j ⟨i, rfl⟩
      simp only [initialConfiguration]
      rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.wenc_A_s, coldBank_s]
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel P.compile E n hrel r hr
  have hhalt : P.compile.halted r.final.control = true := by
    have := runFrom_halted P.compile n _ r hr
    exact this
  refine ⟨r', hr', by rw [← hrel'.heads, hh], fun i => ?_, fun j => ?_, by rw [← hrel'.control]; exact hhalt⟩
  · rw [← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, NearCubicWires.WireExponent3_5.FinalPass.Tm.wenc_A_s]
  · rw [← ht]; exact fun p => (hrel'.read j p).symm

/-! ## The verdict as a control state -/

/-- Read one bit; halt in control `1` if it is set, else in control `2`. -/
def verdictM : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (q.val ≠ 0)
  rule := fun q b => if q.val = 0 then some ⟨if b 0 then 1 else 2, fun _ => none, fun _ => .stay⟩ else none

theorem verdict_run (h : Fin 1 → ℕ) (t : Fin 1 → List Bool) :
    ∃ r, runFrom verdictM 1 ⟨verdictM.start, h, t⟩ = some r ∧
      r.final.control = (if readTapeBit (t 0) (h 0) then 1 else 2) ∧ r.final.heads = h ∧ r.final.tapes = t := by
  cases hb : readTapeBit (t 0) (h 0)
  · refine ⟨⟨⟨2, h, t⟩, 1, max (Configuration.tapeCells (⟨verdictM.start, h, t⟩ : Configuration 1 3))
      (Configuration.tapeCells (⟨2, h, t⟩ : Configuration 1 3))⟩, ?_, rfl, rfl, rfl⟩
    have hst : step verdictM ⟨verdictM.start, h, t⟩ = some ⟨2, h, t⟩ := by
      simp only [step, verdictM, Configuration.scanned]
      simp [hb, applyAction, HeadMove.apply]
    exact runFrom_step (fuel := 0) verdictM _ _ ⟨⟨2, h, t⟩, 0, _⟩ rfl hst rfl
  · refine ⟨⟨⟨1, h, t⟩, 1, max (Configuration.tapeCells (⟨verdictM.start, h, t⟩ : Configuration 1 3))
      (Configuration.tapeCells (⟨1, h, t⟩ : Configuration 1 3))⟩, ?_, rfl, rfl, rfl⟩
    have hst : step verdictM ⟨verdictM.start, h, t⟩ = some ⟨1, h, t⟩ := by
      simp only [step, verdictM, Configuration.scanned]
      simp [hb, applyAction, HeadMove.apply]
    exact runFrom_step (fuel := 0) verdictM _ _ ⟨⟨1, h, t⟩, 0, _⟩ rfl hst rfl

/-- The verdict reads the register `ALL`. -/
def vslot : Fin 1 → Fin (NS + 2 + NR) := fun _ => rTape rALL

theorem vslot_inj : Function.Injective vslot := fun a b _ => Subsingleton.elim a b

/-- The body followed by the verdict. -/
noncomputable def bodyFull : Machine (NS + 2 + NR) (body.size + 3) :=
  Composition.machine body.compile (RecoveryFocus.machine vslot verdictM)

theorem config_self {t u s : ℕ} (slot : Fin t → Fin u) (q : Fin s) (H : Fin u → ℕ) (T : Fin u → List Bool) :
    RecoveryFocus.config slot H T (⟨q, fun j => H (slot j), fun j => T (slot j)⟩ : Configuration t s) = ⟨q, H, T⟩ := by
  apply configuration_ext
  · rfl
  · funext i; simp only [RecoveryFocus.config]
    cases hp : RecoveryFocus.pick slot i with
    | none => rfl
    | some j => simp only; rw [RecoveryFocus.slot_of_pick slot hp]
  · funext i; simp only [RecoveryFocus.config]
    cases hp : RecoveryFocus.pick slot i with
    | none => rfl
    | some j => simp only; rw [RecoveryFocus.slot_of_pick slot hp]

/-- **The body's verdict** (proof of `lem:multitape-refuter`): the raw run of `bodyFull` from the body's cold tapes. -/
theorem bodyFull_run {capB : ℕ} (x w : List Bool) (τ : St) (n : ℕ) (h : WXExec capB body (coldSt x w) τ n) :
    ∃ rB, runFrom bodyFull (n + 1 + 1) (initialConfiguration bodyFull (coldBank (coldSt x w))) = some rB ∧
      rB.final.control.val = body.size + (if τ.val rALL ≠ 0 then 1 else 2) := by
  obtain ⟨r1, hr1, hh1, _, hrd1, _⟩ := cold_run' h (fun _ => rfl) (fun _ => rfl) rfl
  obtain ⟨rV, hrV, hcV, hhV, htV⟩ := verdict_run (fun _ => r1.final.heads (vslot 0)) (fun _ => r1.final.tapes (vslot 0))
  obtain ⟨res, hres, hresf, _⟩ := RecoveryFocus.run_config vslot vslot_inj verdictM r1.final.heads r1.final.tapes 1
    ⟨verdictM.start, fun j => r1.final.heads (vslot j), fun j => r1.final.tapes (vslot j)⟩ rV (by
      have : (fun j : Fin 1 => r1.final.heads (vslot j)) = fun _ => r1.final.heads (vslot 0) := by
        funext j; rw [Subsingleton.elim j 0]
      have h2 : (fun j : Fin 1 => r1.final.tapes (vslot j)) = fun _ => r1.final.tapes (vslot 0) := by
        funext j; rw [Subsingleton.elim j 0]
      rw [this, h2]; exact hrV)
  rw [config_self] at hres
  have hrestart : Composition.restart r1.final (RecoveryFocus.machine vslot verdictM).start =
      (⟨verdictM.start, r1.final.heads, r1.final.tapes⟩ : Configuration (NS + 2 + NR) 3) := rfl
  rw [← hrestart] at hres
  have hjoin := Composition.run_join body.compile (RecoveryFocus.machine vslot verdictM) n 1 _ r1 res hr1 hres
  refine ⟨_, hjoin, ?_⟩
  have hc : (Composition.joinedReceipt r1 res).final.control.val = body.size + res.final.control.val := by
    simp [Composition.joinedReceipt, Composition.rightConfig]
  rw [hc, hresf]
  simp only [RecoveryFocus.config]
  rw [hcV]
  have hbit : readTapeBit (r1.final.tapes (vslot 0)) (r1.final.heads (vslot 0)) = decide (τ.val rALL ≠ 0) := by
    rw [hrd1, hh1]
    simp [vslot, regTape_read]
  rw [hbit]
  by_cases ha : τ.val rALL ≠ 0 <;> simp [ha]

end NearCubicGates.Adapters.Refuter.Clock
