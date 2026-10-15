import Proof.Circuits.PolynomialClockPositive
import Proof.Circuits.PolynomialClockBounds

/-! A physical first-marker branch handles zero without entering the positive
canonicalizer. Every branch returns through the same finite controller. -/
namespace NearCubicWires.RepairOrdinary.PolynomialClock
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def marker (k : ℕ) : Machine (tapes k) 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
def statesOf {t s : ℕ} (_ : Machine t s) := s
noncomputable def positiveStates (k : ℕ) := statesOf (positive k)
noncomputable abbrev sizes (k : ℕ) : Fin 2 → ℕ := ![1,positiveStates k]
noncomputable def programs (k : ℕ) : (j : Fin 2) → Machine (tapes k) (sizes k j)
  | ⟨0,_⟩ => marker k
  | ⟨1,_⟩ => positive k
  | ⟨n+2,h⟩ => False.elim (by omega)
def inputTape (k : ℕ) := old k (HierarchyFromInput.field (k+2) 2)
noncomputable def next (k : ℕ) (j : Fin 2) (_ : Fin (sizes k j))
    (bits : Fin (tapes k) → Bool) : Option (Fin 2) :=
  if j.val=0 ∧ bits (inputTape k)=true then some 1 else none
noncomputable def machine (k : ℕ) := RecoveryCalls.machine (sizes k) (programs k) 0 (next k)
def budget (k n : ℕ) := positiveBudget k n+2

theorem input_marker (k n : ℕ) :
    (initialConfiguration (marker k) (input k n)).scanned (inputTape k)=decide (0<n) := by
  change readTapeBit (frame (List.replicate n true)) 0=decide (0<n)
  cases n <;> rfl

theorem selected_run (k n : ℕ) (hn : 0<n) : ∃ out,
    ClockJoin.ReadyRun (machine k) (budget k n) (input k n) out ∧
      out (outputTape k)=(n^(k+2)).bits := by
  obtain ⟨out,hready,hout⟩ := positive_run k n hn
  obtain ⟨body,hb,ht,hh,hs⟩ := hready
  have hstart := RecoveryCalls.return_step (sizes k) (programs k) 0 (next k)
    0 1 (initialConfiguration (marker k) (input k n)) (by rfl) (by
      change (if (0:ℕ)=0 ∧ readTapeBit (frame (List.replicate n true)) 0=true then some (1 : Fin 2) else none)=some 1
      have hm := input_marker k n
      change readTapeBit (frame (List.replicate n true)) 0=decide (0<n) at hm
      rw [hm]; simp [hn])
  obtain ⟨hp,hhalt⟩ := prefix_of_run (positive k) (positiveBudget k n) _ body hb
  have hrun := RecoveryCalls.body_timed (sizes k) (programs k) 0 (next k) 1 ⟨body.peakTapeCells,hp⟩
  have hend := RecoveryCalls.stop_step (sizes k) (programs k) 0 (next k) 1 body.final hhalt (by simp [next])
  have hfirst := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hstart
  have hlast := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hend
  have hjoined := (hfirst.trans hrun).trans hlast
  obtain ⟨r,hr,hf,hsteps⟩ := hjoined.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have htime : 1+body.steps+1 ≤ budget k n := by dsimp [budget]; omega
  have hm := runFrom_moreFuel (machine k) (1+body.steps+1) (budget k n-(1+body.steps+1)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨out,⟨r,hm,?_,?_,hsteps.le.trans htime⟩,hout⟩
  · rw [hf]; exact ht
  · rw [hf]; exact hh

theorem zero_run (k : ℕ) : ClockJoin.ReadyRun (machine k) 1 (input k 0) (input k 0) := by
  have hs := RecoveryCalls.stop_step (sizes k) (programs k) 0 (next k) 0
    (initialConfiguration (marker k) (input k 0)) (by rfl) (by rfl)
  have ht := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hs
  obtain ⟨r,hr,hf,hsteps⟩ := ht.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by rw [hf]; rfl,by intro i; rw [hf]; rfl,hsteps.le⟩

theorem total_run (k n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine k) (budget k n) (input k n) out ∧
      out (outputTape k)=(n^(k+2)).bits := by
  cases n with
  | zero =>
    have hb : 1 ≤ budget k 0 := by dsimp [budget]; omega
    refine ⟨input k 0,ClockJoin.enlarge _ _ _ _ _ (zero_run k) hb,?_⟩
    simp [input,outputTape,fresh]
  | succ n => exact selected_run k (n+1) (by omega)

theorem sharp_bound (k n : ℕ) : budget k n ≤
    PolynomialClockPower.finalCoefficient (k+2)*(n+1)*(PCPResourceLedger.ell n+1)^2 := by
  have h := PolynomialClockPower.final_budget_bound (k+2) (List.replicate n true)
  simp only [List.length_replicate] at h
  unfold budget positiveBudget
  omega

end NearCubicWires.RepairOrdinary.PolynomialClock
