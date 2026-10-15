import Proof.CaseAnalysis.WitnessSupportLiftHandoff
import Proof.MachineModel.UAcceptanceCarrier

/-! One ordinary weak-machine wrapper for the actual all-input worker.
The worker receipt remains a mandatory supplier until the row run is closed.
The existing physical acceptance gate costs two steps and rules out alternate
fuel acceptance by determinism. No second worker execution is introduced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Weak
open LocalBitMultitape SourceInterfaces RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {t s : ℕ} (p : Machine t s) (ht : 2≤t) (result : Fin t)
variable (fuel : ℕ→ℕ) (meaning : (n : ℕ)→BitInput n→List Bool→Prop)

def AllInputRun : Prop :=
  ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),∃ actual,
    run p (fuel n) ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits)=some actual ∧
      (actual.final.scanned result=true ↔ meaning n x bits)

def machine (supplier : AllInputRun p ht result fuel meaning) : OrdinaryWeakMachine where
  verifier:=UAcceptanceCarrier.verifier p ht result
  runtime:=fun n=>fuel n+2
  halts:=by
    intro n x w
    obtain ⟨actual,hr,_meaning⟩:=supplier n x (List.ofFn w)
    exact ⟨UAcceptanceCarrier.receipt result actual,
      (UAcceptanceCarrier.verifier_run p ht result (fuel n) (List.ofFn x) (List.ofFn w) actual hr).1⟩

theorem runtime_eq (supplier : AllInputRun p ht result fuel meaning) (n : ℕ) :
    (machine p ht result fuel meaning supplier).runtime n=fuel n+2:=rfl

theorem decision_exact (supplier : AllInputRun p ht result fuel meaning)
    (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (machine p ht result fuel meaning supplier).verifier.accepts (List.ofFn x) bits ↔ meaning n x bits := by
  obtain ⟨actual,hr,hm⟩:=supplier n x bits
  exact (UAcceptanceCarrier.accepts_transfer p ht result (fuel n) (List.ofFn x) bits actual hr).trans hm

theorem accepts_exact (supplier : AllInputRun p ht result fuel meaning) (n : ℕ) (x : BitInput n) :
    (machine p ht result fuel meaning supplier).accepts n x ↔
      ∃ w : BitInput (n/16),meaning n x (List.ofFn w) := by
  apply exists_congr
  intro w
  exact decision_exact p ht result fuel meaning supplier n x (List.ofFn w)

theorem one_sided (supplier : AllInputRun p ht result fuel meaning)
    (language : (n : ℕ)→BitInput n→Prop)
    (soundness : ∀ n x bits,meaning n x bits→language n x) :
    ∀ n x,(machine p ht result fuel meaning supplier).accepts n x→language n x := by
  intro n x accepted
  obtain ⟨w,hw⟩:=(accepts_exact p ht result fuel meaning supplier n x).mp accepted
  exact soundness n x (List.ofFn w) hw

theorem dyadic_complete (supplier : AllInputRun p ht result fuel meaning)
    (property : (s : ℕ)→BitInput (2^s)→Prop) (onset : ℕ)
    (complete : ∀ s,onset ≤ s→∀ x,property s x→
      ∃ w : BitInput (2^s/16),meaning (2^s) x (List.ofFn w)) :
    ∀ s,onset ≤ s→∀ x,property s x→(machine p ht result fuel meaning supplier).accepts (2^s) x := by
  intro s hs x hx
  exact (accepts_exact p ht result fuel meaning supplier (2^s) x).mpr (complete s hs x hx)

end NearCubicWires.RepairOrdinary.CloseoutWitness.Weak
