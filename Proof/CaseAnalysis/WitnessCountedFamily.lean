import Proof.CaseAnalysis.WitnessTermLoopMeaning

/-! The existing rejecting repeater is packaged with symbolic control
size. This avoids expanding a nested circuit/sum controller merely to
state its physical result; no machine or instruction is added. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CountedFamily
open LocalBitMultitape
open RepairSource.VerifierDecoding
open private iterate_invariant from Proof.CaseAnalysis.WitnessTermLoopDriver
open private result_bits from Proof.CaseAnalysis.WitnessTermLoopMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def Run {α : Type} {t s : ℕ} (body : Machine t s) (source : ℕ → α → Configuration t s)
    (Inv : ℕ → α → Prop) (cost total : ℕ) (bit : Fin t) (initial : α) (flag : Bool) : Prop :=
  ∃ r,runFrom (RepeatMachine.machine body (fun _ bits=>bits bit)) (total*(cost+3)+3)
    (RepeatMachine.cfg 0 (source 0 initial) total 1)=some r ∧ r.steps ≤ total*(cost+3)+3 ∧
    r.final.heads (bit.castAdd 1)=0 ∧ r.final.tapes (bit.castAdd 1)=[flag] ∧
    (flag=true → ∃ after,r.final=RepeatMachine.cfg 3 (source total after) total 1 ∧ Inv total after)

theorem complete_run {α : Type} {t s : ℕ} (body : Machine t s) (source : ℕ → α → Configuration t s)
    (next : ℕ → α → Bool×α) (Inv : ℕ → α → Prop) (cost total : ℕ) (bit : Fin t)
    (flags : ℕ → Bool) (hflags : ∀ j x,(next j x).1=flags j)
    (hstart : ∀ j<total,∀ x,Inv j x → (source j x).control=body.start)
    (supplier : ∀ j<total,∀ x,Inv j x → ∃ r,runFrom body cost (source j x)=some r ∧ r.steps ≤ cost ∧
      r.final.scanned bit=(next j x).1 ∧
      ((next j x).1=true → r.final.heads=(source (j+1) (next j x).2).heads ∧
        r.final.tapes=(source (j+1) (next j x).2).tapes ∧ Inv (j+1) (next j x).2) ∧
      ((next j x).1=false → r.final.heads bit=0 ∧ r.final.tapes bit=[false]))
    (htrue : ∀ j x,(source j x).heads bit=0 ∧ (source j x).tapes bit=[true])
    (initial : α) (hinitial : Inv 0 initial) :
    Run body source Inv cost total bit initial ((List.range' 0 total).all flags) := by
  obtain ⟨r,run,rs,result,reject⟩:=CountedReject.counted_run body (fun _ bits=>bits bit)
    source next Inv cost total bit hstart supplier initial hinitial
  let output:=RepeatMachine.iterate (CountedReject.advance next) total (0,initial)
  have flag:output.1=(List.range' 0 total).all flags:=TermLoop.iterate_flag next flags hflags total 0 initial
  obtain ⟨fh,ft⟩:=result_bits (fun x=>source x.1 x.2) total output r.final bit result
    (by intro x;exact htrue x.1 x.2) reject
  rw [flag] at ft
  refine ⟨r,run,rs,fh,ft,?_⟩
  intro accepted
  have hp:output.1=true:=flag.trans accepted
  have indexInv:=iterate_invariant next Inv total (by
    intro j hj x hx hg
    obtain ⟨r,_run,_rs,_flag,good,_bad⟩:=supplier j hj x hx
    exact (good hg).2.2) total 0 initial hinitial (by omega) hp
  have index:output.2.1=total:=by simpa only [Nat.zero_add] using indexInv.1
  have he:=result
  change RepeatMachine.Result (fun x=>source x.1 x.2) total output r.final at he
  simp only [RepeatMachine.Result,hp,↓reduceIte] at he
  rw [index] at he
  exact ⟨output.2.2,he,by simpa only [Nat.zero_add] using indexInv.2⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.CountedFamily
