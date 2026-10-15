import Proof.MachineModel.OrdinaryWilliamsPowerLayout

/-! The fixed finite power-call graph consumes each previous physical
product as the next operand. Its clock includes every return transition. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPower
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (D : ℕ) : Fin D → ℕ := fun _ => 7
noncomputable def programs (D : ℕ) (j : Fin D) : Machine (tapes D) (sizes D j) := program D j
def next (D : ℕ) (j : Fin D) (_ : Fin (sizes D j)) (_ : Fin (tapes D) → Bool) : Option (Fin D) :=
  if h : j.val+1<D then some ⟨j.val+1,h⟩ else none
noncomputable def machine (D : ℕ) (hD : 0<D) :=
  RecoveryCalls.machine (sizes D) (programs D) ⟨0,hD⟩ (next D)
noncomputable def atNode (D : ℕ) (j : Fin D) (ambient : Fin (tapes D) → List Bool) :=
  controlConfig (RecoveryCalls.code (sizes D) j) (initialConfiguration (programs D j) ambient)
def outputTape (D : ℕ) (hD : 0<D) : Fin (tapes D) := block D ⟨D-1,by omega⟩ 0
def Fields (D c : ℕ) (hD : 0<D) (ambient : Fin (tapes D) → List Bool) : Prop :=
  ambient (factor D)=UnaryTemplate.tape c ∧ ambient (outputTape D hD)=List.replicate (c^D) true

theorem power_prefix (D c : ℕ) (hD : 0<D) (hc : 1≤c) (remaining : ℕ) (j : Fin D)
    (hj : j.val+remaining=D) (ambient : Fin (tapes D) → List Bool) (hin : Input D c j ambient) :
    ∃ count out, count≤remaining*(stepBudget D c+1) ∧ Fields D c hD out ∧
      Timed (machine D hD) count (atNode D j ambient)
        (RecoveryCalls.stopped (sizes D) (fun _ => 0) out) := by
  induction remaining generalizing j ambient with
  | zero => omega
  | succ remaining ih =>
    obtain ⟨r,hr,hout,hfactor,hfuture,hh,hs⟩ := step_run D c j hc ambient hin
    obtain ⟨hp,hhalt⟩ := prefix_of_run (program D j) (stepBudget D c) _ r hr
    have hb := RecoveryCalls.body_timed (sizes D) (programs D) ⟨0,hD⟩ (next D) j ⟨r.peakTapeCells,hp⟩
    cases remaining with
    | zero =>
      have hjlast : j.val+1=D := by omega
      have he := RecoveryCalls.stop_step (sizes D) (programs D) ⟨0,hD⟩ (next D) j r.final hhalt
        (by simp [next]; omega)
      have hheads := funext hh
      rw [hheads] at he
      have hfinal := hb.trans (Timed.single
        (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
      have hslot : outputTape D hD=slot D j 2 := by
        apply Fin.ext
        simp [outputTape,slot,block]
        omega
      refine ⟨r.steps+1,r.final.tapes,by omega,?_,hfinal⟩
      exact ⟨hfactor,by rw [hslot,hout,hjlast]⟩
    | succ remaining =>
      have hjnext : j.val+1<D := by omega
      let jnext : Fin D := ⟨j.val+1,hjnext⟩
      have hoperand : operand D jnext=slot D j 2 := by
        apply Fin.ext
        simp [operand,jnext,previous,slot,block]
      have hnext : Input D c jnext r.final.tapes := by
        refine ⟨hfactor,?_,?_⟩
        · rw [hoperand]
          exact hout
        · exact hfuture
      obtain ⟨count,out,hcount,hfields,hpath⟩ := ih jnext (by dsimp [jnext]; omega) r.final.tapes hnext
      have he := RecoveryCalls.return_step (sizes D) (programs D) ⟨0,hD⟩ (next D) j jnext r.final hhalt
        (by simp [next,hjnext,jnext])
      have hrestart : RecoveryCalls.restarted (programs D jnext) r.final.heads r.final.tapes=
          initialConfiguration (programs D jnext) r.final.tapes := by
        apply configuration_ext
        · rfl
        · exact funext hh
        · rfl
      rw [hrestart] at he
      have hcall := hb.trans (Timed.single
        (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
      refine ⟨r.steps+1+count,out,?_,hfields,hcall.trans hpath⟩
      nlinarith

def budget (D c : ℕ) := D*(stepBudget D c+1)

theorem power_run (D c : ℕ) (hD : 0<D) (hc : 1≤c) (ambient : Fin (tapes D) → List Bool)
    (hin : Input D c ⟨0,hD⟩ ambient) :
    ∃ r : ExecutionReceipt (tapes D) (Fintype.card (RecoveryCalls.Control (sizes D))),
      run (machine D hD) (budget D c) ambient=some r ∧ Fields D c hD r.final.tapes ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤budget D c := by
  obtain ⟨count,out,hcount,hout,hp⟩ := power_prefix D c hD hc D ⟨0,hD⟩ (by simp) ambient hin
  obtain ⟨r,hr,hf,hs⟩ := hp.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel (machine D hD) count (budget D c-count) _ r hr
  change count≤budget D c at hcount
  rw [Nat.add_sub_of_le hcount] at hm
  refine ⟨r,hm,?_,?_,hs.le.trans hcount⟩
  · rw [hf]
    exact hout
  · intro i
    rw [hf]
    rfl

end NearCubicWires.RepairOrdinary.WilliamsPower
