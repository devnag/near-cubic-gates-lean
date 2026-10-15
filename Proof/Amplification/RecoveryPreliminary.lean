import Proof.Amplification.RecoveryWitnessCopy

/-! The actual verifier's two-input entry. Original code and witness occupy
tapes0/1; every other tape is initially blank. The complete scalar header
and counted witness copy execute on fixed disjoint banks. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdPreliminary
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits word : List Bool) (i : Fin 26) : List Bool :=
  if i.val=0 then frame bits else if i.val=1 then frame word else []
def headerSlots (j : Fin 22) : Fin 26 :=
  if j.val=0 then 0 else ⟨j.val+1,by omega⟩
def witnessSlots : Fin 4→Fin 26 := ![1,23,24,25]
theorem headerSlots_injective : Function.Injective headerSlots := by decide

theorem witnessSlots_injective : Function.Injective witnessSlots := by decide
noncomputable def headerMachine := RecoveryFocus.machine headerSlots RecoveryColdHeaderCap.machine
noncomputable def witnessMachine := RecoveryFocus.machine witnessSlots RecoveryColdWitnessCopy.machine
noncomputable def machine := Composition.machine headerMachine witnessMachine
noncomputable def middle (bits word : List Bool) (cap scratch : Nat) :=
  install headerSlots (input bits word) (RecoveryColdHeaderCap.output bits cap scratch)
noncomputable def output (bits word : List Bool) (cap scratch : Nat) :=
  install witnessSlots (middle bits word cap scratch) (RecoveryColdWitnessCopy.output word)
def budget (bits word : List Bool) := RecoveryColdHeaderCap.budget bits+1+(8*word.length+14)

private theorem ready_of_run {t s fuel : Nat} {p : Machine t s} {a b : Fin t→List Bool}
    (r : ExecutionReceipt t s) (hr : run p fuel a=some r)
    (hh : r.final.heads=(fun _=>0)) (ht : r.final.tapes=b) : ReadyRun p r.steps a b := by
  obtain ⟨hp,hhalt⟩ := prefix_of_run p fuel (initialConfiguration p a) r hr
  have timed : Timed p r.steps (initialConfiguration p a) r.final := ⟨r.peakTapeCells,hp⟩
  obtain ⟨out,hout,hfinal,hsteps⟩ := timed.run hhalt
  exact ⟨out,hout,by rw [hfinal]; exact ht,fun i=>by rw [hfinal,hh],hsteps⟩

theorem header_ready (bits word : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ n≤RecoveryColdHeaderCap.budget bits,ReadyRun headerMachine n (input bits word) (middle bits word cap scratch) := by
  obtain ⟨cap,scratch,hcap,hscratch,r,hr,hh,ht,hn⟩ := RecoveryColdHeaderCap.prepare_run bits
  have h := ready_of_run r hr hh ht
  refine ⟨cap,scratch,hcap,hscratch,r.steps,hn,?_⟩
  exact h.focus headerSlots headerSlots_injective (input bits word) (by intro j; fin_cases j <;> rfl)

theorem witness_ready (bits word : List Bool) (cap scratch : Nat) :
    ReadyRun witnessMachine (8*word.length+14) (middle bits word cap scratch) (output bits word cap scratch) := by
  apply (RecoveryColdWitnessCopy.copy_ready word).focus witnessSlots witnessSlots_injective
  intro j
  fin_cases j
  all_goals exact install_other headerSlots _ _ _ (by intro k; fin_cases k <;> decide)

theorem preliminary_run (bits word : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run machine (budget bits word) (input bits word)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=output bits word cap scratch ∧ r.steps≤budget bits word := by
  obtain ⟨cap,scratch,hcap,hscratch,n,hn,first,hfirst,hft,hfh,_⟩ := header_ready bits word
  obtain ⟨last,hlast,hlt,hlh,_⟩ := witness_ready bits word cap scratch
  have hi : Composition.restart first.final witnessMachine.start=
      initialConfiguration witnessMachine (middle bits word cap scratch) := by
    apply configuration_ext
    · rfl
    · exact funext hfh
    · exact hft
  unfold run at hlast
  rw [←hi] at hlast
  have h := Composition.run_join headerMachine witnessMachine n (8*word.length+14)
    _ first last hfirst hlast
  let r := Composition.joinedReceipt first last
  have hr : run machine (n+1+(8*word.length+14)) (input bits word)=some r := h
  have hle : n+1+(8*word.length+14)≤budget bits word := by unfold budget; omega
  have hm := run_moreFuel machine (n+1+(8*word.length+14)) (budget bits word-(n+1+(8*word.length+14))) _ r hr
  rw [Nat.add_sub_of_le hle] at hm
  exact ⟨cap,scratch,hcap,hscratch,r,hm,funext hlh,hlt,runFrom_steps_le machine (budget bits word) _ r hm⟩

end NearCubicWires.RepairOrdinary.RecoveryColdPreliminary
