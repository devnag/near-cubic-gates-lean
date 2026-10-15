import Proof.PCP.PCPTraversalPairResult

namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def testNext (n : ℕ) : Fin 39 := if n=0 then 1 else if n=1 then 2 else 14

theorem test_path (n countCap : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : ambient 79=ZeroPadding.pad countCap (List.replicate n true)) (hh : heads 79=0) :
    Path 0 (testNext n) (PCPControlOps.testCost n+1) heads ambient heads ambient := by
  obtain ⟨base,hr,hf,_⟩ := PCPControlOps.test_run n countCap
  obtain ⟨r,hrun,hq,hrh,hrt,_⟩ := focused_run_at PCPControlOps.testMachine ![79]
    (by decide) heads ambient _ base hr rfl
    (by intro i; fin_cases i; exact hh) (by intro i; fin_cases i; exact hc)
  rw [hf] at hq hrh hrt
  change r.final.control=PCPControlOps.testCode n at hq
  have hheads : installedHeads ![79] heads (fun _ : Fin 1 => 0)=heads :=
    installedHeads_existing ![79] heads _ (by intro i; fin_cases i; exact hh)
  have htapes : install ![79] ambient
      (fun _ : Fin 1 => ZeroPadding.pad countCap (List.replicate n true))=ambient :=
    install_existing ![79] ambient _ (by intro i; fin_cases i; exact hc)
  change r.final.heads=installedHeads ![79] heads (fun _ : Fin 1 => 0) at hrh
  change r.final.tapes=install ![79] ambient
    (fun _ : Fin 1 => ZeroPadding.pad countCap (List.replicate n true)) at hrt
  rw [hheads] at hrh
  rw [htapes] at hrt
  obtain ⟨steps,hsteps,hpath⟩ := call_receipt sizes programs 37 next 0 (testNext n)
    (PCPControlOps.testCost n) (RecoveryCalls.restarted (programs 0) heads ambient) r hrun (by
      change next 0 r.final.control r.final.scanned=some (testNext n)
      rw [hq]
      by_cases h0 : n=0
      · simp [next,testNext,PCPControlOps.testCode,h0]
      · by_cases h1 : n=1 <;> simp [next,testNext,PCPControlOps.testCode,h0,h1])
  rw [hrh,hrt] at hpath
  exact ⟨steps,hsteps,hpath⟩

def WorkingHeads (heads : Fin 128 → ℕ) : Prop :=
  ∀ i,39 ≤ i.val → i≠80 → i≠81 → i≠82 → heads i=0

theorem WorkingHeads.advance {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (pre bits : List Bool) :
    WorkingHeads (installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0]) := by
  intro i hi h80 h81 h82
  by_cases h84 : i=84
  · subst i
    exact installedHeads_slot advanceSlots advanceSlots_injective heads _ 1
  by_cases h90 : i=90
  · subst i
    exact installedHeads_slot advanceSlots advanceSlots_injective heads _ 2
  rw [installedHeads_other advanceSlots heads _ i (by
    intro j; fin_cases j
    · intro he; subst i; contradiction
    · exact Ne.symm h84
    · exact Ne.symm h90)]
  exact hh i hi h80 h81 h82

theorem leafLoaded_other (pre bits suffix : List Bool) (cap log : ℕ)
    (ambient : Fin 128 → List Bool) (i : Fin 128)
    (h0 : 0≠i) (hi : ∀ j,leafSlots j≠i) (hd : 28≠i) (hl : 127≠i) :
    leafLoaded pre bits suffix cap log ambient i=ambient i := by
  apply Eq.trans (install_other advanceSlots _ _ i ?_)
    (leaf_printed_other cap log ambient i hi hd hl)
  intro j; fin_cases j
  · exact h0
  · exact hi 1
  · exact hi 3

theorem leafLoaded_driver (pre bits suffix : List Bool) (cap log : ℕ)
    (ambient : Fin 128 → List Bool) :
    leafLoaded pre bits suffix cap log ambient 28=List.replicate cap true := by
  apply Eq.trans (install_other advanceSlots _ _ 28 (by decide))
  apply Eq.trans (install_other leafPrintSlots _ _ 28 (by decide))
  exact cleared_driver leafSlots leafSlots_injective (by decide) (by decide) cap log ambient
theorem leafLoaded_log (pre bits suffix : List Bool) (cap log : ℕ)
    (ambient : Fin 128 → List Bool) :
    leafLoaded pre bits suffix cap log ambient 127=List.replicate (max log (cap+1)) false := by
  apply Eq.trans (install_other advanceSlots _ _ 127 (by decide))
  apply Eq.trans (install_other leafPrintSlots _ _ 127 (by decide))
  exact cleared_log leafSlots leafSlots_injective (by decide) (by decide) cap log ambient

theorem pairResult_driver (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) (localOut : Fin 38 → List Bool) :
    pairResult cap log bits ambient localOut 28=List.replicate cap true := by
  change install resultCopySlots
    (cleared resultSlots cap (max log (cap+1)) (paired cap log ambient localOut))
    (resultLocal cap bits) 28=List.replicate cap true
  apply Eq.trans (install_other resultCopySlots _ _ 28 (by decide))
  exact cleared_driver resultSlots resultSlots_injective (by decide) (by decide) cap
    (max log (cap+1)) (paired cap log ambient localOut)
theorem pairResult_log (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) (localOut : Fin 38 → List Bool) :
    pairResult cap log bits ambient localOut 127=List.replicate (max log (cap+1)) false := by
  change install resultCopySlots
    (cleared resultSlots cap (max log (cap+1)) (paired cap log ambient localOut))
    (resultLocal cap bits) 127=List.replicate (max log (cap+1)) false
  apply Eq.trans (install_other resultCopySlots _ _ 127 (by decide))
  have h := cleared_log resultSlots resultSlots_injective (by decide) (by decide) cap
    (max log (cap+1)) (paired cap log ambient localOut)
  rw [max_eq_left (le_max_right log (cap+1))] at h
  exact h

theorem pairResult_other (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) (localOut : Fin 38 → List Bool) (i : Fin 128)
    (hrange : i.val<39 ∨ 78 ≤ i.val)
    (h83 : 83≠i) (h84 : 84≠i) (h91 : 91≠i) (h28 : 28≠i) (h127 : 127≠i) :
    pairResult cap log bits ambient localOut i=ambient i := by
  apply Eq.trans (copiedResult_other cap (max log (cap+1)) bits _ i
    (by intro h; subst i; rcases hrange with h|h <;> contradiction)
    (by intro h; subst i; rcases hrange with h|h <;> contradiction) h91 h28 h127)
  apply Eq.trans (install_other pairSlots _ _ i
    (fun j => pair_ne j i (by omega) h83 h84))
  exact cleared_other bank cap log ambient i (fun j => bank_ne j i (by omega)) h28 h127

theorem leaf_branch (pre bits suffix : List Bool) (cap log countCap : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hcap : PCPPairCanonical.budget (1 : ℕ).bits bits+1≤cap)
    (hc : 3≤cap) (hbits : 2*bits.length+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hcount : ambient 79=ZeroPadding.pad countCap (List.replicate 1 true))
    (hsource : ambient 0=pre++frame bits++suffix)
    (hhd : heads 28=0) (hhsource : heads 0=pre.length) :
    ∃ out : Fin 128 → List Bool,
      Path 0 9 (11*cap+38) heads ambient
        (installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0]) out ∧
      out 77=ZeroPadding.pad cap (frame (Nat.pair 1 (value bits)).bits) ∧
      WorkBound cap out ∧ out 0=ambient 0 ∧ out 2=ambient 2 ∧
      out 28=List.replicate cap true ∧
      out 127=List.replicate (max log (cap+1)) false ∧
      (∀ i : Fin 128,i=78 ∨ i=80 ∨ i=81 ∨ i=82 → out i=ambient i) := by
  have htest := test_path 1 countCap heads ambient hcount (hh 79 (by decide) (by decide) (by decide) (by decide))
  have hload := leaf_load_path pre bits suffix cap log heads ambient hc
    (by intro i; fin_cases i <;> exact hb _ (by decide) (by decide)) hdriver hlog hsource
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide)) hhsource
  let loaded := leafLoaded pre bits suffix cap log ambient
  let moved := installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0]
  have hhmoved : WorkingHeads moved := hh.advance pre bits
  have hpos : 0<Nat.pair (value (1 : ℕ).bits) (value bits) := by
    change 0<Nat.pair 1 (value bits)
    unfold Nat.pair
    split <;> omega
  obtain ⟨localOut,hpair,_,_,hbound⟩ := pair_leaf_result_path cap (max log (cap+1)) (1 : ℕ).bits bits
    moved loaded hpos hcap (hb.leafLoaded hc pre bits suffix hbits)
    (leafLoaded_driver pre bits suffix cap log ambient) (leafLoaded_log pre bits suffix cap log ambient)
    (leaf_loaded_operands pre bits suffix cap log ambient).1
    (leaf_loaded_operands pre bits suffix cap log ambient).2
    (by intro i; apply hhmoved
        · simp only [bank]; omega
        · exact bank_ne i 80 (by decide)
        · exact bank_ne i 81 (by decide)
        · exact bank_ne i 82 (by decide))
    (by intro i; apply hhmoved
        · simp only [pairSlots]; split; decide; split; decide; simp only [bank]; omega
        · exact pair_ne i 80 (by decide) (by decide) (by decide)
        · exact pair_ne i 81 (by decide) (by decide) (by decide)
        · exact pair_ne i 82 (by decide) (by decide) (by decide))
    (by intro i; fin_cases i <;> exact hhmoved _ (by decide) (by decide) (by decide) (by decide))
    ((installedHeads_other advanceSlots heads _ 28 (by decide)).trans hhd)
    (hhmoved 127 (by decide) (by decide) (by decide) (by decide))
  let out := pairResult cap (max log (cap+1)) (Nat.pair 1 (value bits)).bits loaded localOut
  have hpath := (htest.trans hload).trans hpair
  refine ⟨out,hpath.mono (by dsimp [PCPControlOps.testCost]; omega),?_,hbound,?_,?_,?_,?_,?_⟩
  · exact copiedResult_result cap _ _ _
  · exact (pairResult_other cap _ _ loaded localOut 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      ((install_slot advanceSlots advanceSlots_injective _ (PCPFieldMoves.output pre bits suffix cap cap) 0).trans hsource.symm)
  · exact (pairResult_other cap _ _ loaded localOut 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (leafLoaded_other pre bits suffix cap log ambient 2 (by decide) (by decide) (by decide) (by decide))
  · exact pairResult_driver cap _ _ loaded localOut
  · have h := pairResult_log cap (max log (cap+1)) (Nat.pair 1 (value bits)).bits loaded localOut
    rw [max_eq_left (le_max_right log (cap+1))] at h
    exact h
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals apply Eq.trans (pairResult_other cap _ _ loaded localOut _ (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
    all_goals exact leafLoaded_other pre bits suffix cap log ambient _ (by decide) (by decide) (by decide) (by decide)

end NearCubicWires.RepairOrdinary.PCPTraversal
