import Proof.PCP.PCPPNativeCanonicalGuardLayout
import Proof.Amplification.RecoveryFocusDock

/-! Total cold guard for an arbitrary canonical tagged pair. The exact same
ordinary extractor serves circuit and legal-sum headers, preserving both
original-width payload frames. Nested payload validation is a later consumer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalGuard
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def allTests (bs : Fin 3 → Bool) := (bs 0 && bs 1) && bs 2

theorem allTests_iff (bits : List Bool) : allTests (tests bits)=true ↔ PCPPNativeCanonical.headerValid bits := by
  simp [allTests,tests,PCPPNativeCanonical.headerValid,and_assoc]

def gateInput (bs : Fin 3 → Bool) : Fin 4 → List Bool := ![[bs 0],[bs 1],[bs 2],[]]
def gateOutput (bs : Fin 3 → Bool) : Fin 4 → List Bool := ![[bs 0],[bs 1],[bs 2],[allTests bs]]
def gate : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    ![none,none,none,some ((scanned 0 && scanned 1) && scanned 2)],fun _=>.stay⟩ else none

theorem gate_ready (bs : Fin 3 → Bool) : ReadyRun gate 1 (gateInput bs) (gateOutput bs) := by
  let final : Configuration 4 2 := ⟨1,fun _=>0,gateOutput bs⟩
  have h : step gate (initialConfiguration gate (gateInput bs))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],hs⟩

noncomputable def last := RecoveryFocus.machine gateSlots gate
noncomputable def output (x bits : List Bool) := install gateSlots (before x bits 3) (gateOutput (tests bits))

theorem last_ready (x bits : List Bool) : ReadyRun last 1 (before x bits 3) (output x bits) := by
  exact (gate_ready (tests bits)).focus gateSlots (by decide) (before x bits 3) (by
    intro i;fin_cases i
    · exact physical_tests x bits 0
    · exact physical_tests x bits 1
    · exact physical_tests x bits 2
    · exact output_blank x bits)

theorem output_passes (x bits : List Bool) : readTapeBit (output x bits 137) 0=true ↔ PCPPNativeCanonical.headerValid bits := by
  have h := install_slot gateSlots (by decide) (before x bits 3) (gateOutput (tests bits)) 3
  change output x bits 137=[allTests (tests bits)] at h
  rw [h]
  exact allTests_iff bits

abbrev kindStates := Fintype.card (RecoveryCalls.Control CompetitorWitnessKind.sizes)
def sizes : Fin 4 → ℕ := ![kindStates,kindStates,kindStates,2]
noncomputable def programs : (j : Fin 4) → Machine 138 (sizes j)
  | ⟨0,_⟩=>program 0
  | ⟨1,_⟩=>program 1
  | ⟨2,_⟩=>program 2
  | ⟨3,_⟩=>last
  | ⟨n+4,h⟩=>False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 138 → Bool) : Option (Fin 4) := ![some 1,some 2,some 3,none] j
noncomputable def guard := RecoveryCalls.machine sizes programs 0 next

theorem guard_ready (x bits : List Bool) : ReadyRun guard (48*bits.length+86) (start x bits) (output x bits) := by
  have hh (j : Fin 3) : ReadyRun (program j) (16*bits.length+27)
      (before x bits j.val) (before x bits (j.val+1)) := by
    simpa only [values_length] using step_ready x bits j
  have h0 := (hh 0).call sizes programs 0 next 0 1 (by intro q;rfl)
  have h1 := (hh 1).call sizes programs 0 next 1 2 (by intro q;rfl)
  have h2 := (hh 2).call sizes programs 0 next 2 3 (by intro q;rfl)
  have h3 := (last_ready x bits).stop sizes programs 0 next 3 (by intro q;rfl)
  have h := ((h0.trans h1).trans h2).trans h3
  have he : ((16*bits.length+27+1+(16*bits.length+27+1))+(16*bits.length+27+1))+(1+1)=48*bits.length+86 := by omega
  rw [he] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i;simp [hf,RecoveryCalls.stopped],hs⟩

noncomputable def first := TapeEmbedding.machine 16 CompetitorWitnessTriple.machine
noncomputable def machine := Composition.machine first guard
def input (x bits : List Bool) : Fin 138 → List Bool := Fin.addCases
  (m := 122) (n := 16) (motive := fun _=>List Bool) (CompetitorWitnessTriple.input x bits) (fun _=>[])
def budget (bits : List Bool) := 26000*(bits.length+1)^2

theorem input_eq (x bits : List Bool) (i : Fin 138) : input x bits i=
    if i.val=0 then frame x else if i.val=1 then frame bits else [] := by
  refine Fin.addCases (m := 122) (n := 16) ?_ ?_ i
  · intro j
    rw [input,Fin.addCases_left,CompetitorWitnessTriple.input]
    rfl
  · intro j
    rw [input,Fin.addCases_right]
    have h0 : (j.natAdd 122).val≠0 := by simp only [Fin.val_natAdd];omega
    have h1 : (j.natAdd 122).val≠1 := by simp only [Fin.val_natAdd];omega
    rw [if_neg h0,if_neg h1]

theorem output_nodes (x bits : List Bool) : output x bits 38=frame (PCPPNativeCanonical.nodeWord bits) := by
  rw [output,install_other gateSlots _ _ 38 (by intro j;fin_cases j <;> decide)]
  exact nodes_retained x bits

theorem output_index (x bits : List Bool) : output x bits 78=frame (PCPPNativeCanonical.outputWord bits) := by
  rw [output,install_other gateSlots _ _ 78 (by intro j;fin_cases j <;> decide)]
  exact output_retained x bits

theorem header_run (x bits : List Bool) :
    ∃ r : ExecutionReceipt 138 _,run machine (budget bits) (input x bits)=some r ∧
      r.steps ≤ budget bits ∧ (∀ i,r.final.heads i=0) ∧
      (readTapeBit (r.final.tapes 137) 0=true ↔ PCPPNativeCanonical.headerValid bits) ∧
      r.final.tapes 38=frame (PCPPNativeCanonical.nodeWord bits) ∧
      r.final.tapes 78=frame (PCPPNativeCanonical.outputWord bits) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := CompetitorWitnessTriple.triple_ready x bits
  let padded : ExecutionReceipt 138 _ := TapeEmbedding.receipt (fun _ : Fin 16=>0) (fun _=>[]) base
  have hp := TapeEmbedding.run_embed CompetitorWitnessTriple.machine (fun _ : Fin 16=>0) (fun _=>[]) _ _ base hb
  have pi : TapeEmbedding.config (fun _ : Fin 16=>0) (fun _=>[]) (initialConfiguration CompetitorWitnessTriple.machine (CompetitorWitnessTriple.input x bits))=
      initialConfiguration first (input x bits) := by
    apply configuration_ext
    · rfl
    · funext i;refine Fin.addCases (m := 122) (n := 16) ?_ ?_ i
      · intro j;simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left]
      · intro j;simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_right]
    · rfl
  change runFrom first _ _=some padded at hp
  rw [pi] at hp
  have ph : padded.final.heads=fun _=>0 := by
    funext i;refine Fin.addCases (m := 122) (n := 16) ?_ ?_ i
    · intro j;exact (TapeEmbedding.receipt_heads_old _ _ base j).trans (bh j)
    · intro j;exact TapeEmbedding.receipt_heads_new _ _ base j
  have pt : padded.final.tapes=start x bits := by
    funext i;refine Fin.addCases (m := 122) (n := 16) ?_ ?_ i
    · intro j
      rw [start,Fin.addCases_left]
      exact (TapeEmbedding.receipt_tapes_old _ _ base j).trans (congrFun bt j)
    · intro j
      rw [start,Fin.addCases_right]
      exact TapeEmbedding.receipt_tapes_new _ _ base j
  obtain ⟨tail,ht,tt,th,ts⟩ := guard_ready x bits
  have hi : Composition.restart padded.final guard.start=initialConfiguration guard (start x bits) := by
    apply configuration_ext
    · rfl
    · exact ph
    · exact pt
  have ht' : runFrom guard (48*bits.length+86) (Composition.restart padded.final guard.start)=some tail := by
    rw [hi];exact ht
  have hj := Composition.run_join first guard _ _ _ padded tail hp ht'
  let actual := Composition.joinedReceipt padded tail
  have htime : CompetitorWitnessTriple.time bits+1+(48*bits.length+86) ≤ budget bits := by
    have hb := CompetitorWitnessTriple.time_bound bits
    have hs : 0<(bits.length+1)^2 := by positivity
    unfold CompetitorWitnessTriple.budget budget at *
    nlinarith
  have hm := run_moreFuel machine _ (budget bits-(CompetitorWitnessTriple.time bits+1+(48*bits.length+86)))
    _ actual hj
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨actual,hm,?_,th,?_,?_,?_⟩
  · change base.steps+1+tail.steps ≤ budget bits
    rw [bs,ts]
    exact htime
  · change readTapeBit (tail.final.tapes 137) 0=true ↔_
    rw [tt];exact output_passes x bits
  · change tail.final.tapes 38=_
    rw [tt];exact output_nodes x bits
  · change tail.final.tapes 78=_
    rw [tt];exact output_index x bits

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalGuard
