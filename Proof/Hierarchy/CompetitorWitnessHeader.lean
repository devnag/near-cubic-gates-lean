import Proof.Hierarchy.CompetitorWitnessHeaderFlags
import Proof.Amplification.RecoveryFocusDock

/-! Complete all-input canonical witness-header guard. One fixed ordinary
machine starts with exactly the input/witness frames and blank workspace,
extracts the header, classifies every control field, and leaves a validity
bit while preserving both nested payloads. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev kindStates := Fintype.card (RecoveryCalls.Control CompetitorWitnessKind.sizes)
def sizes : Fin 6 → ℕ := ![kindStates,kindStates,kindStates,kindStates,kindStates,2]
noncomputable def programs : (j : Fin 6) → Machine 148 (sizes j)
  | ⟨0,_⟩=>program 0
  | ⟨1,_⟩=>program 1
  | ⟨2,_⟩=>program 2
  | ⟨3,_⟩=>program 3
  | ⟨4,_⟩=>program 4
  | ⟨5,_⟩=>last
  | ⟨n+6,h⟩=>False.elim (by omega)
def next (j : Fin 6) (_ : Fin (sizes j)) (_ : Fin 148 → Bool) : Option (Fin 6) := ![some 1,some 2,some 3,some 4,some 5,none] j
noncomputable def guard := RecoveryCalls.machine sizes programs 0 next

theorem guard_ready (x bits : List Bool) : ReadyRun guard (80*bits.length+142) (start x bits) (output x bits) := by
  have hh (j : Fin 5) : ReadyRun (program j) (16*bits.length+27)
      (before x bits j.val) (before x bits (j.val+1)) := by
    simpa only [values_length] using step_ready x bits j
  have h0 := (hh 0).call sizes programs 0 next 0 1 (by intro q;rfl)
  have h1 := (hh 1).call sizes programs 0 next 1 2 (by intro q;rfl)
  have h2 := (hh 2).call sizes programs 0 next 2 3 (by intro q;rfl)
  have h3 := (hh 3).call sizes programs 0 next 3 4 (by intro q;rfl)
  have h4 := (hh 4).call sizes programs 0 next 4 5 (by intro q;rfl)
  have h5 := (last_ready x bits).stop sizes programs 0 next 5 (by intro q;rfl)
  have h := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
  have he : ((((16*bits.length+27+1+(16*bits.length+27+1))+(16*bits.length+27+1))+
      (16*bits.length+27+1))+(16*bits.length+27+1))+(1+1)=80*bits.length+142 := by omega
  rw [he] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i;simp [hf,RecoveryCalls.stopped],hs⟩

noncomputable def first := TapeEmbedding.machine 26 CompetitorWitnessTriple.machine
noncomputable def machine := Composition.machine first guard
def input (x bits : List Bool) : Fin 148 → List Bool := Fin.addCases
  (m := 122) (n := 26) (motive := fun _=>List Bool) (CompetitorWitnessTriple.input x bits) (fun _=>[])
def budget (bits : List Bool) := 26000*(bits.length+1)^2

theorem input_eq (x bits : List Bool) (i : Fin 148) : input x bits i=
    if i.val=0 then frame x else if i.val=1 then frame bits else [] := by
  refine Fin.addCases (m := 122) (n := 26) ?_ ?_ i
  · intro j
    rw [input,Fin.addCases_left,CompetitorWitnessTriple.input]
    rfl
  · intro j
    rw [input,Fin.addCases_right]
    have h0 : (j.natAdd 122).val≠0 := by simp only [Fin.val_natAdd];omega
    have h1 : (j.natAdd 122).val≠1 := by simp only [Fin.val_natAdd];omega
    rw [if_neg h0,if_neg h1]

theorem output_oracle (x bits : List Bool) : output x bits 78=
    frame (RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 3)) := by
  rw [output,install_other gateSlots _ _ 78 (by intro j;fin_cases j <;> decide)]
  exact oracle_retained x bits

theorem output_sum (x bits : List Bool) : output x bits 118=
    frame (RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 5)) := by
  rw [output,install_other gateSlots _ _ 118 (by intro j;fin_cases j <;> decide)]
  exact sum_retained x bits

theorem header_run (x bits : List Bool) :
    ∃ r : ExecutionReceipt 148 _,run machine (budget bits) (input x bits)=some r ∧
      r.steps ≤ budget bits ∧ (∀ i,r.final.heads i=0) ∧
      (readTapeBit (r.final.tapes 147) 0=true ↔ CompetitorWitnessTriple.headerValid bits) ∧
      r.final.tapes 78=frame (RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 3)) ∧
      r.final.tapes 118=frame (RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 5)) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := CompetitorWitnessTriple.triple_ready x bits
  let padded : ExecutionReceipt 148 _ := TapeEmbedding.receipt (fun _ : Fin 26=>0) (fun _=>[]) base
  have hp := TapeEmbedding.run_embed CompetitorWitnessTriple.machine (fun _ : Fin 26=>0) (fun _=>[]) _ _ base hb
  have pi : TapeEmbedding.config (fun _ : Fin 26=>0) (fun _=>[]) (initialConfiguration CompetitorWitnessTriple.machine (CompetitorWitnessTriple.input x bits))=
      initialConfiguration first (input x bits) := by
    apply configuration_ext
    · rfl
    · funext i;refine Fin.addCases (m := 122) (n := 26) ?_ ?_ i
      · intro j;simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left]
      · intro j;simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_right]
    · rfl
  change runFrom first _ _=some padded at hp
  rw [pi] at hp
  have ph : padded.final.heads=fun _=>0 := by
    funext i;refine Fin.addCases (m := 122) (n := 26) ?_ ?_ i
    · intro j;exact (TapeEmbedding.receipt_heads_old _ _ base j).trans (bh j)
    · intro j;exact TapeEmbedding.receipt_heads_new _ _ base j
  have pt : padded.final.tapes=start x bits := by
    funext i;refine Fin.addCases (m := 122) (n := 26) ?_ ?_ i
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
  have ht' : runFrom guard (80*bits.length+142) (Composition.restart padded.final guard.start)=some tail := by
    rw [hi];exact ht
  have hj := Composition.run_join first guard _ _ _ padded tail hp ht'
  let actual := Composition.joinedReceipt padded tail
  have htime : CompetitorWitnessTriple.time bits+1+(80*bits.length+142) ≤ budget bits := by
    have hb := CompetitorWitnessTriple.time_bound bits
    have hs : 0<(bits.length+1)^2 := by positivity
    unfold CompetitorWitnessTriple.budget budget at *
    nlinarith
  have hm := run_moreFuel machine _ (budget bits-(CompetitorWitnessTriple.time bits+1+(80*bits.length+142)))
    _ actual hj
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨actual,hm,?_,th,?_,?_,?_⟩
  · change base.steps+1+tail.steps ≤ budget bits
    rw [bs,ts]
    exact htime
  · change readTapeBit (tail.final.tapes 147) 0=true ↔_
    rw [tt];exact output_passes x bits
  · change tail.final.tapes 78=_
    rw [tt];exact output_oracle x bits
  · change tail.final.tapes 118=_
    rw [tt];exact output_sum x bits

end NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
