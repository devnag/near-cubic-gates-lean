import Proof.MachineModel.ClockFloorLog

/-! The exact code-length guard limit is produced from the retained literal
input. No free limit word or precomputed binary length is an antecedent. -/
namespace NearCubicWires.RepairOrdinary.ClockFloorLogFromInput
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) : Fin 6 → List Bool := ![[],[],frame bits,[],[],[]]
def counted (bits : List Bool) (cap scratch : ℕ) : Fin 6 → List Bool :=
  ![frame (ClockBinary.word bits.length),List.replicate cap false,frame bits,
    List.replicate scratch false,[],[]]
noncomputable def countProgram := ClockJoin.lifted (e:=2) (Equiv.refl (Fin 6)) HierarchyInputLength.machine
def logSlots : Fin 3 → Fin 6 := ![0,4,5]
theorem log_injective : Function.Injective logSlots := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [logSlots] at h ⊢
noncomputable def logProgram := RecoveryFocus.machine logSlots ClockFloorLog.machine
noncomputable def machine := Composition.machine countProgram logProgram
def budget (bits : List Bool) := HierarchyInputLength.budget bits+1+(4*PCPResourceLedger.ell bits.length+8)

theorem pick_other (i : Fin 6) (hi : ∀ j,logSlots j≠i) : RecoveryFocus.pick logSlots i=none := by
  have hn : ¬∃ j,logSlots j=i := by simpa using hi
  simp [RecoveryFocus.pick,hn]
theorem pick_values (i : Fin 6) :
    RecoveryFocus.pick logSlots i=(![some 0,none,none,none,some 1,some 2] : Fin 6 → Option (Fin 3)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot _ log_injective 0
  · exact pick_other _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ log_injective 1
  · exact RecoveryFocus.pick_slot _ log_injective 2

theorem count_ready (bits : List Bool) :
    ∃ cap scratch,ClockJoin.ReadyRun countProgram (HierarchyInputLength.budget bits) (input bits) (counted bits cap scratch) := by
  obtain ⟨cap,scratch,_,_,r,hr,h0,h1,h2,h3,hh,hs⟩ := HierarchyInputLength.count_run bits
  have ht : r.final.tapes=![frame (ClockBinary.word bits.length),List.replicate cap false,frame bits,
      List.replicate scratch false] := by
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have h := ClockJoin.lift (e:=2) (Equiv.refl (Fin 6)) HierarchyInputLength.machine _ _ _ (fun _ => [])
    ⟨r,hr,ht,hh,hs⟩
  have hi : ClockJoin.data (e:=2) (Equiv.refl (Fin 6)) (HierarchyInputLength.input bits) (fun _ => [])=input bits := by
    funext i; fin_cases i <;> rfl
  have ho : ClockJoin.data (e:=2) (Equiv.refl (Fin 6))
      ![frame (ClockBinary.word bits.length),List.replicate cap false,frame bits,List.replicate scratch false]
      (fun _ => [])=counted bits cap scratch := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at h
  exact ⟨cap,scratch,h⟩

theorem log_run (bits : List Bool) (cap scratch : ℕ) :
    ∃ r,run logProgram (4*PCPResourceLedger.ell bits.length+8) (counted bits cap scratch)=some r ∧
      r.final.tapes 0=frame (ClockBinary.word bits.length) ∧ r.final.tapes 2=frame bits ∧
      r.final.tapes 4=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 bits.length) ∧
      r.final.heads=![0,0,0,0,1,0] ∧ r.steps=4*PCPResourceLedger.ell bits.length+8 := by
  obtain ⟨base,hb,h0,h1,_,hh,hs⟩ := ClockFloorLog.binary_run bits.length
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config logSlots log_injective ClockFloorLog.machine
    (fun _ => 0) (counted bits cap scratch) (4*PCPResourceLedger.ell bits.length+8) _ base hb
  have hi : RecoveryFocus.config logSlots (fun _ => 0) (counted bits cap scratch)
      (initialConfiguration ClockFloorLog.machine (ClockFloorLog.input (ClockBinary.word bits.length)))=
      initialConfiguration logProgram (counted bits cap scratch) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick logSlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing logSlots _ _ (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,?_,?_,hrs.trans hs⟩
  · simpa [hf,RecoveryFocus.config,pick_values] using h0
  · simp [hf,RecoveryFocus.config,pick_values,counted]
  · simpa [hf,RecoveryFocus.config,pick_values] using h1
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,pick_values,hh]

theorem from_input_run (bits : List Bool) :
    ∃ r,run machine (budget bits) (input bits)=some r ∧
      r.final.tapes 0=frame (ClockBinary.word bits.length) ∧ r.final.tapes 2=frame bits ∧
      r.final.tapes 4=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 bits.length) ∧
      r.final.heads=![0,0,0,0,1,0] ∧ r.steps ≤ budget bits := by
  obtain ⟨cap,scratch,first,hfirst,ht,hh,hs⟩ := count_ready bits
  obtain ⟨last,hlast,h0,h2,h4,hlh,hls⟩ := log_run bits cap scratch
  have he : Composition.restart first.final logProgram.start=initialConfiguration logProgram (counted bits cap scratch) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  unfold run at hlast
  rw [← he] at hlast
  have h := Composition.run_join countProgram logProgram (HierarchyInputLength.budget bits)
    (4*PCPResourceLedger.ell bits.length+8) _ first last hfirst hlast
  refine ⟨Composition.joinedReceipt first last,h,h0,h2,h4,hlh,?_⟩
  dsimp only [Composition.joinedReceipt,budget]
  omega

end NearCubicWires.RepairOrdinary.ClockFloorLogFromInput
