import Proof.Amplification.RecoveryPCPFormulaResumeRowReusable
import Proof.Amplification.RecoveryPCPFormulaResumeRandomness

/-! The same stored randomness field changes at one exact physical slot.
All restored source, clause, address and formula tapes remain in place. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRowRandomness
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
open RecoveryPCPFormulaResumeRow RecoveryPCPFormulaResumeRowReset CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem install_update {t u : Nat} (slot : Fin t→Fin u) (hinj : Function.Injective slot)
    (ambient : Fin u→List Bool) (replacement : Fin t→List Bool) (j : Fin t) (value : List Bool) :
    install slot ambient (Function.update replacement j value)=
      Function.update (install slot ambient replacement) (slot j) value := by
  funext i
  by_cases hi : i=slot j
  · subst i
    rw [install_slot slot hinj,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hi]
    cases hp : RecoveryFocus.pick slot i with
    | none => simp only [install,hp]
    | some k =>
      have he:=RecoveryFocus.slot_of_pick slot hp
      have hk : k≠j := by intro h; subst k; exact hi he.symm
      simp only [install,hp,Function.update_of_ne hk]

theorem batch_random (p : RawProjectionPCP) (R Q : Nat) (r s : BitInput R) (logCap : Nat) :
    Function.update (batchInput p R Q r logCap) 29 (frame (List.ofFn s))=batchInput p R Q s logCap := by
  funext i
  fin_cases i
  all_goals first | rfl | exact (List.append_nil _).symm

theorem initial_random (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (r s : BitInput R) (logCap : Nat) :
    Function.update (initialTapes cap source out 0 count p R Q r logCap) 310 (frame (List.ofFn s))=
      initialTapes cap source out 0 count p R Q s logCap := by
  unfold initialTapes
  rw [←batch_random p R Q r s logCap,install_update addressSlots address_injective]
  rfl

theorem input_random (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (r s : BitInput R) (logCap resetCap : Nat) :
    Function.update (input cap source out count p R Q r logCap resetCap) 310 (frame (List.ofFn s))=
      input cap source out count p R Q s logCap resetCap := by
  have h:=initial_random cap source out count p R Q r s logCap
  funext i
  refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
  · by_cases hi : i=310
    · subst i
      change frame (List.ofFn s)=ZeroPadding.pad 0 (initialTapes cap source out 0 count p R Q s logCap 310)
      rw [ZeroPadding.pad_zero,←h,Function.update_self]
    · have hn : (i.castAdd 1 : Fin 318)≠310 := by
        intro he; apply hi; exact Fin.ext (congrArg (fun j : Fin 318=>j.val) he)
      rw [Function.update_of_ne hn]
      simp only [input,Fin.addCases_left,tapes]
      rw [←h,Function.update_of_ne hi]
  · fin_cases i; rfl

def slots (i : Fin 37) : Fin 318 := (addressSlots i).castAdd 1
theorem slots_injective : Function.Injective slots := by
  intro a b h
  apply address_injective
  exact Fin.ext (congrArg (fun i : Fin 318=>i.val) h)
noncomputable def machine := RecoveryFocus.machine slots RecoveryPCPFormulaResumeRandomness.machine

theorem increment_run (p : RawProjectionPCP) (R Q cap logCap resetCap k : Nat) (source out : List Bool)
    (count : Nat) (hk : k+1<2^R) : ∃ r,
    runFrom machine (4*R+2)
      ⟨machine.start,heads cap source out count,
        input cap source out count p R Q (bitInputOfCode R k) logCap resetCap⟩=some r ∧
      r.final.heads=heads cap source out count ∧
      r.final.tapes=input cap source out count p R Q (bitInputOfCode R (k+1)) logCap resetCap ∧
      r.steps≤4*R+2 := by
  let ambient:=input cap source out count p R Q (bitInputOfCode R k) logCap resetCap
  let projected : Fin 37→List Bool := fun i=>ambient (slots i)
  have hrandom : projected 29=frame (List.ofFn (bitInputOfCode R k)) := by
    change ZeroPadding.pad 0 (initialTapes cap source out 0 count p R Q (bitInputOfCode R k) logCap (addressSlots 29))=_
    rw [ZeroPadding.pad_zero,initialTapes,install_slot addressSlots address_injective]
    exact List.append_nil _
  have hlog : projected 33=List.replicate (RecoveryProjectionRows.capacity R+1) false := by
    change ZeroPadding.pad 0 (initialTapes cap source out 0 count p R Q (bitInputOfCode R k) logCap (addressSlots 33))=_
    rw [ZeroPadding.pad_zero,initialTapes,install_slot addressSlots address_injective]
    rfl
  have ready:=RecoveryPCPFormulaResumeRandomness.increment_ready R k (RecoveryProjectionRows.capacity R+1)
    hk (by have h:=RecoveryProjectionColdRows.capacity_initialization R; omega) projected hrandom hlog
  obtain ⟨r,hr,rh,rt,rs⟩ := ready.focus_at slots slots_injective (heads cap source out count) ambient
    (by intro i; rfl) (by
      intro i
      change Fin.addCases (m:=317) (n:=1) (motive:=fun _=>Nat)
        (initialHeads cap source out 0 count) (fun _=>0) ((addressSlots i).castAdd 1)=0
      rw [Fin.addCases_left]
      exact address_heads cap source out 0 count i)
  refine ⟨r,hr,rh,?_,rs⟩
  rw [rt,install_update slots slots_injective,install_existing slots ambient projected (by intro i; rfl)]
  exact input_random cap source out count p R Q (bitInputOfCode R k) (bitInputOfCode R (k+1)) logCap resetCap

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRowRandomness
