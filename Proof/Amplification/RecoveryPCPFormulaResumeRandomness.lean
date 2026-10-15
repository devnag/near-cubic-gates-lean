import Proof.Amplification.RecoveryProjectionRowsRewind
import Proof.MachineModel.OrdinaryFramedIncrement

/-! The same physical randomness field advances in the original formula's
little-endian allBitInputs order. Both local heads return to zero, and the
existing erase-log backing is reused. Every other tape is retained. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRandomness
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SignedSortKey
open SourceInterfaces CanonicalRecoveryLanguage ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem random_word (R k : Nat) : List.ofFn (bitInputOfCode R k)=binary R k :=
  VerifierDecoding.fixedBits_binary R k

def slots : Fin 2→Fin 37 := ![29,33]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots FramedIncrement.machine

theorem increment_ready (R k cap : Nat) (hk : k+1<2^R) (hc : 2*R≤cap)
    (ambient : Fin 37→List Bool)
    (hr : ambient 29=RepairOrdinary.frame (List.ofFn (bitInputOfCode R k)))
    (hlog : ambient 33=List.replicate cap false) :
    ClockJoin.ReadyRun machine (4*R+2) ambient
      (Function.update ambient 29 (RepairOrdinary.frame (List.ofFn (bitInputOfCode R (k+1))))) := by
  obtain ⟨r,hRun,hWord,hLog,hHeads,hSteps,_hPeak⟩ := FramedIncrement.increment_run R k cap hk hc
  have hTapes : r.final.tapes=![RepairOrdinary.frame (binary R (k+1)),List.replicate cap false] := by
    funext i; fin_cases i
    · exact hWord
    · exact hLog
  have hInput : Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>RepairOrdinary.frame (binary R k)) (fun _=>List.replicate cap false)=
      ![RepairOrdinary.frame (binary R k),List.replicate cap false] := by
    funext i; fin_cases i <;> rfl
  rw [hInput] at hRun
  have ready : ClockJoin.ReadyRun FramedIncrement.machine (4*R+2)
      ![RepairOrdinary.frame (binary R k),List.replicate cap false]
      ![RepairOrdinary.frame (binary R (k+1)),List.replicate cap false] :=
    ⟨r,hRun,hTapes,hHeads,hSteps⟩
  have focused:=ready.focus slots slots_injective ambient (by
    intro i; fin_cases i
    · change ambient 29=RepairOrdinary.frame (binary R k)
      simpa only [random_word] using hr
    · exact hlog)
  have he : install slots ambient
      ![RepairOrdinary.frame (binary R (k+1)),List.replicate cap false]=
      Function.update ambient 29 (RepairOrdinary.frame (List.ofFn (bitInputOfCode R (k+1)))) := by
    funext i
    by_cases h29 : i=29
    · subst i
      change install slots _ _ (slots 0)=_
      rw [install_slot _ slots_injective,Function.update_self,random_word]
      rfl
    by_cases h33 : i=33
    · subst i
      change install slots _ _ (slots 1)=_
      rw [install_slot _ slots_injective,Function.update_of_ne (by decide : (33 : Fin 37)≠29)]
      exact hlog.symm
    rw [install_other _ _ _ _ (by
      intro j; fin_cases j
      · exact Ne.symm h29
      · exact Ne.symm h33),Function.update_of_ne h29]
  rw [he] at focused
  exact focused

noncomputable def afterBatch (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (logCap : Nat) : Fin 37→List Bool :=
  Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryProjectionRows.cfg 3 (RecoveryProjectionRows.capacity R) R
      (QueryBytes.framedCodes (normalizedRows p R Q).flatten) (List.ofFn randomness) []
      (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))
      (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length Q 1).tapes
    (fun _=>List.replicate logCap false)

theorem batch_successor (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (k logCap : Nat) (hk : k+1<2^R) :
    ClockJoin.ReadyRun machine (4*R+2) (afterBatch p R Q hr hq x (bitInputOfCode R k) logCap)
      (Function.update (afterBatch p R Q hr hq x (bitInputOfCode R k) logCap) 29
        (RepairOrdinary.frame (List.ofFn (bitInputOfCode R (k+1))))) := by
  apply increment_ready R k (RecoveryProjectionRows.capacity R+1) hk
  · have h:=RecoveryProjectionColdRows.capacity_initialization R
    omega
  · change RepairOrdinary.frame (List.ofFn (bitInputOfCode R k))++[]= _
    exact List.append_nil _
  · rfl

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRandomness
