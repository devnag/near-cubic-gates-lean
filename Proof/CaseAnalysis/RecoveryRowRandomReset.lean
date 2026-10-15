import Proof.CaseAnalysis.RecoveryRowPacketFields

/-! The original retained projector bank returns to randomness zero before
the next count case. Only the actual framed randomness word is rewritten. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowRandomReset
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairSource CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2→Fin 37:=![29,33]
noncomputable def localMachine:=RecoveryFocus.machine slots RecoveryBoundedRowRandomZero.machine

theorem zero_word (R : ℕ) : List.ofFn (bitInputOfCode R 0)=List.replicate R false := by
  exact (RecoveryPCPFormulaResumeRandomness.random_word R 0).trans
    (VerifierDecoding.LookupRuntime.binary_zero R)

theorem ready (p : RawProjectionPCP) (R Q k B : ℕ) :
    ClockJoin.ReadyRun localMachine (4*R+4)
      (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B)
      (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B) := by
  let cap:=RecoveryProjectionRows.capacity R+1
  have h:=RecoveryBoundedRowRandomZero.ready (List.ofFn (bitInputOfCode R k)) cap (by
    rw [List.length_ofFn]
    have h:=RecoveryProjectionColdRows.capacity_initialization R
    omega)
  rw [List.length_ofFn] at h
  have hz : ClockJoin.ReadyRun RecoveryBoundedRowRandomZero.machine (4*R+4)
      ![frame (List.ofFn (bitInputOfCode R k)),List.replicate cap false]
      ![frame (List.ofFn (bitInputOfCode R 0)),List.replicate cap false] := by
    rw [zero_word R]
    exact h
  let A:=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B
  have focused:=hz.focus slots (by decide) A (by
    intro j;fin_cases j
    · change ZeroPadding.pad 0 (frame (List.ofFn (bitInputOfCode R k))++[])=_
      rw [ZeroPadding.pad_zero,List.append_nil]
      rfl
    · change ZeroPadding.pad 0 (List.replicate cap false)=_
      exact ZeroPadding.pad_zero _)
  have he : install slots A ![frame (List.ofFn (bitInputOfCode R 0)),List.replicate cap false]=
      Function.update A 29 (frame (List.ofFn (bitInputOfCode R 0))) := by
    apply HierarchyWidth.install_eq slots (by decide)
    · intro j;fin_cases j
      · rfl
      · change ZeroPadding.pad 0 (List.replicate cap false)=List.replicate cap false
        exact ZeroPadding.pad_zero _
    · intro i hi
      have h29 : i≠29:=fun he=>hi 0 he.symm
      exact Function.update_of_ne h29 _ _
  rw [he,RecoveryBoundedRowProjection.bank_random] at focused
  exact focused

def outerSlots (j : Fin 37) : Fin 116:=(RecoveryBoundedRows.projectionSlots j).castAdd 1
theorem outer_injective : Function.Injective outerSlots := by
  intro a b h
  exact RecoveryBoundedRows.projection_injective (Fin.ext (congrArg (fun i : Fin 116=>i.val) h))
noncomputable def machine:=RecoveryFocus.machine outerSlots localMachine

theorem run (p : RawProjectionPCP) (R Q k B : ℕ) (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (hH : ∀ j,H (outerSlots j)=0)
    (hA : ∀ j,A (outerSlots j)=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B j) :
    ∃ r,runFrom machine (4*R+4) ⟨machine.start,H,A⟩=some r ∧ r.final.heads=H ∧
      r.final.tapes=install outerSlots A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B) ∧
      r.steps≤4*R+4 :=
  (ready p R Q k B).focus_at outerSlots outer_injective H A hA hH

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowRandomReset
