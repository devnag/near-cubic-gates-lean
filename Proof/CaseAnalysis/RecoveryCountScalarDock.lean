import Proof.CaseAnalysis.RecoveryCountPacketRun

/-! Restore the original grammar's four row scalars inside the single
count bank, preserving the projector and both actual finite drivers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountScalarDock
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedCountBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 37) : Fin 152:=grammarSlots ((RecoveryBoundedGrammarAdvance.outerSlots j).castAdd 2)
theorem injective : Function.Injective slots :=
  grammar_injective.comp ((Fin.castAdd_injective 112 2).comp RecoveryBoundedGrammarAdvance.outer_injective)
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedCountScalarReset.machine

theorem projection (fields : Fin 78→List Bool) (node B P total : ℕ)
    (out stack packet source : List Bool) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool)
    (bd cd : List Bool) (j : Fin 37) :
    data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total cold bd cd (slots j)=
      RecoveryBoundedGrammarAdvance.bank B cold j := by
  have h73 : RecoveryBoundedGrammarBank.ready fields node B out stack packet source 73=List.replicate B false := by
    rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)];rfl
  have h76 : RecoveryBoundedGrammarBank.ready fields node B out stack packet source 76=List.replicate B true := by
    rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)];rfl
  have h77 : RecoveryBoundedGrammarBank.ready fields node B out stack packet source 77=List.replicate (B+1) false := by
    rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)];rfl
  fin_cases j <;> simp [slots,grammarSlots,RecoveryBoundedGrammarAdvance.outerSlots,data,extras,
    RecoveryBoundedFixedRestart.data,RecoveryBoundedFixedContinue.data,
    RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,
    RecoveryBoundedGrammarAdvance.bank,h73,h76,h77,ZeroPadding.pad_zero,Fin.addCases]

theorem projection_heads (out stack : List Bool) (bp cp : ℕ) (j : Fin 37) :
    heads out stack bp cp (slots j)=0 := by
  fin_cases j <;> rfl

theorem install_bank (fields : Fin 78→List Bool) (node B P total : ℕ)
    (out stack packet source : List Bool) (proj : Fin 37→List Bool) (cold next : Fin 33→List Bool)
    (bd cd : List Bool) :
    install slots (data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total cold bd cd)
      (RecoveryBoundedGrammarAdvance.bank B next)=
    data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total next bd cd := by
  apply HierarchyWidth.install_eq slots injective
  · intro j
    exact projection fields node B P total out stack packet source proj next bd cd j
  · intro i
    refine Fin.addCases (m:=116) (n:=36) (fun j=>?_) (fun j=>?_) i
    · intro _
      simp only [data,Fin.addCases_left]
    · refine Fin.addCases (m:=1) (n:=35) (fun k=>?_) (fun k=>?_) j
      · intro _
        simp only [data,extras,Fin.addCases_right,Fin.addCases_left]
      · refine Fin.addCases (m:=33) (n:=2) (fun k=>?_) (fun k=>?_) k
        · intro hi
          apply False.elim (hi (k.castAdd 4) ?_)
          simp only [slots,RecoveryBoundedGrammarAdvance.outerSlots,Fin.addCases_left]
          have he : (k.natAdd 79).castAdd 2=((k.castAdd 2).natAdd 1).natAdd 78 := by
            apply Fin.ext
            simp only [Fin.val_castAdd,Fin.val_natAdd]
            omega
          rw [he]
          simp only [grammarSlots,Fin.addCases_right]
        · intro _
          simp only [data,extras,Fin.addCases_right]

theorem run (q bound row C B P node total : ℕ) (extra : Fin 12→List Bool)
    (fields : Fin 78→List Bool) (out stack packet source : List Bool) (proj : Fin 37→List Bool)
    (bd cd : List Bool) (bp cp : ℕ)
    (hindex : row*BoundedOracleStructuralCircuit.rowWidth q bound+6+OuterPCPRecovery.boundedCircuitFieldLimit q bound≤B)
    (hrow : row≤B) (hF : 6+OuterPCPRecovery.boundedCircuitFieldLimit q bound+2≤B) :
    ∃ r,runFrom machine (RecoveryBoundedCountScalarReset.budget B)
      ⟨machine.start,heads out stack bp cp,
        data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total
          (RecoveryBoundedGrammarCold.metadata q bound row C B extra) bd cd⟩=some r ∧
      r.steps≤RecoveryBoundedCountScalarReset.budget B ∧ r.final.heads=heads out stack bp cp ∧
      r.final.tapes=data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total
        (RecoveryBoundedGrammarCold.metadata q bound 0 C B extra) bd cd := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(RecoveryBoundedCountScalarReset.ready q bound row C B extra hindex hrow hF).focus_at
    slots injective (heads out stack bp cp)
    (data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total
      (RecoveryBoundedGrammarCold.metadata q bound row C B extra) bd cd)
    (projection fields node B P total out stack packet source proj _ bd cd) (projection_heads out stack bp cp)
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt,install_bank]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountScalarDock
