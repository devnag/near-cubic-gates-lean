import Proof.MachineModel.FinalRun

/-! The occurrence loop's actual accumulated streams meet the finalizer entry.
This ties cache bytes and occurrence counts to the SAME executed constructors. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

def totalWord {q:ℕ} (occ:List (SupportedNormalizedGate q)):=false::List.replicate (B a occ) true
def countWord {q:ℕ} (occ:List (SupportedNormalizedGate q)):=(counts a occ).flatMap natWord
def bodyWord {q:ℕ} (occ:List (SupportedNormalizedGate q)):=(GS a occ).flatMap exactWord

theorem final_entry_heads {q:ℕ} (occ:List (SupportedNormalizedGate q)) (pos:ℕ) :
    ∀j,loopHeads a pos (countWord a occ) (bodyWord a occ) (totalWord a occ)
      (FinalLayout.prefixSlots a j)=CacheStart.inputHeads (B a occ) j := by
  intro j;fin_cases j <;>
    simp (disch:=omega) [FinalLayout.prefixSlots,FinalLayout.prefixValue,loopHeads,
      CacheStart.inputHeads,totalWord,Fin.addCases,sb_eq] <;> omega

theorem final_entry_tapes {q:ℕ} (C:ℕ) (occ:List (SupportedNormalizedGate q)) (source:List Bool) :
    ∀j,loopTapes a C q source (countWord a occ) (bodyWord a occ) (totalWord a occ)
      (FinalLayout.prefixSlots a j)=CacheStart.input C (B a occ) j := by
  intro j;fin_cases j <;>
    simp (disch:=omega) [FinalLayout.prefixSlots,FinalLayout.prefixValue,loopTapes,
      CacheStart.input,totalWord,Fin.addCases,sb_eq] <;> omega

theorem final_state_run {q:ℕ} (C:ℕ) (occ:List (SupportedNormalizedGate q))
    (pos:ℕ) (source:List Bool)
    (hn:B a occ+2≤C) (hh:PCPPNativeNaturalAppend.budget (B a occ)≤C)
    (hb:(bodyWord a occ).length≤C) (hc:(exactListWord (GS a occ)).length≤C) :
    ∃ O:Fin (T a) → List Bool,
      Step (FinalLayout.machine a) (FinalLayout.finalCost C (GS a occ))
        (loopHeads a pos (countWord a occ) (bodyWord a occ) (totalWord a occ))
        (loopTapes a C q source (countWord a occ) (bodyWord a occ) (totalWord a occ))
        (FinalLayout.finishedHeads a (GS a occ)
          (loopHeads a pos (countWord a occ) (bodyWord a occ) (totalWord a occ))) O ∧
      O (cch a)=exactListWord (GS a occ) ∧ O (cnt a)=countWord a occ ∧ O (str a)=source ∧
      O (tot a)=UnaryTemplate.tape (B a occ) ∧ O (dom a)=UnaryTemplate.tape q ∧
      O (scr a)=List.replicate (B a occ) false ∧
      O (drv a)=List.replicate C true ∧ O (wsp a)=List.replicate (C+1) false := by
  let H:=loopHeads a pos (countWord a occ) (bodyWord a occ) (totalWord a occ)
  let A:=loopTapes a C q source (countWord a occ) (bodyWord a occ) (totalWord a occ)
  obtain ⟨O,run,cache,total,domain,driver,log,scratch,keep⟩:=FinalLayout.final_run a C (GS a occ) H A
    (final_entry_heads a occ pos) (final_entry_tapes a C occ source)
    (by simp [H,loopHeads,bod,ex,bodyWord]) (by simp [A,loopTapes,bod,ex,bodyWord])
    (by simp [H,loopHeads,dom,ex]) (by simp [A,loopTapes,dom,ex])
    (by simp [H,loopHeads,drv,ex]) (by simp [A,loopTapes,drv,ex])
    (by simp [H,loopHeads,wsp,ex]) (by simp [A,loopTapes,wsp,ex]) hn hh hb hc
  refine ⟨O,run,cache,?_,?_,total,domain,scratch,driver,log⟩
  · have h:=keep 1 (Or.inr rfl)
    simpa [A,loopTapes,ex,cnt] using h
  · have h:=keep 0 (Or.inl rfl)
    simpa [A,loopTapes,ex,str] using h

end NearCubicWires.ExtDecompositionBatch
