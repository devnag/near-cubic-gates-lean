import Proof.Circuits.DecompositionNestingRun

/-! Literal five-field native nesting entry, with every other tape blank.
This is the physical interface consumed by the cold prefix dock. -/
namespace NearCubicWires.RepairOrdinary.DecompositionNesting
open LocalBitMultitape
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeInput (C T k m : ℕ) (source : List Bool) (i : Fin 443) : List Bool :=
  if i.val=0 then source else if i.val=177 then List.replicate C true
  else if i.val=179 then CompareMachine.word T else if i.val=181 then CompareMachine.word k
  else if i.val=182 then CompareMachine.word m else []
def nativeHeads (pos : ℕ) (i : Fin 443) : ℕ :=
  if i.val=0 then pos else if i.val=179 ∨ i.val=181 ∨ i.val=182 then 1 else 0

theorem entry_tapes (C T k m : ℕ) (source : List Bool) (pos : ℕ) :
    (entry C T k m source pos).tapes=nativeInput C T k m source := by
  simp only [entry,DecompositionAtomStreamReady.entry,Rewind.recording,Rewind.config,DecompositionAtomCold.entry]
  funext i
  refine Fin.addCases (m:=181) (n:=262) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=180) (n:=1) (fun q => ?_) (fun q => ?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (m:=179) (n:=1) (fun p => ?_) (fun p => ?_) q
      · simp only [DecompositionAtomCold.input,Fin.addCases_left]
        change DecompositionAtomStart.input C source [] p=
          nativeInput C T k m source (((p.castAdd 1).castAdd 1).castAdd 262)
        simp only [DecompositionAtomStart.input,nativeInput,Fin.val_castAdd,Fin.ext_iff,Fin.val_zero,
          show (176 : Fin 179).val=176 from rfl,show (177 : Fin 179).val=177 from rfl]
        have hp := p.isLt
        split_ifs <;> first | rfl | omega
      · fin_cases p; rfl
    · fin_cases q; rfl
  · simp only [Fin.addCases_right,extras,nativeInput,Fin.val_natAdd]
    split_ifs <;> first | rfl | omega

theorem entry_heads (C T k m : ℕ) (source : List Bool) (pos : ℕ) :
    (entry C T k m source pos).heads=nativeHeads pos := by
  simp only [entry,DecompositionAtomStreamReady.entry,Rewind.recording,Rewind.config,DecompositionAtomCold.entry]
  funext i
  refine Fin.addCases (m:=181) (n:=262) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=180) (n:=1) (fun q => ?_) (fun q => ?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (m:=179) (n:=1) (fun p => ?_) (fun p => ?_) q
      · simp only [DecompositionAtomCold.heads,Fin.addCases_left,List.length_nil]
        change DecompositionAtomReuse.bodyHeads pos 0 p=nativeHeads pos (((p.castAdd 1).castAdd 1).castAdd 262)
        simp only [DecompositionAtomReuse.bodyHeads,nativeHeads,Fin.val_castAdd,Fin.ext_iff,Fin.val_zero,
          show (176 : Fin 179).val=176 from rfl]
        have hp := p.isLt
        split_ifs <;> omega
      · fin_cases p; rfl
    · fin_cases q; rfl
  · simp only [Fin.addCases_right,extraHeads,nativeHeads,Fin.val_natAdd]
    split_ifs <;> omega

end NearCubicWires.RepairOrdinary.DecompositionNesting
