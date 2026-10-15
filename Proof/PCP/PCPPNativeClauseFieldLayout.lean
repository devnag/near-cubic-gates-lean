import Proof.PCP.PCPPNativeClauseReferenceWord
import Proof.PCP.PCPFieldMoves
import Proof.PCP.ProjectionNormalizationUnary

/-! Read the actual original clause's framed Nat.bits field. The native
output natWord format is not assumed equal to this source encoding. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseField
open LocalBitMultitape RecoveryExecution RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 3→Fin 19 := ![13,14,15]
def unarySlots : Fin 5→Fin 19 := ![14,16,17,0,18]
def refSlots (j : Fin 13) : Fin 19 := j.castAdd 6
theorem copy_injective : Function.Injective copySlots := by decide
theorem unary_injective : Function.Injective unarySlots := by decide
theorem ref_injective : Function.Injective refSlots := by intro i j h; exact Fin.ext (congrArg (fun k : Fin 19=>k.val) h)
noncomputable def copyMachine := RecoveryFocus.machine copySlots PCPFieldMoves.advanceMachine
noncomputable def unaryMachine := RecoveryFocus.machine unarySlots Unary.machine
noncomputable def refMachine := RecoveryFocus.machine refSlots PCPPNativeClauseReference.machine
def input (source : List Bool) (stride p n : ℕ) (i : Fin 19) :=
  if i=13 then source else if i=4 then UnaryTemplate.tape stride
  else if i=5 then List.replicate p true else if i=6 then List.replicate n true else []
def heads (pos : ℕ) (i : Fin 19) := if i=13 then pos else 0
def copied (source bits : List Bool) (stride p n : ℕ) (i : Fin 19) :=
  if i=14 then frame bits else if i=15 then List.replicate (2*bits.length+1) false else input source stride p n i
def entry {s : ℕ} (p : Machine 19 s) (pos : ℕ) (data : Fin 19→List Bool) : Configuration 19 s :=
  ⟨p.start,heads pos,data⟩

theorem copy_run (pre bits tail : List Bool) (stride p n : ℕ) : ∃ r,
    runFrom copyMachine (4*bits.length+4)
      (entry copyMachine pre.length (input (pre++frame bits++tail) stride p n))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes=copied (pre++frame bits++tail) bits stride p n ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,bt,bh,bs⟩:=PCPFieldMoves.advance_run pre bits tail 0 0
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock copySlots copy_injective PCPFieldMoves.advanceMachine _
    (heads pre.length) (input (pre++frame bits++tail) stride p n) (PCPFieldMoves.entry pre bits tail 0 0)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [input,copySlots,PCPFieldMoves.entry,PCPFieldMoves.caps,ZeroPadding.config,ZeroPadding.pad_zero,Rewind.recording,Rewind.config,Field.cfg,Fin.addCases,List.append_assoc]) base hb
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · funext i
    by_cases h13 : i=13
    · rw [h13]
      exact (rh 0).trans (by rw [bh]; rfl)
    by_cases h14 : i=14
    · rw [h14]
      exact (rh 1).trans (by rw [bh]; rfl)
    by_cases h15 : i=15
    · rw [h15]
      exact (rh 2).trans (by rw [bh]; rfl)
    rw [(keep i (by intro j; fin_cases j; exact Ne.symm h13; exact Ne.symm h14; exact Ne.symm h15)).1]
    simp [heads,h13]
  · funext i
    by_cases h13 : i=13
    · rw [h13]
      exact (rt 0).trans (by rw [bt]; rfl)
    by_cases h14 : i=14
    · rw [h14]
      exact (rt 1).trans (by rw [bt]; exact ZeroPadding.pad_zero _)
    by_cases h15 : i=15
    · rw [h15]
      exact (rt 2).trans (by rw [bt]; simp [PCPFieldMoves.output,copied])
    rw [(keep i (by intro j; fin_cases j; exact Ne.symm h13; exact Ne.symm h14; exact Ne.symm h15)).2]
    simp [copied,h14,h15]

end NearCubicWires.RepairOrdinary.PCPPNativeClauseField
