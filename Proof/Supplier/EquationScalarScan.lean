import Proof.Supplier.EquationScalarArithmetic
import Proof.Circuits.DecompositionBitFields

/-! Reuse the accepted Boolean-field scan to decide canonical zero,
including an actual rewind from its cold local bank. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Scan
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Rewind.machine DecompositionBitFields.machine
def input (bits : List Bool) : Fin 4→List Bool := ![frame bits,[],[false],[]]
def output (bits : List Bool) : Fin 4→List Bool :=
  ![frame bits,DecompositionBitFields.stream bits,[DecompositionBitFields.present bits],
    List.replicate (4*bits.length+1) false]

theorem present_value (bits : List Bool) :
    DecompositionBitFields.present bits=decide (0<RadixSemantics.value bits) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change (b || DecompositionBitFields.present bits)=decide (0<(b.toNat+2*RadixSemantics.value bits))
    rw [ih]
    cases b <;> simp

theorem ready (bits : List Bool) : ReadyRun machine (8*bits.length+4) (input bits) (output bits) := by
  obtain ⟨base,hb,hf,hs⟩ := DecompositionBitFields.field_run [] bits [] [] false
  have hi : DecompositionBitFields.cfg 0 ([]++frame bits++[]) 0 [] false=
      initialConfiguration DecompositionBitFields.machine ![frame bits,[],[false]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [DecompositionBitFields.cfg,initialConfiguration]
  simp only [List.length_nil] at hb
  rw [hi] at hb
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace DecompositionBitFields.machine
    _ _ base hb 0
  have he : 2*base.steps+2=8*bits.length+4 := by rw [hs]; omega
  rw [he] at hr
  have hin : (Fin.addCases (m:=3) (n:=1) (motive:=fun _ : Fin 4 => List Bool)
      ![frame bits,[],[false]] (fun _ : Fin 1 => List.replicate 0 false))=input bits := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨r,hr,?_,hh,hsteps.trans he⟩
  funext i; fin_cases i
  · change r.final.tapes 0=frame bits
    have h := ht (0 : Fin 3)
    simpa [hf,DecompositionBitFields.cfg] using h
  · change r.final.tapes 1=DecompositionBitFields.stream bits
    have h := ht (1 : Fin 3)
    simpa [hf,DecompositionBitFields.cfg] using h
  · change r.final.tapes 2=[DecompositionBitFields.present bits]
    have h := ht (2 : Fin 3)
    simpa [hf,DecompositionBitFields.cfg] using h
  · change r.final.tapes 3=List.replicate (4*bits.length+1) false
    simpa [hs] using hc

end NearCubicWires.RepairOrdinary.EquationScalar.Scan
