import Proof.PCP.PCPPNativeQueryTail

/-! The single query-output negation reuses the larger, physically cleared
node workspace. Finite zero padding preserves its actual inner-capacity trace. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryTail
open LocalBitMultitape PCPPNativeAddressReusable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (F : ℕ) (i : Fin 24) := if i=0 ∨ i=1 ∨ i=20 ∨ i=22 then 0 else F
def paddedData (base index C F : ℕ) (out : List Bool) (i : Fin 24) : List Bool :=
  if i=0 then List.replicate base true else if i=1 then List.replicate index true
  else if i=20 then out else if i=22 then List.replicate C true else List.replicate F false
noncomputable def paddedEntry (base index C F : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,paddedData base index C F out⟩ : Configuration 24 _)

theorem padded_data (base index C F : ℕ) (out : List Bool) (hCF : C+1 ≤ F) :
    (fun i => ZeroPadding.pad (caps F i) (data base index C out i))=paddedData base index C F out := by
  funext i
  fin_cases i <;> simp [caps,data,paddedData,ZeroPadding.pad_zero,
    PCPPNativeNodeReusable.pad_zeros F C (by omega),PCPPNativeNodeReusable.pad_zeros F (C+1) hCF]

theorem padded_entry (base index C F : ℕ) (out : List Bool) (hCF : C+1 ≤ F) :
    ZeroPadding.config (caps F) (entry base index C out)=paddedEntry base index C F out := by
  apply configuration_ext
  · rfl
  · rfl
  · exact padded_data base index C F out hCF

theorem padded_run (base index C F : ℕ) (out : List Bool)
    (hC : PCPPNativeAddressAppend.budget base index+1 ≤ C) (hCF : C+1 ≤ F) :
    ∃ r,runFrom machine (budget base index C) (paddedEntry base index C F out)=some r ∧
      r.steps ≤ budget base index C ∧ r.final.heads=heads (out++emitted base index) ∧
      r.final.tapes=paddedData base index C F (out++emitted base index) := by
  obtain ⟨raw,hr,rs,rh,rt⟩ := node_run base index C out hC
  obtain ⟨r,run,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine (caps F) _ _ raw hr
  rw [padded_entry base index C F out hCF] at run
  refine ⟨r,run,by omega,?_,?_⟩
  · rw [hfinal]; exact rh
  · rw [hfinal]
    change (fun i => ZeroPadding.pad (caps F i) (raw.final.tapes i))=_
    rw [rt]
    exact padded_data base index C F (out++emitted base index) hCF

end NearCubicWires.RepairOrdinary.PCPPNativeQueryTail
