import Proof.CaseAnalysis.CaseTwoSystematicBit
import Proof.PCP.PCPPNativeTemplateRaw

/-! Charge the selected variable template's one-cell query positioning before
the original support call. The systematic branch starts with that template at
head zero, as the actual unsigned-variable producer returns it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SystematicReady
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 5→Fin 13:=![5,0,1,2,4]
def shift:=RecoveryFocus.machine slots (PCPPNativeTemplateRaw.shift .right)
def machine:=Composition.machine shift SystematicBit.machine
def heads (i : Fin 13):=if i=3 then 1 else 0

theorem bit_run (a : RepairRepresentation.PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (i : Fin (a.output r).systematicBits) : ∃ out,
    runFrom machine (1+1+SystematicBit.budget a r)
      ⟨machine.start,heads,SystematicBit.data a r u i.val⟩=some out ∧
      out.steps≤1+1+SystematicBit.budget a r ∧
      out.final.tapes 11=[parityOn ((a.output r).systematicSupport i) u]:=by
  let data:=SystematicBit.data a r u i.val
  obtain ⟨s,hs,sf,ss⟩:=PCPPNativeTemplateRaw.shift_run .right
    (fun j=>heads (slots j)) (fun j=>data (slots j))
  obtain ⟨first,hfirst,_,fs,fh,ft,keep⟩:=RecoveryFocus.dock slots (by decide)
    (PCPPNativeTemplateRaw.shift .right) 1 heads data _ (by intro j;rfl) (by intro j;rfl) s hs
  have tapes:first.final.tapes=data:=by
    funext j
    by_cases h : ∃ k,slots k=j
    · obtain ⟨k,rfl⟩:=h
      rw [ft,sf]
    · exact (keep j (by intro k hk;exact h ⟨k,hk⟩)).2
  have position:first.final.heads=SystematicBit.heads:=by
    funext j
    by_cases h : ∃ k,slots k=j
    · obtain ⟨k,rfl⟩:=h
      rw [fh,sf]
      fin_cases k <;>rfl
    · rw [(keep j (by intro k hk;exact h ⟨k,hk⟩)).1]
      have h5 : j≠5:=by intro he;subst j;exact h ⟨0,rfl⟩
      fin_cases j <;>first | rfl | contradiction
  obtain ⟨last,hl,ls,bit⟩:=SystematicBit.bit_run a r u i
  have hi : Composition.restart first.final SystematicBit.machine.start=
      (⟨SystematicBit.machine.start,SystematicBit.heads,data⟩ : Configuration 13 _):=by
    apply configuration_ext
    · rfl
    · exact position
    · exact tapes
  rw [←hi] at hl
  have whole:=Composition.run_join shift SystematicBit.machine _ _ _ first last hfirst hl
  exact ⟨_,whole,by change first.steps+1+last.steps≤_;rw [fs,ss];omega,bit⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SystematicReady
