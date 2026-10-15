import Proof.CaseAnalysis.RecoveryClauseLookup

/-! The selected actual framed query reference is copied to raw unary form.
The existing copier and recorded rewind restore every cursor and log. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLookup
open LocalBitMultitape GeneratedAmplifier RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readMachine:=Rewind.machine Copy.machine

theorem read_ready (node C L : ℕ) (hL : 2*node+1 ≤ L) :
    ClockJoin.ReadyRun readMachine (4*node+4)
      ![ZeroPadding.pad C (frame (List.replicate node true)),List.replicate C false,List.replicate L false]
      ![ZeroPadding.pad C (frame (List.replicate node true)),
        ZeroPadding.pad C (List.replicate node true),List.replicate L false] := by
  obtain ⟨p,hp,pf,ps⟩:=Copy.copy_run [] (List.replicate node true) [] []
  simp only [List.nil_append,List.append_nil,List.length_nil] at hp pf
  have hpInput : Copy.cfg 0 (frame (List.replicate node true)) 0 []=
      initialConfiguration Copy.machine ![frame (List.replicate node true),[]] := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  rw [hpInput] at hp
  obtain ⟨r,hr,rt,rl,rh,rs,_⟩:=Rewind.Workspace.reset_workspace Copy.machine _ _ p hp L
  have ht : 2*p.steps+2=4*node+4 := by rw [ps,List.length_replicate];omega
  rw [ht] at hr
  have hi : (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
      ![frame (List.replicate node true),[]] (fun _=>List.replicate L false))=
      (![frame (List.replicate node true),[],List.replicate L false] : Fin 3→List Bool) := by
    funext i;fin_cases i <;> rfl
  change run readMachine (4*node+4)
    (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
      ![frame (List.replicate node true),[]] (fun _=>List.replicate L false))=some r at hr
  rw [hi] at hr
  have he : r.final.tapes=![frame (List.replicate node true),List.replicate node true,List.replicate L false] := by
    funext i
    fin_cases i
    · exact (rt 0).trans (by rw [pf];rfl)
    · exact (rt 1).trans (by rw [pf];rfl)
    · change r.final.tapes ((0 : Fin 1).natAdd 2)=_
      rw [rl,ps,List.length_replicate,max_eq_left hL]
      rfl
  have ready : ClockJoin.ReadyRun readMachine (4*node+4)
      ![frame (List.replicate node true),[],List.replicate L false]
      ![frame (List.replicate node true),List.replicate node true,List.replicate L false] :=
    ⟨r,hr,he,rh,rs.le.trans ht.le⟩
  have padded:=PCPPairReusable.padded_ready _ _ _ ready (![C,C,0] : Fin 3→ℕ)
  have ho : (fun i=>ZeroPadding.pad ((![C,C,0] : Fin 3→ℕ) i)
      ((![frame (List.replicate node true),List.replicate node true,List.replicate L false] : Fin 3→List Bool) i))=
      ![ZeroPadding.pad C (frame (List.replicate node true)),ZeroPadding.pad C (List.replicate node true),List.replicate L false] := by
    funext i;fin_cases i
    · rfl
    · rfl
    · exact ZeroPadding.pad_zero _
  rw [ho] at padded
  convert padded using 1
  funext i;fin_cases i
  · rfl
  · rfl
  · exact (ZeroPadding.pad_zero _).symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLookup
