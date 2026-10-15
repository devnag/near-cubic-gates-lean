import Proof.CaseAnalysis.CaseTwoFieldReady
import Proof.PCP.PCPPQueryField

/-! Reuse the existing native field copier at a live output cursor. Its
source and scratch heads are physically rewound using paid reusable space. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeCopy
open LocalBitMultitape RepairRepresentation StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected : Fin 3→Bool:=![true,true,false]
def pads (C : ℕ) : Fin 3→ℕ:=![C,0,0]
def heads (out : List Bool) : Fin 4→ℕ:=![0,0,out.length,0]
def input (n C : ℕ) (out : List Bool) : Fin 4→List Bool:=
  ![ZeroPadding.pad C (natWord n),List.replicate C false,out,List.replicate C false]
def output (n C : ℕ) (out : List Bool) : Fin 4→List Bool:=
  ![ZeroPadding.pad C (natWord n),overlay (UnaryTemplate.tape (natBitLength n)) (List.replicate C false),
    out++natWord n,List.replicate C false]
noncomputable def machine:=MaskedReset.machine (PCPPQueryField.machine true) selected
def budget (n : ℕ):=4*natBitLength n+8

theorem append_run (n C : ℕ) (out : List Bool) (hC : 2*natBitLength n+3≤C) :
    ∃ r,runFrom machine (budget n) ⟨machine.start,heads out,input n C out⟩=some r ∧
      r.final.tapes=output n C out ∧ r.final.heads=heads (out++natWord n) ∧ r.steps=budget n := by
  obtain ⟨base,hr,hf,hs⟩:=PCPPQueryField.nat_run true [] [] (List.replicate C false) out n
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config (PCPPQueryField.machine true) (pads C) _ _ base hr
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run (PCPPQueryField.machine true) selected _ C _ p hp
    (by intro i hi;fin_cases i <;> first | rfl | contradiction)
    (by rw [ps,hs];exact hC)
  have hb : 2*p.steps+2=budget n:=by rw [ps,hs];unfold budget;omega
  rw [hb] at rr rs
  have hi : ZeroPadding.config (Rewind.Workspace.capacities 3 C)
      (Rewind.recording (ZeroPadding.config (pads C)
        (PCPPQueryField.cfg 0 ([]++natWord n++[]) 0 (List.replicate C false) 0 out)) 0)=
      (⟨machine.start,heads out,input n C out⟩ : Configuration 4 _):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,Rewind.Workspace.capacities,
        Rewind.recording,Rewind.config,PCPPQueryField.cfg,pads,input,Fin.addCases,ZeroPadding.pad]
  simp only [List.length_nil] at rr
  rw [hi] at rr
  refine ⟨r,rr,?_,?_,rs⟩
  · rw [rf]
    funext i
    fin_cases i
    · change p.final.tapes 0=_
      rw [pf,hf]
      simp [ZeroPadding.config,PCPPQueryField.payload,PCPPQueryField.cfg,pads,output]
    · change p.final.tapes 1=_
      rw [pf,hf]
      simp [ZeroPadding.config,PCPPQueryField.payload,PCPPQueryField.cfg,pads,output]
    · change p.final.tapes 2=_
      rw [pf,hf]
      simp [ZeroPadding.config,PCPPQueryField.payload,PCPPQueryField.cfg,pads,output,PCPPQueryField.selected]
    · rfl
  · rw [rf]
    funext i
    fin_cases i
    · rfl
    · rfl
    · change p.final.heads 2=_
      rw [pf,hf]
      rfl
    · rfl

theorem scratch_bound (n C : ℕ) (hC : 2*natBitLength n+3≤C) :
    (overlay (UnaryTemplate.tape (natBitLength n)) (List.replicate C false)).length≤C:=by
  rw [overlay_length,List.length_replicate]
  simp only [UnaryTemplate.tape,List.length_cons,List.length_append,List.length_replicate,List.length_nil]
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeCopy
