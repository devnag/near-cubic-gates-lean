import Proof.CaseAnalysis.RecoveryUniversalGateMeaning

/-! The forward tag-reference appender reuses a C-backed destination as
well as its already checked scalar, frame and rewind workspaces. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagReferenceAppend
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 7):=if i=4 then C else 0
def paddedData (n P C : ℕ) (out : List Bool) (i : Fin 7):=
  if i=4 then ZeroPadding.pad C out else data n P C out false i

theorem pad_data (n P C : ℕ) (out : List Bool) :
    (fun i=>ZeroPadding.pad (caps C i) (data n P C out false i))=paddedData n P C out := by
  funext i
  by_cases hi : i=4
  · subst i;rfl
  · simp only [caps,paddedData,if_neg hi,ZeroPadding.pad_zero]

theorem padded_run (n P C : ℕ) (out : List Bool) (hC : 2*n+1 ≤ C) :
    ∃ r,runFrom machine (budget n C) ⟨machine.start,heads out,paddedData n P C out⟩=some r ∧
      r.steps ≤ budget n C ∧ r.final.heads=heads (out++frame (List.replicate n true)) ∧
      r.final.tapes=paddedData n P C (out++frame (List.replicate n true)) := by
  obtain ⟨p,hp,ps,ph,pt⟩:=reference_run n P C out hC
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config machine (caps C) _ _ p hp
  have hi : ZeroPadding.config (caps C) (⟨machine.start,heads out,data n P C out false⟩ : Configuration 7 _)=
      (⟨machine.start,heads out,paddedData n P C out⟩ : Configuration 7 _) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact pad_data n P C out
  rw [hi] at hr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    change p.final.heads=_
    exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps C i) (p.final.tapes i))=_
    rw [pt,pad_data]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagReferenceAppend
