import Proof.MachineModel.GeneratedAmplifierCopyReady
import Proof.CaseAnalysis.RecoverySelectorSchedule

/-! The selector reads one actual framed unary wire reference. The existing
raw field copier advances the source cursor, and its ordinary reset restores
the numeric output head; allocated zero tails remain reusable. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceRead
open LocalBitMultitape GeneratedAmplifier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool:=decide (i=1)
def machine:=MaskedReset.machine Copy.machine selected
def caps (C : ℕ) : Fin 3→ℕ:=![0,C,C]
def entry (pre tail : List Bool) (ref C : ℕ) :=
  ZeroPadding.config (caps C) (Rewind.recording
    (Copy.cfg 0 (pre++frame (List.replicate ref true)++tail) pre.length []) 0)

theorem read_run (pre tail : List Bool) (ref C : ℕ) (hC : 2*ref+1 ≤ C) : ∃ r,
    runFrom machine (4*ref+4) (entry pre tail ref C)=some r ∧
      r.final.heads=![pre.length+2*ref+1,0,0] ∧
      r.final.tapes=![pre++frame (List.replicate ref true)++tail,
        ZeroPadding.pad C (List.replicate ref true),List.replicate C false] ∧
      r.steps=4*ref+4 := by
  obtain ⟨a,ha,af,as⟩:=Copy.copy_run pre (List.replicate ref true) tail []
  have hh : ∀ i,selected i=true → a.final.heads i ≤ a.steps := by
    intro i hi
    have he : i=1 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    rw [af,as]
    change ([]++List.replicate ref true).length ≤ _
    simp
    omega
  obtain ⟨b,hb,bf,bs,_bp⟩:=MaskedReset.reset_run Copy.machine selected _ _ a ha hh
  obtain ⟨r,hr,rf,rs,_rp⟩:=ZeroPadding.run_config machine (caps C) _ _ b hb
  have time : 2*a.steps+2=4*ref+4 := by rw [as,List.length_replicate]; omega
  rw [time] at hr bs
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf,af]
    funext i
    fin_cases i <;>
      simp [ZeroPadding.config,SelectiveReset.finished,Rewind.config,selected,Copy.cfg,Fin.addCases]
  · rw [rf,bf,af]
    change (fun i=>ZeroPadding.pad (caps C i)
      (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
        ![pre++frame (List.replicate ref true)++tail,[]++List.replicate ref true]
        (fun _=>List.replicate a.steps false) i))=_
    rw [as,List.length_replicate]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad C (List.replicate (2*ref+1) false)=List.replicate C false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceRead
