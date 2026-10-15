import Proof.CaseAnalysis.RecoveryGrammarRoom

/-! Coarse C.12 room absorbs all original atom costs, including packet
production, wrapper reset, reference save, erasure, and reload. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def atomBudget (B : ℕ):=128*(B+2)

theorem Runs.more {s u v B P : ℕ} {p : Machine 112 s} {source : List Bool}
    {cold : Fin 33→List Bool} {a b : RowState}
    (h : Runs p u B P source cold a b) (hu : u≤v) : Runs p v B P source cold a b := by
  obtain ⟨r,rr,rs,rh,rt⟩:=h
  have more:=runFrom_moreFuel p u (v-u) _ r rr
  rw [show u+(v-u)=v by omega] at more
  exact ⟨r,more,rs.trans hu,rh,rt⟩

theorem Room.atom_budget {W C D L S B P q bound row : ℕ}
    (h : Room W C D L S B P) (hs : ScalarFits q bound row W)
    (p : Selection) (u ref : ℕ) (hu : u≤B) (hr : ref≤W) :
    preparedBudget C (rowIndex q bound row p.index) p.value.val (rowLimit q bound p.limit)
      (rowUpper q row p.upper) B ((2*(u+2)+2)+1+
        RecoveryBoundedGrammarAfter.budget ref B (selectedFields p q bound row C))≤atomBudget B := by
  have hi:=hs.index p.index
  have hl:=hs.limit p.limit
  have hx:=hs.upper p.upper
  have hv : p.value.val≤W:=by have hh:=p.value.isLt;have h6:=hs.value;omega
  have hp:=(h.packet_fits hs p).2.2.2.2.2.2
  have load:=RecoveryBoundedRowReload.budget_bound (selectedFields p q bound row C) B hp
  have hb:=h.packet
  have hw:=h.wB
  unfold preparedBudget refreshBudget RecoveryBoundedGrammarPrototype.readyBudget
  rw [RecoveryBoundedGrammarPrototype.budget_eq]
  unfold RecoveryBoundedGrammarAfter.budget atomBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
