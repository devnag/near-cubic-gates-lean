import Proof.CaseAnalysis.RecoveryClauseLiteralState

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RecoveryBoundedClauseLiteralOutput (data graph heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalBudget (W C : ℕ):=32*C+32*W+128
theorem literal_budget (second neg : Bool) (before : List ℕ) (ref node W C : ℕ)
    (hb : before.length ≤ W) (href : ref ≤ W) (hn : node ≤ W)
    (hp : (RecoveryBoundedSelectorLoop.sourceWord before).length ≤ C) (hC : 16384*(W+1)^2 ≤ C) :
    RecoveryBoundedLiteralStream.budget second neg before ref node C ≤ literalBudget W C := by
  have hd:=RecoveryBoundedLiteralLoad.budget_bound before.length W C neg hb hC
  have hg:=RecoveryBoundedLiteralNode.budget_bound (RecoveryBoundedLiteral.kind second) ref 0 node W C href (Nat.zero_le _) hC
  unfold RecoveryBoundedLiteralStream.budget RecoveryBoundedLiteral.budget RecoveryBoundedClauseSelect.budget
    RecoveryBoundedClauseLookup.budget RecoveryBoundedClauseLookup.rawBudget literalBudget
  omega

theorem literal_run (H : Fin 71→ℕ) (A : Fin 71→List Bool) (node left right W C L : ℕ)
    (out pre source refs : List Bool) (h : State H A node left right C L out pre source refs)
    (second neg : Bool) (before : List ℕ) (ref : ℕ) (sourceTail refTail : List Bool)
    (hSource : source=pre++frame (RecoveryBoundedLiteralDriver.code before.length neg)++sourceTail)
    (hRefs : refs=RecoveryBoundedClauseLookup.source before ref refTail)
    (hLog : RecoveryBoundedClauseLookup.rawBudget before ref ≤ L)
    (hPrefix : (RecoveryBoundedSelectorLoop.sourceWord before).length ≤ C)
    (hb : before.length ≤ W) (href : ref ≤ W) (hn : node ≤ W)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    let bits:=RecoveryBoundedLiteralDriver.code before.length neg
    ∃ work r,runFrom (RecoveryBoundedLiteralStream.machine second) (literalBudget W C)
      ⟨(RecoveryBoundedLiteralStream.machine second).start,H,A⟩=some r ∧
      r.steps ≤ literalBudget W C ∧
      r.final.heads=heads H second neg ref out pre bits ∧
      r.final.tapes=data A second neg before ref node C out bits work ∧
      State r.final.heads r.final.tapes (node+neg.toNat) (nextLeft second neg left node ref)
        (nextRight second neg right node ref) C L (graph second neg ref out) (pre++frame bits) source refs := by
  have hlC : left ≤ C := by nlinarith [Nat.zero_le (W^2)]
  have hrC : right ≤ C := by nlinarith [Nat.zero_le (W^2)]
  have hnC : node+1 ≤ C := by nlinarith [Nat.zero_le (W^2)]
  have hfC : 2*ref+1 ≤ C := by nlinarith [Nat.zero_le (W^2)]
  obtain ⟨work,r,rr,rs,rh,rt,_flag,_index,hwork⟩:=RecoveryBoundedLiteralStream.stream_run second neg H A
    before ref node W C L out pre sourceTail refTail (reset_heads h second) (h.restoreA 3) (h.restoreA 4)
    (reset_bounds h second hlC hrC) h.sourceH (h.sourceA.trans hSource) (h.refsA.trans hRefs) h.logA
    (lookup_heads h) (literal_heads h second) (clean_gate h second) (replace_heads h second) (clean_replace h second)
    hLog hb href hC hnC
  have hc:=literal_budget second neg before ref node W C hb href hn hPrefix hC
  have more:=runFrom_moreFuel (RecoveryBoundedLiteralStream.machine second) _
    (literalBudget W C-RecoveryBoundedLiteralStream.budget second neg before ref node C) _ r rr
  rw [Nat.add_sub_of_le hc] at more
  refine ⟨work,r,more,rs.trans hc,rh,rt,?_⟩
  rw [rh,rt]
  exact literal_state H A node left right C L out pre source refs h second neg before ref
    (RecoveryBoundedLiteralDriver.code before.length neg) work hwork hPrefix hfC

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseState
