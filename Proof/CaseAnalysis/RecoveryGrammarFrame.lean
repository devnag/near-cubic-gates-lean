import Proof.CaseAnalysis.RecoveryGrammarContinue
import Proof.MachineModel.OrdinaryRankScalar

/-! Produce each grammar prototype's unary field from its actual scalar.
The existing doubled-unary loop writes its payload; the existing fixed-word
writer adds its delimiter. The source is physically rewound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFrame
open LocalBitMultitape Composition RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def count : Machine 2 4:={PCPUnaryStackPush.raw with start:=1}
def slot : Fin 1→Fin 2:=fun _=>1
noncomputable def delimiter:=RecoveryFocus.machine slot (HierarchyFixedWord.raw [false])
noncomputable def raw:=Composition.machine count delimiter
def selected (i : Fin 2):=decide (i=0)
noncomputable def machine:=MaskedReset.machine raw selected
noncomputable def rawInput (n : ℕ) (out : List Bool):=
  (⟨raw.start,![0,out.length],![List.replicate n true,out]⟩ : Configuration 2 _)
noncomputable def input (n B : ℕ) (out : List Bool):=
  ZeroPadding.config (Rewind.Workspace.capacities 2 B) (Rewind.recording (rawInput n out) 0)

theorem raw_run (n : ℕ) (out : List Bool) :
    ∃ r,runFrom raw (2*n+3) (rawInput n out)=some r ∧ r.steps≤2*n+3 ∧
      r.final.heads=![n,(out++frame (List.replicate n true)).length] ∧
      r.final.tapes=![List.replicate n true,out++frame (List.replicate n true)] := by
  obtain ⟨p,pr,pf,ps⟩:=(PCPUnaryStackPush.count_loop n n 0 out (by omega)).run (by rfl)
  have pr' : runFrom count (2*n+1) (PCPUnaryStackPush.cfg 1 n 0 out)=some p := by
    rw [count,RankScalar.runFrom_start]
    exact pr
  let mid:=out++List.replicate (2*n) true
  obtain ⟨q,qr,qf,qs⟩:=RepairSource.ProjectionNormalization.Constants.write_run [false] mid
  obtain ⟨s,sr,_,ss,sh,st,skeep⟩:=RecoveryFocus.dock slot (by decide)
    (HierarchyFixedWord.raw [false]) 1 p.final.heads p.final.tapes
    (RepairSource.ProjectionNormalization.Constants.cfg [false] mid 0 (by omega))
    (by intro j;fin_cases j;rw [pf];rfl)
    (by intro j;fin_cases j;rw [pf];simp only [RepairSource.ProjectionNormalization.Constants.cfg,List.take_zero,List.append_nil];rfl) q qr
  have whole:=Composition.run_join count delimiter _ _ _ p s pr' sr
  have he : 2*n+1+1+1=2*n+3:=by omega
  rw [he] at whole
  refine ⟨joinedReceipt p s,whole,?_,?_,?_⟩
  · change p.steps+1+s.steps≤2*n+3
    have hs : s.steps=1:=ss.trans qs
    omega
  · change s.final.heads=_
    funext i;fin_cases i
    · change s.final.heads 0=n
      rw [(skeep 0 (by decide)).1,pf]
      rfl
    · change s.final.heads (slot 0)=_
      rw [sh 0,qf]
      change mid.length+1=(out++frame (List.replicate n true)).length
      rw [PCPUnaryStackPush.frame_unary]
      simp only [mid,List.length_append,List.length_replicate,List.length_singleton,Nat.add_assoc]
  · change s.final.tapes=_
    funext i;fin_cases i
    · change s.final.tapes 0=List.replicate n true
      rw [(skeep 0 (by decide)).2,pf]
      rfl
    · change s.final.tapes (slot 0)=_
      rw [st 0,qf]
      change mid++[false]=out++frame (List.replicate n true)
      rw [PCPUnaryStackPush.frame_unary]
      exact List.append_assoc _ _ _

theorem append_run (n B : ℕ) (out : List Bool) (hB : 2*n+4≤B) :
    ∃ r,runFrom machine (4*n+8) (input n B out)=some r ∧ r.steps≤4*n+8 ∧
      r.final.heads=![0,(out++frame (List.replicate n true)).length,0] ∧
      r.final.tapes=![List.replicate n true,out++frame (List.replicate n true),List.replicate B false] := by
  obtain ⟨p,pr,ps,ph,pt⟩:=raw_run n out
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run raw selected _ B _ p pr
    (by intro i hi;have he : i=0:=of_decide_eq_true hi;subst i;rfl) (by omega)
  have hb : 2*p.steps+2≤4*n+8:=by omega
  have more:=runFrom_moreFuel machine _ (4*n+8-(2*p.steps+2)) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,by omega,?_,?_⟩
  · rw [rf]
    funext i;fin_cases i
    · rfl
    · change p.final.heads 1=(out++frame (List.replicate n true)).length
      rw [ph]
      rfl
    · rfl
  · rw [rf]
    funext i;fin_cases i
    · change p.final.tapes 0=List.replicate n true
      rw [pt]
      rfl
    · change p.final.tapes 1=out++frame (List.replicate n true)
      rw [pt]
      rfl
    · rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFrame
