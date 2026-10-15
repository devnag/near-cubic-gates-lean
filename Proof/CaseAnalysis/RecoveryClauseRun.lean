import Proof.CaseAnalysis.RecoveryClauseOrOriginal
import Proof.CaseAnalysis.RecoveryClausePipeline

/-! The complete original clause: first literal, second literal, OR,
third literal, OR. One retained bank and the original shared query wires. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseRun
open LocalBitMultitape Composition SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedClauseState
open RecoveryBoundedClauseMeaning
open RecoveryBoundedLiteral (references)
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryBoundedClausePipeline.machine (RecoveryBoundedLiteralStream.machine false)
  (RecoveryBoundedLiteralStream.machine true) RecoveryBoundedClauseOr.machine
def budget (W C : ℕ):=5*literalBudget W C+4
def word {q : ℕ} (clause : Fin 3→Literal q):=
  frame (RepairSource.literalCode (clause 0)).bits++
  frame (RepairSource.literalCode (clause 1)).bits++
  frame (RepairSource.literalCode (clause 2)).bits

theorem clause_run {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q)
    (H : Fin 71→ℕ) (A : Fin 71→List Bool) (left right W C L : ℕ) (out pre source tail : List Bool)
    (h : State H A b.nodes.length left right C L out pre source (sourceWord (references values)))
    (hSource : source=pre++word clause++tail)
    (hFinal : (compileClause b values hv clause).compiled.final.nodes.length ≤ W)
    (hq : q ≤ W) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (hL : C+5*W+7 ≤ L) :
    let compiled:=compileClause b values hv clause
    ∃ result,runFrom machine (budget W C) ⟨machine.start,H,A⟩=some result ∧
      result.steps ≤ budget W C ∧
      State result.final.heads result.final.tapes compiled.compiled.final.nodes.length compiled.compiled.output.val
        (third b values hv clause).compiled.output.val C L
        (out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native) (pre++word clause)
        source (sourceWord (references values)) := by
  let x:=first b values hv clause
  let y:=second b values hv clause
  let z:=firstOr b values hv clause
  let t:=third b values hv clause
  let u:=lastOr b values hv clause
  have hu : u.final.nodes.length ≤ W:=hFinal
  have ht : t.compiled.final.nodes.length ≤ W:=u.extension.length_le.trans hu
  have hz : z.final.nodes.length ≤ W:=t.compiled.extension.length_le.trans ht
  have hy : y.compiled.final.nodes.length ≤ W:=z.extension.length_le.trans hz
  have hx : x.compiled.final.nodes.length ≤ W:=y.compiled.extension.length_le.trans hy
  have hb : b.nodes.length ≤ W:=x.compiled.extension.length_le.trans hx
  let c0:=frame (RepairSource.literalCode (clause 0)).bits
  let c1:=frame (RepairSource.literalCode (clause 1)).bits
  let c2:=frame (RepairSource.literalCode (clause 2)).bits
  let o1:=out++x.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let o2:=o1++y.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let o3:=o2++z.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let o4:=o3++t.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let o5:=o4++u.extension.suffix.flatMap PCPPRequestNodeSchema.native
  obtain ⟨_wx,rx,rxr,rxs,_rxh,_rxt,sx⟩:=RecoveryBoundedClauseLiteralOriginal.original_run b values hv (clause 0) false
    H A left right W C L out pre source (c1++c2++tail) h
    (by simpa only [word,List.append_assoc] using hSource) hb hq hl hr hC hL
  change State _ _ x.compiled.final.nodes.length x.compiled.output.val right C L o1 (pre++c0) source
    (sourceWord (references values)) at sx
  let v1:=liftLiveWires x.compiled.extension values
  have hv1 : v1.length=q:=by rw [liftLiveWires_length];exact hv
  have sx' : State rx.final.heads rx.final.tapes x.compiled.final.nodes.length x.compiled.output.val right C L
      o1 (pre++c0) source (sourceWord (references v1)) := by
    rw [references_lift]
    exact sx
  obtain ⟨_wy,ry,ryr,rys,_ryh,_ryt,sy⟩:=RecoveryBoundedClauseLiteralOriginal.original_run x.compiled.final v1 hv1
    (clause 1) true rx.final.heads rx.final.tapes x.compiled.output.val right W C L o1 (pre++c0) source (c2++tail) sx'
    (by simpa only [word,List.append_assoc] using hSource) hx hq (x.compiled.output.isLt.le.trans hx) hr hC hL
  change State _ _ y.compiled.final.nodes.length x.compiled.output.val y.compiled.output.val C L o2
    ((pre++c0)++c1) source (sourceWord (references v1)) at sy
  rw [references_lift] at sy
  obtain ⟨rz,rzr,rzs,sz⟩:=RecoveryBoundedClauseOrOriginal.original_run y.compiled.final
    (x.live.lift y.compiled.extension) y.live ry.final.heads ry.final.tapes W C L o2
    ((pre++c0)++c1) source (sourceWord (references values)) sy hy hC
  change State _ _ z.final.nodes.length z.output.val y.compiled.output.val C L o3 ((pre++c0)++c1)
    source (sourceWord (references values)) at sz
  let v2:=liftLiveWires (x.compiled.extension.trans (y.compiled.extension.trans z.extension)) values
  have hv2 : v2.length=q:=by rw [liftLiveWires_length];exact hv
  have sz' : State rz.final.heads rz.final.tapes z.final.nodes.length z.output.val y.compiled.output.val C L
      o3 ((pre++c0)++c1) source (sourceWord (references v2)) := by
    rw [references_lift]
    exact sz
  obtain ⟨_wt,rt,rtr,rts,_rth,_rtt,st⟩:=RecoveryBoundedClauseLiteralOriginal.original_run z.final v2 hv2
    (clause 2) true rz.final.heads rz.final.tapes z.output.val y.compiled.output.val W C L o3
    ((pre++c0)++c1) source tail sz' (by simpa only [word,List.append_assoc] using hSource)
    hz hq (z.output.isLt.le.trans hz) (y.compiled.output.isLt.le.trans hy) hC hL
  change State _ _ t.compiled.final.nodes.length z.output.val t.compiled.output.val C L o4
    (((pre++c0)++c1)++c2) source (sourceWord (references v2)) at st
  rw [references_lift] at st
  obtain ⟨ru,rur,rus,su⟩:=RecoveryBoundedClauseOrOriginal.original_run t.compiled.final
    (z.live.lift t.compiled.extension) t.live rt.final.heads rt.final.tapes W C L o4
    (((pre++c0)++c1)++c2) source (sourceWord (references values)) st ht hC
  change State _ _ u.final.nodes.length u.output.val t.compiled.output.val C L o5
    (((pre++c0)++c1)++c2) source (sourceWord (references values)) at su
  obtain ⟨result,rr,rs,rh,ra⟩:=RecoveryBoundedClausePipeline.clause_run
    (RecoveryBoundedLiteralStream.machine false) (RecoveryBoundedLiteralStream.machine true) RecoveryBoundedClauseOr.machine
    H A (literalBudget W C) rx ry rz rt ru rxr ryr rzr rtr rur
  refine ⟨result,rr,?_,?_⟩
  · unfold budget
    rw [rs]
    omega
  · rw [rh,ra]
    have hg : o5=out++(compileClause b values hv clause).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native := by
      rw [original_native]
      simp only [o5,o4,o3,o2,o1,x,y,z,t,u,List.append_assoc]
    have hp : ((pre++c0)++c1)++c2=pre++word clause := by simp only [word,c0,c1,c2,List.append_assoc]
    rw [hg,hp] at su
    exact su

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseRun
