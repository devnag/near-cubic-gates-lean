import Proof.Amplification.RecoveryTseitinRun
import Proof.Hierarchy.CompetitorFieldEmit

/-! Any original three-literal clause is appended to a live formula stream.
The existing framed appender is shared with the scalar/PCP producers; its
output cursor is retained while every arithmetic head returns to zero. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinClauseAppend
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (position : Nat) : Fin 241→Nat := Fin.addCases (m:=239) (n:=2) (motive:=fun _=>Nat) (fun _ : Fin 239=>0) ![position,0]
def input (ambient : Fin 239→List Bool) (out : List Bool) (cap : Nat) : Fin 241→List Bool :=
  Fin.addCases (m:=239) (n:=2) (motive:=fun _=>List Bool) ambient ![out,List.replicate cap false]
noncomputable def firstMachine (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) := TapeEmbedding.machine 2 (kernel signs sources)
noncomputable def appendMachine := CompetitorFieldEmit.program (clauseSlot.castAdd 2) 239 240
noncomputable def emitMachine (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) := Composition.machine (firstMachine signs sources) appendMachine

theorem emit_run (cap log : Nat) (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) (indices : Fin 3→Nat)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hcap : capacity (Prepare.literals signs indices) ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1) (hi : ∀ k,ambient (Prepare.sourceSlot sources k)=RepairOrdinary.frame (indices k).bits++padding k) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom (emitMachine signs sources) (20*cap+4)
        ⟨(emitMachine signs sources).start,heads out.length,input ambient out cap⟩=some r ∧
      r.final.heads=heads (out++RepairOrdinary.frame (Encodable.encode (clause (Prepare.literals signs indices))).bits).length ∧
      r.final.tapes=input after (out++RepairOrdinary.frame (Encodable.encode (clause (Prepare.literals signs indices))).bits) cap ∧
      (∀ i : Fin 239,i.val<3 → after i=ambient i) ∧
      after 3=List.replicate cap true ∧ after 4=List.replicate (cap+1) false ∧
      Bounded cap after ∧ r.steps ≤ 20*cap+4 := by
  obtain ⟨after,baseReady,hclause,hkeep,hdriver,hlog,hbound⟩ := clause_run cap log signs sources indices ambient padding hcap hb hd hl hz hi
  obtain ⟨base,hr,bt,bh,bs⟩ := baseReady
  let eh : Fin 2→Nat := ![out.length,0]
  let et : Fin 2→List Bool := ![out,List.replicate cap false]
  let first := TapeEmbedding.receipt eh et base
  have hfirst := TapeEmbedding.run_embed (kernel signs sources) eh et _ _ base hr
  have fh : first.final.heads=heads out.length := by
    funext i
    refine Fin.addCases (m:=239) (n:=2) (fun j=>?_) (fun j=>?_) i
    · simpa only [first,TapeEmbedding.receipt_heads_old,heads,Fin.addCases_left] using bh j
    · simp only [first,TapeEmbedding.receipt_heads_new,heads,Fin.addCases_right,eh]
  have ft : first.final.tapes=input after out cap := by
    funext i
    refine Fin.addCases (m:=239) (n:=2) (fun j=>?_) (fun j=>?_) i
    · simp only [first,TapeEmbedding.receipt_tapes_old,bt,input,Fin.addCases_left]
    · simp only [first,TapeEmbedding.receipt_tapes_new,input,Fin.addCases_right,et]
  have hsize : 2*(Encodable.encode (clause (Prepare.literals signs indices))).bits.length+1 ≤ cap := by
    have h := hbound clauseSlot (by decide)
    rw [hclause,ZeroPadding.pad_length,frame_length] at h
    omega
  obtain ⟨last,hlast,lh,lt,ls⟩ := CompetitorFieldEmit.field_run (clauseSlot.castAdd 2) 239 240
    (by decide) (by decide) (by decide) (Encodable.encode (clause (Prepare.literals signs indices))).bits out cap
    first.final.heads first.final.tapes
    (by rw [fh]; rfl) (by rw [fh]; rfl) (by rw [fh]; rfl)
    (by rw [ft]; exact hclause) (by rw [ft]; rfl) (by rw [ft]; rfl) hsize
  have hall := Composition.run_join (firstMachine signs sources) appendMachine _ _ _ first last hfirst hlast
  have htime : 16*cap+1+(4*(Encodable.encode (clause (Prepare.literals signs indices))).bits.length+3) ≤ 20*cap+4 := by omega
  have hmore := runFrom_moreFuel (emitMachine signs sources) _
    (20*cap+4-(16*cap+1+(4*(Encodable.encode (clause (Prepare.literals signs indices))).bits.length+3))) _ _ hall
  rw [Nat.add_sub_of_le htime] at hmore
  refine ⟨after,_,hmore,?_,?_,hkeep,hdriver,hlog,hbound,?_⟩
  · change last.final.heads=_
    rw [lh,fh]
    funext i
    refine Fin.addCases (m:=239) (n:=2) (fun j=>?_) (fun j=>?_) i
    · have hn : (j.castAdd 2 : Fin 241)≠239 := by intro he; have hv:=congrArg Fin.val he; have hj:=j.isLt; change j.val=239 at hv; omega
      simp [Function.update_of_ne hn,heads]
    · fin_cases j <;> rfl
  · change last.final.tapes=_
    rw [lt,ft]
    funext i
    refine Fin.addCases (m:=239) (n:=2) (fun j=>?_) (fun j=>?_) i
    · have hn : (j.castAdd 2 : Fin 241)≠239 := by intro he; have hv:=congrArg Fin.val he; have hj:=j.isLt; change j.val=239 at hv; omega
      simp [Function.update_of_ne hn,input]
    · fin_cases j <;> rfl
  · change base.steps+1+last.steps ≤ 20*cap+4
    omega

end NearCubicWires.RepairSource.RecoveryTseitinClauseAppend
