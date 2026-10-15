import Proof.CaseAnalysis.RowsCircuitGuarded
import Proof.CaseAnalysis.RowsCircuitNativePrepare
import Proof.CaseAnalysis.RowsCircuitBottomEntry

/-! Paid native header/top publication and one physical positioning move
produce the exact original counted-bottom entry at the frozen circuit ABI. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPreparedRun
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuit CloseoutRowsCircuitBottomDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (threshold : Bool):=CloseoutRowsGateColdPair.machine CloseoutRowsCircuitNativePrepare.machine
  (CloseoutRowsCircuitBottomPosition.machine threshold) (fun _=>true)
def budget (C retained : ℕ) (top : List Bool):=CloseoutRowsCircuitNativePrepare.budget C retained top+3

theorem new_heads (threshold : Bool) (out next : List Bool) (D : ℕ) :
    Function.update (CloseoutRowsCircuitBottomEntry.heads threshold out D 0) 1688 next.length=
      CloseoutRowsCircuitBottomEntry.heads threshold next D 0:=by
  funext i
  by_cases hi:i=1688
  · subst i;rw [Function.update_self];rfl
  · rw [Function.update_of_ne hi]
    simp only [CloseoutRowsCircuitBottomEntry.heads,if_neg hi]

theorem blank_from_gate (C : ℕ) (A : Fin 1703 → List Bool)
    (blank : ∀ j,A (CloseoutRowsCircuitAllocate.gate j)=List.replicate C false)
    (i : Fin 1703) (hi : 639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674) : A i=List.replicate C false:=by
  let j:Fin 1048:=⟨if i.val<1674 then i.val-639 else i.val-640,by split_ifs <;> omega⟩
  have he:CloseoutRowsCircuitAllocate.gate j=i:=by
    apply Fin.ext
    rw [CloseoutRowsCircuitAllocate.gate_val]
    dsimp only [j]
    split_ifs <;> omega
  rw [←he];exact blank j

theorem prepared_run (threshold : Bool) (C core count retained D : ℕ)
    (top out source members : List Bool) (A : Fin 1703 → List Bool)
    (hc : 1 ≤ C) (hn : retained ≤ C) (hheader : EquationHeaderAppend.budget retained+1 ≤ C)
    (hbits : 2*top.length+1 ≤ C)
    (small : ∀ j,(A (CloseoutRowsCircuitAllocate.gate j)).length ≤ C)
    (hdriver : A 1694=List.replicate C true) (hlog : A 1695=List.replicate (C+1) false)
    (hretained : A 1702=ZeroPadding.pad C (List.replicate retained true))
    (htop : A 1701=ZeroPadding.pad C (frame top)) (hnative : A 1688=out)
    (hscratch : A 1696=List.replicate C false) (hcount : A 624=UnaryTemplate.tape count)
    (fields : ∀ i : Fin 7,A (![1689,1690,297,1692,1693,1697,1674] i)=
      (![List.replicate D true,[],source,members,[true],ZeroPadding.pad C [true],UnaryTemplate.tape core] : Fin 7 → List Bool) i) : ∃ B r,
    runFrom (machine threshold) (budget C retained top)
      ⟨(machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out D 0,A⟩=some r ∧
      r.steps ≤ budget C retained top ∧
      r.final.heads=CloseoutRowsCircuitBottomPosition.output
        (CloseoutRowsCircuitBottomEntry.heads threshold (out++natWord retained++frame top) D 0) ∧
      r.final.tapes=B ∧
      (∀ i,B (bottomSlots i)=localTapes C core count (out++natWord retained++frame top) source members D 0 true i) ∧
      (∀ i,(i.val<639 ∨ 1687 < i.val ∨ i.val=1674) → i≠1694 → i≠1695 → i≠1688 → i≠1696 → B i=A i):=by
  let H:=CloseoutRowsCircuitBottomEntry.heads threshold out D 0
  obtain ⟨B,first,hfirst,fs,fh,ft,native,scratch,driver,log,blank,keep⟩:=CloseoutRowsCircuitNativePrepare.prepare_run
    C retained top out H A hn hheader hbits (by
      intro j
      have hv:=CloseoutRowsCircuitGateErase.slots_val j
      dsimp only [H,CloseoutRowsCircuitBottomEntry.heads]
      split_ifs <;> first | rfl | (split_ifs at hv <;> omega)) small
    (by constructor;rfl;constructor;rfl;constructor;rfl;rfl) hdriver hlog hretained htop hnative hscratch
  let next:=out++natWord retained++frame top
  have head: first.final.heads=CloseoutRowsCircuitBottomEntry.heads threshold next D 0:=
    fh.trans (new_heads threshold out next D)
  obtain ⟨last,hl,lh,lt,_ls⟩:=CloseoutRowsCircuitBottomPosition.position_run threshold
    (CloseoutRowsCircuitBottomEntry.heads threshold next D 0) B rfl rfl
  have lr:runFrom (CloseoutRowsCircuitBottomPosition.machine threshold) 1
      (RecoveryCalls.restarted (CloseoutRowsCircuitBottomPosition.machine threshold) first.final.heads first.final.tapes)=some last:=by
    rw [head,ft];exact hl
  obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.accepted CloseoutRowsCircuitNativePrepare.machine
    (CloseoutRowsCircuitBottomPosition.machine threshold) (fun _=>true) _ 1 H A first last hfirst lr rfl
  have time:CloseoutRowsCircuitNativePrepare.budget C retained top+1+1+1=budget C retained top:=by unfold budget;omega
  rw [time] at hr rs
  refine ⟨B,r,hr,rs,rh.trans lh,rt.trans lt,?_,keep⟩
  apply CloseoutRowsCircuitBottomEntry.tapes_ready C core count next source members D 0 true B hc
    (blank_from_gate C B blank)
  · exact (keep 1674 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 6)
  · intro i;fin_cases i
    · exact native
    · exact (keep 1689 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 0)
    · exact (keep 1690 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 1)
    · exact (keep 297 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 2)
    · exact (keep 1692 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 3)
    · exact (keep 1693 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 4)
    · exact driver
    · exact log
    · exact scratch
    · exact (keep 1697 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fields 5)
  · exact (keep 624 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPreparedRun
