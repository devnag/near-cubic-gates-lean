import Proof.CaseAnalysis.RowsCircuitBottomFinish

/-! Only the original top bitmap selects threshold bottom requests. The
symmetric mode takes every bottom. Both branches retain the same scratch,
and every executed call/return is charged by the existing controller. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def halt : Machine 1059 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
theorem halt_run (hh : Fin 1059→ℕ) (tt : Fin 1059→List Bool) : ReadyAt halt 0 hh tt tt := by
  refine ⟨⟨⟨0,hh,tt⟩,0,_⟩,rfl,rfl,rfl,by rfl⟩
def retention (threshold : Bool) (scanned : Fin 1059→Bool) : Bool:=if threshold then scanned 1053 else true
def kept (threshold : Bool) (membership : List Bool) (memberPos : ℕ) : Bool:=
  if threshold then readTapeBit membership memberPos else true
def keptOutput (keep : Bool) (bits out : List Bool):=if keep then out++frame bits else out
def keptWires (keep : Bool) (support wireCount : ℕ):=if keep then wireCount+(support+1) else wireCount
noncomputable def choice (threshold : Bool):=CloseoutRowsGateColdPair.machine halt selected (retention threshold)
def choiceBudget (bits : List Bool) (support : ℕ):=((4*bits.length+3)+1+(2*(support+1)+6))+2

theorem retention_eq (threshold : Bool) (cap core pos memberPos : ℕ) (out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (tapes : Fin 1059→List Bool)
    (hs : Stored cap core out source membership description wireCount flag tapes) :
    retention threshold (fun i=>readTapeBit (tapes i) (heads pos memberPos out description wireCount i))=
      kept threshold membership memberPos := by
  cases threshold
  · rfl
  · change readTapeBit (tapes 1053) memberPos=readTapeBit membership memberPos
    have hm:tapes 1053=membership:=hs.extra 4
    rw [hm]

theorem choice_run (threshold : Bool) (cap core pos memberPos support : ℕ)
    (bits out source membership : List Bool) (description wireCount : ℕ) (flag : Bool)
    (tapes : Fin 1059→List Bool) (hs : Stored cap core out source membership description wireCount flag tapes)
    (hn : tapes 1033=ZeroPadding.pad cap (frame bits))
    (hw : tapes 1047=ZeroPadding.pad cap (List.replicate support true))
    (hbits : 2*bits.length+1 ≤ cap) (hwire : support+1+2 ≤ cap) : ∃ r,
    runFrom (choice threshold) (choiceBudget bits support)
      ⟨(choice threshold).start,heads pos memberPos out description wireCount,tapes⟩=some r ∧
      r.steps ≤ choiceBudget bits support ∧
      r.final.heads=heads pos memberPos (keptOutput (kept threshold membership memberPos) bits out)
        description (keptWires (kept threshold membership memberPos) support wireCount) ∧
      (∀ i,r.final.tapes (coreSlots i)=tapes (coreSlots i)) ∧
      Stored cap core (keptOutput (kept threshold membership memberPos) bits out) source membership
        description (keptWires (kept threshold membership memberPos) support wireCount) flag r.final.tapes := by
  have test:=retention_eq threshold cap core pos memberPos out source membership description wireCount flag tapes hs
  cases hk:kept threshold membership memberPos with
  | false =>
    have stopped:=CloseoutRowsGatePairHeads.rejected halt selected (retention threshold) 0
      (heads pos memberPos out description wireCount) tapes tapes (halt_run _ _) (test.trans hk)
    have enlarged:=enlarge _ 1 (choiceBudget bits support) _ _ _ stopped (by unfold choiceBudget;omega)
    obtain ⟨r,hr,rt,rh,rs⟩:=enlarged
    refine ⟨r,hr,rs,?_,?_,?_⟩
    · simpa only [hk,keptOutput,keptWires,Bool.false_eq_true,if_false] using rh
    · intro i;rw [rt]
    · simpa only [rt,hk,keptOutput,keptWires,Bool.false_eq_true,if_false] using hs
  | true =>
    obtain ⟨base,hb,bh,bt,_bs⟩:=selected_run cap core pos memberPos support bits out source membership
      description wireCount flag tapes hs hn hw hbits hwire
    obtain ⟨r,hr,rt,rh,rs⟩:=CloseoutRowsGateSourceCalls.joined halt selected (retention threshold) 0 _
      (heads pos memberPos out description wireCount) tapes tapes (halt_run _ _) base hb (test.trans hk)
    refine ⟨r,?_,?_,?_,?_,?_⟩
    · have he:0+1+((4*bits.length+3)+1+(2*(support+1)+6))+1=choiceBudget bits support:=by
        unfold choiceBudget;omega
      rw [he] at hr
      exact hr
    · unfold choiceBudget;omega
    · rw [rh,bh]
      simp only [keptOutput,keptWires,if_true]
    · intro i
      rw [rt,bt,Function.update_of_ne (show coreSlots i≠(1051 : Fin 1059) from core_other 2 i),
        Function.update_of_ne (show coreSlots i≠(1049 : Fin 1059) from core_other 0 i)]
    · rw [rt,bt]
      simpa only [hk,keptOutput,keptWires,if_true] using hs.selected (out++frame bits) (wireCount+(support+1))

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
