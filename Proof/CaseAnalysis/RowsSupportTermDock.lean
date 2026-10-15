import Proof.CaseAnalysis.RowsSupportTermLayout
import Proof.CaseAnalysis.RowsCircuitTermPorts

/-! A literal padded circuit receipt discharges the existing term-worker
call. No circuit copy, parser, serializer or additional reset is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape CloseoutWitness CloseoutRowsCircuitTermPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dock {s : ℕ} (circuit : Machine 1704 s) (P H core W L fuel pos : ℕ)
    (bits out native next supports nextSupport : List Bool) (passed : Bool)
    (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (hraw : terms 78=ZeroPadding.pad P (frame bits)) (hdriver : terms 720=List.replicate P true)
    (base : ExecutionReceipt 1704 s)
    (hr : runFrom circuit fuel ⟨circuit.start,Symmetric.heads native supports,
      Padding.input P H core W L bits native supports⟩=some base)
    (flagHead : base.final.heads 1700=0) (flag : readTapeBit (base.final.tapes 1700) 0=passed)
    (rawHead : base.final.heads 1=0) (raw : base.final.tapes 1=ZeroPadding.pad P (frame bits))
    (driverHead : base.final.heads 1694=0) (driver : base.final.tapes 1694=List.replicate P true)
    (good : passed=true →
      base.final.heads=Symmetric.heads (native++next) (supports++nextSupport) ∧
      base.final.tapes 1688=native++next ∧ base.final.tapes 1674=UnaryTemplate.tape core ∧
      base.final.tapes 1694=List.replicate P true ∧ base.final.tapes 1698=List.replicate W true ∧
      base.final.tapes 1699=List.replicate L true ∧ base.final.tapes 1=ZeroPadding.pad P (frame bits) ∧
      base.final.tapes 1703=supports++nextSupport ∧
      ∀ i : Fin 1703,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (base.final.tapes (i.castAdd 1)).length ≤ H) :
    ∃ eh et sh st result,runFrom (programs circuit 1) fuel
      (RecoveryCalls.restarted (programs circuit 1)
        (lift (TermRound.heads pos out (TermEnvironment.heads native)) supports.length)
        (lift (TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)) supports))=some result ∧
      result.final.heads=lift (TermRound.heads pos out eh) sh ∧ result.final.tapes=lift (TermRound.data P terms ambient out et) st ∧
      TermRound.heads pos out eh 2527=0 ∧ readTapeBit (TermRound.data P terms ambient out et 2527) 0=passed ∧
      (passed=true → eh=TermEnvironment.heads (native++next) ∧
        (∀ i : Fin 1703,TermCircuitReset.retained i →
          et (i.castAdd 2)=TermEnvironment.tapes H core W L (native++next) (i.castAdd 2)) ∧
        et 1703=List.replicate H true ∧ et 1704=List.replicate (H+1) false ∧
        sh=(supports++nextSupport).length ∧ st=supports++nextSupport ∧
        (∀ i,(et ((TermCircuitReset.privateSlot i).castAdd 2)).length ≤ H)) :=by
  let HH:=TermRound.heads pos out (TermEnvironment.heads native)
  let AA:=TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)
  have inputHeads:∀ i,HH (TermCircuitDock.slots i)=CloseoutRowsCircuitColdEntry.heads native i:=
    CloseoutRowsCircuitTermPorts.heads pos out native
  have inputTapes:∀ i,AA (TermCircuitDock.slots i)=CloseoutRowsCircuitPadding.input P H core W L bits native i:=
    tapes P H core W L bits out native terms ambient hraw hdriver
  have fullHeads:∀ i,lift HH supports.length (slots i)=Symmetric.heads native supports i:=by
    intro i
    refine Fin.addCases (m:=1703) (n:=1) ?_ ?_ i
    · intro j
      rw [slots_old]
      simpa only [lift,Symmetric.heads,Fin.addCases_left] using inputHeads j
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rfl
  have fullTapes:∀ i,lift AA supports (slots i)=Padding.input P H core W L bits native supports i:=by
    intro i
    refine Fin.addCases (m:=1703) (n:=1) ?_ ?_ i
    · intro j
      rw [slots_old]
      simpa only [lift,Padding.input,Fin.addCases_left] using inputTapes j
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rfl
  obtain ⟨r,rr,_rc,_rs,actualHeads,actualTapes,actualKeep⟩:=RecoveryFocus.dock slots slots_injective circuit fuel
    (lift HH supports.length) (lift AA supports) _ fullHeads fullTapes base hr
  let RH (i : Fin 2532):=r.final.heads (i.castAdd 1)
  let RT (i : Fin 2532):=r.final.tapes (i.castAdd 1)
  have rheads (i : Fin 1703):RH (TermCircuitDock.slots i)=base.final.heads (i.castAdd 1):=by
    change r.final.heads ((TermCircuitDock.slots i).castAdd 1)=_
    rw [←slots_old]
    exact actualHeads (i.castAdd 1)
  have rtapes (i : Fin 1703):RT (TermCircuitDock.slots i)=base.final.tapes (i.castAdd 1):=by
    change r.final.tapes ((TermCircuitDock.slots i).castAdd 1)=_
    rw [←slots_old]
    exact actualTapes (i.castAdd 1)
  have keep (i : Fin 2532) (hi : ∀ j,TermCircuitDock.slots j≠i) : RH i=HH i ∧ RT i=AA i:=by
    have kept:=actualKeep (i.castAdd 1) (old_away i hi)
    simpa only [RH,RT,lift,Fin.addCases_left] using kept
  have old (i : Fin 827):RH (i.castAdd 1705)=HH (i.castAdd 1705) ∧
      RT (i.castAdd 1705)=AA (i.castAdd 1705):=by
    by_cases h78:i.val=78
    · have he:i.castAdd 1705=TermCircuitDock.slots 1:=Fin.ext (by change i.val=78;exact h78)
      rw [he]
      exact ⟨(rheads 1).trans (rawHead.trans (inputHeads 1).symm),
        (rtapes 1).trans (raw.trans (inputTapes 1).symm)⟩
    by_cases h720:i.val=720
    · have he:i.castAdd 1705=TermCircuitDock.slots 1694:=Fin.ext (by change i.val=720;exact h720)
      rw [he]
      exact ⟨(rheads 1694).trans (driverHead.trans (inputHeads 1694).symm),
        (rtapes 1694).trans (driver.trans (inputTapes 1694).symm)⟩
    exact keep _ (TermCircuitDock.term_away i ⟨h78,h720⟩)
  let eh (i : Fin 1705):=RH (i.natAdd 827)
  let et (i : Fin 1705):=RT (i.natAdd 827)
  have endHeads:RH=TermRound.heads pos out eh:=by
    funext i
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
    · intro j
      simpa only [HH,TermRound.heads,Fin.addCases_left] using (old j).1
    · intro j
      simp only [TermRound.heads,Fin.addCases_right,eh]
  have endTapes:RT=TermRound.data P terms ambient out et:=by
    funext i
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
    · intro j
      simpa only [AA,TermRound.data,Fin.addCases_left] using (old j).2
    · intro j
      simp only [TermRound.data,Fin.addCases_right,et]
  have fullEndHeads:r.final.heads=lift (TermRound.heads pos out eh) (r.final.heads 2532):=by
    funext i
    refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ i
    · intro j
      simpa only [lift,Fin.addCases_left] using congrFun endHeads j
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rfl
  have fullEndTapes:r.final.tapes=lift (TermRound.data P terms ambient out et) (r.final.tapes 2532):=by
    funext i
    refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ i
    · intro j
      simpa only [lift,Fin.addCases_left] using congrFun endTapes j
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rfl
  refine ⟨eh,et,r.final.heads 2532,r.final.tapes 2532,r,rr,fullEndHeads,fullEndTapes,?_,?_,?_⟩
  · rw [←endHeads]
    exact (rheads 1700).trans flagHead
  · rw [←endTapes]
    exact (congrArg (fun tape=>readTapeBit tape 0) (rtapes 1700)).trans flag
  · intro hp
    obtain ⟨bh,bnative,bdomain,_bc,bW,bL,_br,supportTape,support⟩:=good hp
    have newHead (i : Fin 1703) : eh (i.castAdd 2)=TermEnvironment.heads (native++next) (i.castAdd 2):=by
      by_cases h1:i=1
      · subst i
        exact (keep _ (holes_away 1 (Or.inl rfl))).1
      by_cases hC:i=1694
      · subst i
        exact (keep _ (holes_away 1694 (Or.inr rfl))).1
      change RH (extra i)=_
      rw [←slot_extra i h1 hC,rheads,bh]
      simpa only [Symmetric.heads,Fin.addCases_left] using (environment_heads (native++next) i).symm
    have newHeads:eh=TermEnvironment.heads (native++next):=by
      funext i
      refine Fin.addCases (m:=1703) (n:=2) ?_ ?_ i
      · exact newHead
      · intro j
        fin_cases j
        · exact (keep _ (TermCircuitDock.reset_away 0)).1
        · exact (keep _ (TermCircuitDock.reset_away 1)).1
    have retained:∀ i : Fin 1703,TermCircuitReset.retained i →
        et (i.castAdd 2)=TermEnvironment.tapes H core W L (native++next) (i.castAdd 2):=by
      intro i hi
      rcases hi with h|h|h|h|h|h
      · have he:i=1:=Fin.ext h;subst i
        exact (keep _ (holes_away 1 (Or.inl rfl))).2
      · have he:i=1674:=Fin.ext h;subst i
        exact (rtapes 1674).trans bdomain
      · have he:i=1688:=Fin.ext h;subst i
        exact (rtapes 1688).trans bnative
      · have he:i=1694:=Fin.ext h;subst i
        exact (keep _ (holes_away 1694 (Or.inr rfl))).2
      · have he:i=1698:=Fin.ext h;subst i
        exact (rtapes 1698).trans bW
      · have he:i=1699:=Fin.ext h;subst i
        exact (rtapes 1699).trans bL
    refine ⟨newHeads,retained,(keep _ (TermCircuitDock.reset_away 0)).2,
      (keep _ (TermCircuitDock.reset_away 1)).2,?_,?_,?_⟩
    · change r.final.heads (slots 1703)=_
      rw [actualHeads,bh]
      rfl
    · change r.final.tapes (slots 1703)=_
      exact (actualTapes 1703).trans supportTape
    intro i
    let j:=TermCircuitReset.privateSlot i
    have hj:=TermCircuitReset.private_not_retained i
    have hn1:j≠1:=by intro he;exact hj (Or.inl (congrArg Fin.val he))
    have hn2:j≠1674:=by intro he;exact hj (Or.inr (Or.inl (congrArg Fin.val he)))
    have hn3:j≠1694:=by intro he;exact hj (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val he)))))
    have hn4:j≠1698:=by intro he;exact hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val he))))))
    have hn5:j≠1699:=by intro he;exact hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Fin.val he))))))
    have hn6:j≠1688:=by intro he;exact hj (Or.inr (Or.inr (Or.inl (congrArg Fin.val he))))
    change (RT (extra j)).length ≤ H
    rw [←slot_extra j hn1 hn3,rtapes]
    exact support j hn1 hn2 hn3 hn4 hn5 hn6

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
