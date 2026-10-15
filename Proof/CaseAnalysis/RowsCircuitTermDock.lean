import Proof.CaseAnalysis.RowsCircuitTermPorts

/-! A literal padded circuit receipt discharges the existing term-worker
call. No circuit copy, parser, serializer or additional reset is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermDock
open LocalBitMultitape CloseoutWitness CloseoutRowsCircuitTermPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dock {s : ℕ} (circuit : Machine 1703 s) (P H core W L fuel pos : ℕ)
    (bits out native next : List Bool) (passed : Bool)
    (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (hraw : terms 78=ZeroPadding.pad P (frame bits)) (hdriver : terms 720=List.replicate P true)
    (base : ExecutionReceipt 1703 s)
    (hr : runFrom circuit fuel ⟨circuit.start,CloseoutRowsCircuitColdEntry.heads native,
      CloseoutRowsCircuitPadding.input P H core W L bits native⟩=some base)
    (flagHead : base.final.heads 1700=0) (flag : readTapeBit (base.final.tapes 1700) 0=passed)
    (rawHead : base.final.heads 1=0) (raw : base.final.tapes 1=ZeroPadding.pad P (frame bits))
    (driverHead : base.final.heads 1694=0) (driver : base.final.tapes 1694=List.replicate P true)
    (good : passed=true →
      base.final.heads=CloseoutRowsCircuitColdEntry.heads (native++next) ∧
      base.final.tapes 1688=native++next ∧ base.final.tapes 1674=UnaryTemplate.tape core ∧
      base.final.tapes 1694=List.replicate P true ∧ base.final.tapes 1698=List.replicate W true ∧
      base.final.tapes 1699=List.replicate L true ∧ base.final.tapes 1=ZeroPadding.pad P (frame bits) ∧
      ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (base.final.tapes i).length ≤ H) :
    ∃ eh et result,runFrom (TermRound.programs circuit 1) fuel
      (RecoveryCalls.restarted (TermRound.programs circuit 1)
        (TermRound.heads pos out (TermEnvironment.heads native))
        (TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)))=some result ∧
      result.final.heads=TermRound.heads pos out eh ∧ result.final.tapes=TermRound.data P terms ambient out et ∧
      TermRound.heads pos out eh 2527=0 ∧ readTapeBit (TermRound.data P terms ambient out et 2527) 0=passed ∧
      (passed=true → eh=TermEnvironment.heads (native++next) ∧
        (∀ i : Fin 1703,TermCircuitReset.retained i →
          et (i.castAdd 2)=TermEnvironment.tapes H core W L (native++next) (i.castAdd 2)) ∧
        et 1703=List.replicate H true ∧ et 1704=List.replicate (H+1) false ∧
        (∀ i,(et ((TermCircuitReset.privateSlot i).castAdd 2)).length ≤ H)):=by
  let HH:=TermRound.heads pos out (TermEnvironment.heads native)
  let AA:=TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)
  have inputHeads:∀ i,HH (TermCircuitDock.slots i)=CloseoutRowsCircuitColdEntry.heads native i:=heads pos out native
  have inputTapes:∀ i,AA (TermCircuitDock.slots i)=CloseoutRowsCircuitPadding.input P H core W L bits native i:=
    tapes P H core W L bits out native terms ambient hraw hdriver
  obtain ⟨r,rr,_rc,_rs,rheads,rtapes,keep⟩:=RecoveryFocus.dock TermCircuitDock.slots
    TermCircuitDock.slots_injective circuit fuel HH AA _ inputHeads inputTapes base hr
  have old (i : Fin 827):r.final.heads (i.castAdd 1705)=HH (i.castAdd 1705) ∧
      r.final.tapes (i.castAdd 1705)=AA (i.castAdd 1705):=by
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
  let eh (i : Fin 1705):=r.final.heads (i.natAdd 827)
  let et (i : Fin 1705):=r.final.tapes (i.natAdd 827)
  have endHeads:r.final.heads=TermRound.heads pos out eh:=by
    funext i
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
    · intro j
      simpa only [HH,TermRound.heads,Fin.addCases_left] using (old j).1
    · intro j
      simp only [TermRound.heads,Fin.addCases_right,eh]
  have endTapes:r.final.tapes=TermRound.data P terms ambient out et:=by
    funext i
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ i
    · intro j
      simpa only [AA,TermRound.data,Fin.addCases_left] using (old j).2
    · intro j
      simp only [TermRound.data,Fin.addCases_right,et]
  refine ⟨eh,et,r,rr,endHeads,endTapes,?_,?_,?_⟩
  · rw [←endHeads]
    exact (rheads 1700).trans flagHead
  · rw [←endTapes]
    exact (congrArg (fun tape=>readTapeBit tape 0) (rtapes 1700)).trans flag
  · intro hp
    obtain ⟨bh,bnative,bdomain,_bc,bW,bL,_br,support⟩:=good hp
    have newHead (i : Fin 1703) : eh (i.castAdd 2)=TermEnvironment.heads (native++next) (i.castAdd 2):=by
      by_cases h1:i=1
      · subst i
        exact (keep _ (holes_away 1 (Or.inl rfl))).1
      by_cases hC:i=1694
      · subst i
        exact (keep _ (holes_away 1694 (Or.inr rfl))).1
      change r.final.heads (extra i)=_
      rw [←slot_extra i h1 hC,rheads,bh]
      exact (environment_heads (native++next) i).symm
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
      (keep _ (TermCircuitDock.reset_away 1)).2,?_⟩
    intro i
    let j:=TermCircuitReset.privateSlot i
    have hj:=TermCircuitReset.private_not_retained i
    have hn1:j≠1:=by intro he;exact hj (Or.inl (congrArg Fin.val he))
    have hn2:j≠1674:=by intro he;exact hj (Or.inr (Or.inl (congrArg Fin.val he)))
    have hn3:j≠1694:=by intro he;exact hj (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val he)))))
    have hn4:j≠1698:=by intro he;exact hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val he))))))
    have hn5:j≠1699:=by intro he;exact hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Fin.val he))))))
    have hn6:j≠1688:=by intro he;exact hj (Or.inr (Or.inr (Or.inl (congrArg Fin.val he))))
    change (r.final.tapes (extra j)).length ≤ H
    rw [←slot_extra j hn1 hn3,rtapes]
    exact support j hn1 hn2 hn3 hn4 hn5 hn6

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermDock
