import Proof.CaseAnalysis.WitnessRationalNormalize

/-! The same normalization receipt retains the original signed numerator
tag. This projects its existing trace; it performs no second parsing pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalNormalize
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem retained_sign (b : ℕ) (bits : List Bool) (output : Fin 552→List Bool)
    (houtput : ClockJoin.ReadyRun machine (budget b bits) (input b bits) output) :
    output 166=frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits)):=by
  obtain ⟨c,hc,_,_,_,hSign,hnum,hden,_⟩:=RationalCold.fields_run bits
  have hc':=hc.focus old old_injective (input b bits) (by
    intro i
    simp only [input,old,RationalCold.input,Fin.val_castAdd,if_neg (show i.val≠539 by omega)]
    rfl)
  have hl:=(squeezed_run b (RationalCold.numerator bits)).focus leftSlots (by decide) (cbank b bits c)
    (left_input b bits c hnum)
  have hr:=(squeezed_run b (RationalCold.denominator bits)).focus rightSlots (by decide) (lbank b bits c)
    (right_input b bits c hden)
  obtain ⟨kr,hkr,krt,krh,krs⟩:=CompetitorWitnessKind.kind_ready (RationalCold.denominator bits)
  have hk:ClockJoin.ReadyRun CompetitorWitnessKind.machine (16*(RationalCold.denominator bits).length+27)
      (CompetitorWitnessKind.input (RationalCold.denominator bits)) (kindOutput bits):=⟨kr,hkr,krt,krh,krs.le⟩
  have hk':=hk.focus kindSlots (by decide) (rbank b bits c) (kind_input b bits c)
  have h1:=ClockJoin.join cold left _ _ _ _ _ hc' hl
  have h2:=ClockJoin.join first right _ _ _ _ _ h1 hr
  have h3:=ClockJoin.join second kind _ _ _ _ _ h2 hk'
  have hall:=ClockJoin.join third finish _ _ _ _ _ h3 (finish_run (kbank b bits c) (k_blank b bits c))
  obtain ⟨r,hr,rt,_,_⟩:=hall
  obtain ⟨s,hs,st,_,_⟩:=houtput
  have he:r=s:=Option.some.inj (hr.symm.trans hs)
  subst s
  rw [st.symm,rt]
  change kbank b bits c 166=_
  rw [kbank,install_other _ _ _ _ (by decide),rbank,install_other _ _ _ _ (by decide),
    lbank,install_other _ _ _ _ (by decide)]
  exact (c_old b bits c 166).trans hSign

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalNormalize
