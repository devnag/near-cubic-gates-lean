import Proof.CaseAnalysis.RowsCircuitBottomChecked

/-! One total bottom round loads the actual next field, runs the public
decoder, conditionally publishes its native request, folds validity, clears
the reusable gate scratch, and advances the original support cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem joined {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (h h' h'' : Fin t→ℕ) (d d' d'' : Fin t→List Bool)
    (first : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p fp ⟨p.start,h,d⟩=some first)
    (ph : first.final.heads=h') (pt : first.final.tapes=d') (ps : first.steps≤fp)
    (hq : runFrom q fq ⟨q.start,h',d'⟩=some last)
    (qh : last.final.heads=h'') (qt : last.final.tapes=d'') (qs : last.steps≤fq) :
    ∃ r,runFrom (Composition.machine p q) (fp+1+fq) ⟨(Composition.machine p q).start,h,d⟩=some r ∧
      r.steps≤fp+1+fq ∧ r.final.heads=h'' ∧ r.final.tapes=d'':=by
  have he:Composition.restart first.final q.start=⟨q.start,h',d'⟩:=configuration_ext rfl ph pt
  have hlast:runFrom q fq (Composition.restart first.final q.start)=some last:=by rw [he];exact hq
  refine ⟨Composition.joinedReceipt first last,Composition.run_join p q fp fq _ first last hp hlast,?_,qh,qt⟩
  change first.steps+1+last.steps≤fp+1+fq
  omega

noncomputable def loaded (threshold : Bool):=Composition.machine loader (checked threshold)
noncomputable def round (threshold : Bool):=Composition.machine (loaded threshold) finish

theorem round_run (threshold : Bool) (cap core memberPos : ℕ)
    (bits out pre tail membership : List Bool) (description wireCount : ℕ) (flag : Bool)
    (hin : 2*bits.length+1 ≤ cap) (hcap : 2*CloseoutRowsGateMeasured.budget bits+4 ≤ cap) :
    ∃ result,runFrom (round threshold) (12*cap+30)
      (cfg (round threshold).start cap core pre.length memberPos [] out
        (pre++frame bits++tail) membership description wireCount flag)=some result ∧
      result.steps ≤ 12*cap+30 ∧
      result.final.heads=heads (pre.length+2*bits.length+1) (memberPos+2)
        (out++emitted core (kept threshold membership memberPos) bits)
        (description+descriptionCost core bits)
        (wireCount+wireCost core (kept threshold membership memberPos) bits) ∧
      result.final.tapes=data cap core []
        (out++emitted core (kept threshold membership memberPos) bits)
        (pre++frame bits++tail) membership (description+descriptionCost core bits)
        (wireCount+wireCost core (kept threshold membership memberPos) bits) (flag && passed core bits):=by
  let source:=pre++frame bits++tail
  let position:=pre.length+2*bits.length+1
  let output:=out++emitted core (kept threshold membership memberPos) bits
  let desc:=description+descriptionCost core bits
  let wires:=wireCount+wireCost core (kept threshold membership memberPos) bits
  obtain ⟨l,hlrun,ls,lh,lt⟩:=load_run cap core memberPos bits out pre tail membership description wireCount flag hin
  obtain ⟨p,hprun,ps,ph,pflag,pstore⟩:=checked_run threshold cap core position memberPos bits out source membership
    description wireCount flag hin hcap
  obtain ⟨lp,hlp,lps,lph,lpt⟩:=joined loader (checked threshold) (4*bits.length+3) (7*cap+12)
    (heads pre.length memberPos out description wireCount)
    (heads position memberPos out description wireCount) (heads position memberPos output desc wires)
    (data cap core [] out source membership description wireCount flag)
    (data cap core bits out source membership description wireCount flag) p.final.tapes
    l p hlrun lh lt ls.le hprun ph rfl ps
  obtain ⟨f,hfrun,fh,ft,fs⟩:=finish_run cap core position memberPos output source membership desc wires flag p.final.tapes
    (by omega) pstore
  rw [pflag] at ft
  obtain ⟨result,hall,rs,rh,rt⟩:=joined (loaded threshold) finish (4*bits.length+3+1+(7*cap+12)) (2*cap+10)
    (heads pre.length memberPos out description wireCount)
    (heads position memberPos output desc wires) (heads position (memberPos+2) output desc wires)
    (data cap core [] out source membership description wireCount flag) p.final.tapes
    (data cap core [] output source membership desc wires (flag && passed core bits))
    lp f hlp lph lpt lps hfrun fh ft fs.le
  have ht:(4*bits.length+3+1+(7*cap+12))+1+(2*cap+10) ≤ 12*cap+30:=by omega
  have more:=runFrom_moreFuel (round threshold) _
    (12*cap+30-((4*bits.length+3+1+(7*cap+12))+1+(2*cap+10))) _
    result hall
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨result,more,rs.trans ht,rh,rt⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
