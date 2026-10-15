import Proof.Hierarchy.CompetitorThresholdPrepared

/-! Complete actual threshold tail: print the fixed rational, physically
clear the scalar workspace, then compare the retained exact sum. Both
validity upper tests and the acceptance midpoint lower test use this tail. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decisionTail (lower : Bool) := Composition.machine clearProgram (decisionProgram lower)
noncomputable def machine (lower : Bool) (k : ℕ) (q : ℚ) :=
  Composition.machine (constantsProgram k q) (decisionTail lower)
def budget (b k : ℕ) := CompetitorThresholdConstants.budget b k+2*capacity b+2000*(b+1)^2+6

theorem tail_run (lower : Bool) (b k pos : ℕ) (q : ℚ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (hs : Fin 110 → ℕ) (ambient : Fin 110 → List Bool)
    (hstore : Store b a source (project ambient))
    (hheads : ∀ i,hs (native i)=heads pos i)
    (hfreshHeads : ∀ i : Fin 110,95 ≤ i.val → hs i=0)
    (hfresh : ∀ i : Fin 110,95 ≤ i.val → ambient i=[])
    (ha : a.Valid b) (hq : 0≤q) (hk : k≤b)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) :
    ∃ r,runFrom (machine lower k q) (budget b k)
        (RecoveryCalls.restarted (machine lower k q) hs ambient)=some r ∧
      r.steps≤budget b k ∧ r.final.heads=hs ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔
        CompetitorThresholdDecision.passes lower a.positive a.negative a.denominator q) := by
  obtain ⟨first,constants,hfirst,hfs,hfh,hft,hproject,hnum,hzero,hden⟩ := constants_run b k pos q a source
    hs ambient hstore hheads hfreshHeads hfresh hk hp hd
  have hconstantStore : Store b a source (project constants) := by rw [hproject]; exact hstore
  obtain ⟨clear,hclear,hcs,hch,hct⟩ := clear_run b pos a source hs constants hconstantStore hheads
  have hpow : 2^k≤(2:ℕ)^b := Nat.pow_le_pow_right (by decide) hk
  obtain ⟨last,hlast,hls,hlh,hflag⟩ := decision_run lower b pos q a source hs constants
    hconstantStore hheads hfreshHeads hnum hzero hden ha hq (hp.trans_le hpow) (hd.trans_le hpow)
  have heLast : Composition.restart clear.final (decisionProgram lower).start=
      RecoveryCalls.restarted (decisionProgram lower) hs (cleaned b constants) := by
    apply configuration_ext
    · rfl
    · exact hch
    · exact hct
  have hlast' : runFrom (decisionProgram lower) (2000*(b+1)^2)
      (Composition.restart clear.final (decisionProgram lower).start)=some last := by rw [heLast]; exact hlast
  have htail := Composition.run_join clearProgram (decisionProgram lower) _ _ _ clear last hclear hlast'
  let tail := Composition.joinedReceipt clear last
  have heTail : Composition.restart first.final (decisionTail lower).start=
      Composition.leftConfig _ (RecoveryCalls.restarted clearProgram hs constants) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have htail' : runFrom (decisionTail lower) ((2*capacity b+4)+1+2000*(b+1)^2)
      (Composition.restart first.final (decisionTail lower).start)=some tail := by rw [heTail]; exact htail
  have hall := Composition.run_join (constantsProgram k q) (decisionTail lower) _ _ _ first tail hfirst htail'
  have hcost : CompetitorThresholdConstants.budget b k+1+((2*capacity b+4)+1+2000*(b+1)^2)=budget b k := by
    unfold budget
    omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first tail,hall,?_,hlh,hflag⟩
  change first.steps+1+(clear.steps+1+last.steps)≤budget b k
  omega

end NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
