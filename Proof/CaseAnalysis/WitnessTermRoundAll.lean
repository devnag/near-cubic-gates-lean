import Proof.CaseAnalysis.WitnessTermEnvironment

/-! One total term result combines all three checked physical branches.
The only pending worker premise is the same full circuit call on the
retained payload and paid source/mode fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRoundAll
open LocalBitMultitape CanonicalWitnessCodec RadixSemantics CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def accepted (C : ℕ) (bits : List Bool) (circuitPass : Bool) :=
  (TermChoice.coefficient (natBitLength C) bits).isSome && circuitPass
def budget (P H C B circuitFuel : ℕ) (bits : List Bool) :=
  TermRead.budget C bits+circuitFuel+TermCommit.budget P B (natBitLength C)+2*H+13

theorem term_run {s : ℕ} (circuit : Machine 1703 s)
    (P H C B core W L circuitFuel : ℕ) (bits pre tail out native nativeWord : List Bool)
    (circuitPass : Bool) (a : Estimate) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hread : TermCoefficient.budget C bits+1 ≤ P)
    (hraw : 2*bits.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hstore : Store B a [] ambient) (ha : a.Valid B) (hb : natBitLength C ≤ B)
    (hcap : MassStep.budget B+1 ≤ P) (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity B+1 ≤ P)
    (worker : ∀ terms : Fin 725 → List Bool,
      terms 78=ZeroPadding.pad P (frame (TermCoefficient.circuitCode bits)) →
      terms 720=List.replicate P true →
      ∃ eh et result,runFrom (TermRound.programs circuit 1) circuitFuel
        (RecoveryCalls.restarted (TermRound.programs circuit 1)
          (TermRound.heads (pre.length+2*bits.length+1) out (TermEnvironment.heads native))
          (TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)))=some result ∧
        result.final.heads=TermRound.heads (pre.length+2*bits.length+1) out eh ∧
        result.final.tapes=TermRound.data P terms ambient out et ∧
        TermRound.heads (pre.length+2*bits.length+1) out eh 2527=0 ∧
        readTapeBit (TermRound.data P terms ambient out et 2527) 0=circuitPass ∧
        (circuitPass=true → eh=TermEnvironment.heads (native++nativeWord) ∧
          (∀ i : Fin 1703,TermCircuitReset.retained i →
            et (i.castAdd 2)=TermEnvironment.tapes H core W L (native++nativeWord) (i.castAdd 2)) ∧
          et 1703=List.replicate H true ∧ et 1704=List.replicate (H+1) false ∧
          (∀ i,(et ((TermCircuitReset.privateSlot i).castAdd 2)).length ≤ H))) :
    ∃ result,runFrom (TermRound.machine circuit) (budget P H C B circuitFuel bits)
      ⟨(TermRound.machine circuit).start,TermRound.heads pre.length out (TermEnvironment.heads native),
        TermRound.data P (TermRead.data P (natBitLength C) [] (pre++frame bits++tail) true) ambient out
          (TermEnvironment.tapes H core W L native)⟩=some result ∧
      result.steps ≤ budget P H C B circuitFuel bits ∧
      result.final.scanned 724=accepted C bits circuitPass ∧
      (accepted C bits circuitPass=true → ∃ next,
        result.final.heads=TermRound.heads (pre.length+2*bits.length+1)
          (out++TermRecord.word (natBitLength C) (TermChoice.rational (natBitLength C) bits))
          (TermEnvironment.heads (native++nativeWord)) ∧
        result.final.tapes=TermRound.data P
          (TermRead.data P (natBitLength C) [] (pre++frame bits++tail) true) next
          (out++TermRecord.word (natBitLength C) (TermChoice.rational (natBitLength C) bits))
          (TermEnvironment.tapes H core W L (native++nativeWord)) ∧
        Store B (CompetitorRationalNumerators.add a
          (Mass.magnitude (TermChoice.rational (natBitLength C) bits))) [] next) ∧
      (accepted C bits circuitPass=false → result.final.heads 724=0 ∧ result.final.tapes 724=[false]) := by
  let b := natBitLength C
  cases choice : TermChoice.coefficient b bits with
  | none =>
    have bad : ¬(PairHeader.valid bits ∧ ∃ q,
        decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
          natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b) := by
      intro h
      have hs := (TermChoice.coefficient_isSome b bits).mpr h
      rw [choice] at hs
      cases hs
    obtain ⟨r,hr,rs,rh,rt⟩ := TermRound.coefficient_reject_run circuit P C bits pre tail out ambient
      (TermEnvironment.heads native) (TermEnvironment.tapes H core W L native) hC hread hraw hwidth bad
    have bound : TermRead.budget C bits+2*P+9 ≤ budget P H C B circuitFuel bits := by
      dsimp only [budget,TermCommit.budget]
      omega
    have more := runFrom_moreFuel (TermRound.machine circuit) _
      (budget P H C B circuitFuel bits-(TermRead.budget C bits+2*P+9)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    have hf : accepted C bits circuitPass=false := by
      change ((TermChoice.coefficient b bits).isSome && circuitPass)=false
      simp only [choice,Option.isSome_none,Bool.false_and]
    refine ⟨r,more,rs.trans bound,?_,by simp only [hf,Bool.false_eq_true,IsEmpty.forall_iff],fun _=>⟨rh,rt⟩⟩
    rw [hf]
    change readTapeBit (r.final.tapes 724) (r.final.heads 724)=false
    rw [rh,rt];rfl
  | some q =>
    obtain ⟨hpair,hq,hqn,hqd⟩ := (TermChoice.coefficient_some b bits q).mp choice
    obtain ⟨terms,base,hr,_rs,rh,rt,bounds,width,extras,raw,flag,values,sign⟩ :=
      TermBegin.read_run P C bits pre tail out true ambient hC hread hraw hwidth
    have good : readTapeBit (terms 719) 0=true := flag.mpr ⟨hpair,q,hq,hqn,hqd⟩
    obtain ⟨q',hq',num,den,tn,td⟩ := values good
    have same : q'=q := Option.some.inj (hq'.symm.trans hq)
    subst q'
    let first := TapeEmbedding.receipt (TermEnvironment.heads native) (TermEnvironment.tapes H core W L native) base
    have firstRun := TapeEmbedding.run_embed TermBegin.machine (TermEnvironment.heads native)
      (TermEnvironment.tapes H core W L native) _ _ base hr
    have firstHeads : first.final.heads=TermRound.heads (pre.length+2*bits.length+1) out (TermEnvironment.heads native) := by
      change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) base.final.heads _=_
      rw [rh];rfl
    have firstTapes : first.final.tapes=TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native) := by
      change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) base.final.tapes _=_
      rw [rt];rfl
    have firstFlag : first.final.scanned 719=true := by
      change readTapeBit (first.final.tapes 719) (first.final.heads 719)=true
      rw [firstHeads,firstTapes]
      exact good
    obtain ⟨eh,et,w,hw,wh,wt,wch,wc,success⟩ := worker terms raw (extras 0)
    have workRun : runFrom (TermRound.programs circuit 1) circuitFuel
        (RecoveryCalls.restarted (TermRound.programs circuit 1) first.final.heads first.final.tapes)=some w := by
      rw [firstHeads,firstTapes]
      exact hw
    cases circuitPass with
    | false =>
      obtain ⟨r,hr,rs,rh,rt⟩ := TermRound.circuit_reject_run circuit (TermRead.budget C bits) circuitFuel
        _ first w firstRun workRun firstFlag P b (pre.length+2*bits.length+1) (pre++frame bits++tail)
        out terms ambient eh et wh wt wch wc (by omega) bounds width extras
      have bound : TermRead.budget C bits+circuitFuel+2*P+12 ≤ budget P H C B circuitFuel bits := by
        dsimp only [budget,TermCommit.budget]
        omega
      have more := runFrom_moreFuel (TermRound.machine circuit) _
        (budget P H C B circuitFuel bits-(TermRead.budget C bits+circuitFuel+2*P+12)) _ r hr
      rw [Nat.add_sub_of_le bound] at more
      have hf : accepted C bits false=false := Bool.and_false _
      refine ⟨r,more,rs.trans bound,?_,by simp only [hf,Bool.false_eq_true,IsEmpty.forall_iff],fun _=>⟨rh,rt⟩⟩
      rw [hf]
      change readTapeBit (r.final.tapes 724) (r.final.heads 724)=false
      rw [rh,rt];rfl
    | true =>
      obtain ⟨ehExact,keptFields,driver,log,scratch⟩ := success rfl
      subst eh
      obtain ⟨next,nextExtra,r,hr,rs,rh,rt,store,cleared,hd,hl,keep⟩ :=
        TermRound.accepted_run circuit (TermRead.budget C bits) circuitFuel _ first w firstRun workRun firstFlag
          P H B b (pre.length+2*bits.length+1) q a (TermCoefficient.coefficientCode bits)
          (pre++frame bits++tail) out terms ambient (TermEnvironment.heads (native++nativeWord)) et
          wh wt wch wc good hstore ha hb num den hq tn td sign width extras bounds hcap hbits hnative
          (TermEnvironment.reset_heads _ _ _) driver log scratch
      have restored : nextExtra=TermEnvironment.tapes H core W L (native++nativeWord) :=
        TermEnvironment.restored H core W L (native++nativeWord) et nextExtra keptFields cleared hd hl keep
      rw [restored] at rt
      have hrat := TermChoice.rational_eq b bits q choice
      have hf : accepted C bits true=true := by
        change ((TermChoice.coefficient b bits).isSome && true)=true
        simp only [choice,Option.isSome_some,Bool.and_self]
      refine ⟨r,hr,rs,?_,fun _=>?_,by simp only [hf,Bool.true_eq_false,IsEmpty.forall_iff]⟩
      · rw [hf]
        change readTapeBit (r.final.tapes 724) (r.final.heads 724)=true
        rw [rh,rt];rfl
      · rw [hrat]
        exact ⟨next,rh,rt,store⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRoundAll
