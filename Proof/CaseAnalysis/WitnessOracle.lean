import Proof.CaseAnalysis.WitnessSource

/-! The complete cold source/oracle prefix has both physical early exits:
the machine-owned original-N cutoff precedes source construction, and the
actual R<=N comparison precedes cold oracle parsing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=ColdSource.tapes source k
def parser (k : ℕ):=ColdSource.old source k ∘ SelectedOracle.fields source k
def input (k : ℕ) (x bits : List Bool):=GuardedOracle.input (ColdSource.input source k x) bits
def first (k CH Cpad cutoff : ℕ) (code : List Bool):=
  RecoveryFocus.machine (@GuardedOracle.old (base source k)) (ColdSource.machine source k CH Cpad cutoff code)
def second (k : ℕ):=GuardedOracle.machine (parser source k) (ColdSource.extra source k 2)
def cutoffSlot (k : ℕ):=GuardedOracle.old (ColdSource.extra source k 6)
def lengthSlot (k : ℕ):=GuardedOracle.old (ColdSource.extra source k 2)
def sourceSlots (k : ℕ) (i : Fin (HierarchySelectedSource.tapes source k)):=GuardedOracle.old (ColdSource.old source k i)
def machine (k CH Cpad cutoff : ℕ) (code : List Bool):=
  CloseoutRowsGateColdPair.machine (first source k CH Cpad cutoff code) (second source k)
    (fun scanned=>scanned (cutoffSlot source k))
def budget (k CH Cpad cutoff : ℕ) (code x bits : List Bool):=
  ColdSource.budget source k CH Cpad cutoff code x+1+
    (if max 2 cutoff ≤ x.length then GuardedOracle.budget (SelectedOracle.width source k CH Cpad code x) x bits else 0)+1
def passed (k CH Cpad cutoff : ℕ) (code x bits : List Bool):=
  decide (max 2 cutoff ≤ x.length) && GuardedOracle.passed (SelectedOracle.width source k CH Cpad code x) x bits

private theorem old_injective (t : ℕ) : Function.Injective (@GuardedOracle.old t):=by
  intro a b h;exact Fin.ext (congrArg (fun z : Fin (GuardedOracle.tapes t)=>z.val) h)
private theorem initial_install {t : ℕ} (base : Fin t → List Bool) (bits : List Bool) (prior : Fin t → List Bool) :
    install (@GuardedOracle.old t) (GuardedOracle.input base bits) prior=GuardedOracle.input prior bits:=by
  funext i
  refine Fin.addCases (m:=t+4) (n:=1385) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=t) (n:=4) ?_ ?_ j
    · intro a
      change install (@GuardedOracle.old t) _ _ (GuardedOracle.old a)=_
      rw [install_slot _ (old_injective t)]
      simp only [GuardedOracle.input,OracleCall.input,NativeGuard.input,Fin.addCases_left]
    · intro a
      rw [install_other _ _ _ _ (by
        intro l h
        have hv:=congrArg (fun z : Fin (GuardedOracle.tapes t)=>z.val) h
        change l.val=t+a.val at hv;omega)]
      simp only [GuardedOracle.input,OracleCall.input,Fin.addCases_left,NativeGuard.input,Fin.addCases_right]
  · intro j
    rw [install_other _ _ _ _ (by
      intro l h
      have hv:=congrArg (fun z : Fin (GuardedOracle.tapes t)=>z.val) h
      change l.val=t+4+j.val at hv;omega)]
    simp only [GuardedOracle.input,OracleCall.input,Fin.addCases_right]

theorem oracle_run (k CH Cpad cutoff : ℕ) (code x bits : List Bool) (hpad : k+3 ≤ Cpad)
    (hcap : 16*bits.length ≤ x.length) :
    ∃ out,ClockJoin.ReadyRun (machine source k CH Cpad cutoff code)
      (budget source k CH Cpad cutoff code x bits) (input source k x bits) out ∧
      out (lengthSlot source k)=List.replicate x.length true ∧
      out (cutoffSlot source k)=[decide (max 2 cutoff ≤ x.length)] ∧
      readTapeBit (out (GuardedOracle.flagSlot (base source k))) 0=passed source k CH Cpad cutoff code x bits ∧
      (max 2 cutoff ≤ x.length →
        HierarchySelectedSource.Fields source k CH Cpad code x
          (out ∘ sourceSlots source k ∘ HierarchySelectedSource.old source k) ∧
        out (sourceSlots source k (HierarchySelectedSource.outputTape source k))=
          (source.output (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x))).word) ∧
      (max 2 cutoff ≤ x.length → SelectedOracle.width source k CH Cpad code x ≤ x.length →
        ∀ c : BooleanCircuit (SelectedOracle.width source k CH Cpad code x),
          decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value bits)=some c →
          out (GuardedOracle.descriptorSlot (base source k))=PCPPNative.descriptor c):=by
  obtain ⟨prior,hprior,rawN,cutoffFlag,sourceGood⟩:=ColdSource.source_run source k CH Cpad cutoff code x hpad
  have firstRun:=hprior.focus (@GuardedOracle.old (base source k)) (old_injective _) (input source k x bits) (by
    intro i
    simp only [input,GuardedOracle.input,GuardedOracle.old,OracleCall.input_old,NativeGuard.input,Fin.addCases_left])
  rw [input,initial_install] at firstRun
  have retained (i : Fin (base source k)) : GuardedOracle.input prior bits (GuardedOracle.old i)=prior i:=by
    simp only [GuardedOracle.input,GuardedOracle.old,OracleCall.input_old,NativeGuard.input,Fin.addCases_left]
  have flag:GuardedOracle.input prior bits (cutoffSlot source k)=[decide (max 2 cutoff ≤ x.length)]:=
    (retained _).trans cutoffFlag
  by_cases live:max 2 cutoff ≤ x.length
  · obtain ⟨fields,word⟩:=sourceGood live
    have hn:2 ≤ x.length:=(Nat.le_max_left 2 cutoff).trans live
    obtain ⟨out,secondRun,keep,_nativeFlag,verdict,descriptor⟩:=GuardedOracle.oracle_run (parser source k)
      (ColdSource.extra source k 2) (ColdSource.outside source k 2 _) prior
      (SelectedOracle.width source k CH Cpad code x) x bits fields.input fields.bitsR fields.rawR rawN hn hcap
    have joined:=CloseoutRowsGateColdPair.joined (first source k CH Cpad cutoff code) (second source k)
      (fun scanned=>scanned (cutoffSlot source k)) _ _ _ _ _ firstRun secondRun
      (by change readTapeBit (GuardedOracle.input prior bits (cutoffSlot source k)) 0=true
          rw [flag];simp [live,readTapeBit])
    refine ⟨out,?_,(keep _).trans rawN,(keep _).trans cutoffFlag,?_,?_,fun _=>descriptor⟩
    · simpa only [machine,budget,input,if_pos live] using joined
    · rw [verdict];simp only [passed,decide_eq_true live,Bool.true_and]
    · intro _
      have ret:out ∘ sourceSlots source k=prior ∘ ColdSource.old source k:=by funext i;exact keep _
      constructor
      · change HierarchySelectedSource.Fields source k CH Cpad code x
          ((out ∘ sourceSlots source k) ∘ HierarchySelectedSource.old source k)
        rw [ret];exact fields
      · exact (keep _).trans word
  · have rejected:=CloseoutRowsGateColdPair.rejected (first source k CH Cpad cutoff code) (second source k)
      (fun scanned=>scanned (cutoffSlot source k)) _ _ _ firstRun
      (by change readTapeBit (GuardedOracle.input prior bits (cutoffSlot source k)) 0=false
          rw [flag];simp [live,readTapeBit])
    refine ⟨_,ClockJoin.enlarge (machine source k CH Cpad cutoff code) _ _ _ _ rejected
      (by unfold budget;rw [if_neg live];omega),(retained _).trans rawN,flag,?_,fun h=>False.elim (live h),
      fun h=>False.elim (live h)⟩
    have blank:GuardedOracle.input prior bits (GuardedOracle.flagSlot (base source k))=[]:=by
      change OracleCall.input (NativeGuard.input prior) bits (OracleCall.extra (base source k+4) ⟨1379,by decide⟩)=[]
      rw [OracleCall.input_extra];rfl
    rw [blank];simp [passed,live,readTapeBit]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
