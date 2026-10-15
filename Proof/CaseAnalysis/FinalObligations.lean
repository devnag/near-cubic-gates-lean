import Proof.CaseAnalysis.Assembly
import Proof.CaseAnalysis.HardnessPair
import Proof.CaseAnalysis.CommonProgramCertificate
import Proof.CaseAnalysis.CommonCutoff
import Proof.CaseAnalysis.WeakSelectedRuntime
import Proof.CaseAnalysis.WitnessWeakMachine

/-! The exact remaining obligations of paper Theorem 2.5, at one fixed gamma.

`thm:main-fixed` fixes gamma first and then chooses the error/degree/copy
constants, the hierarchy level and clock, and one weak machine serving BOTH
classes at that gamma. `ClosureAt` follows that order literally: supplying one
`ClosureAt sources gamma` for every gamma in (0,1/2) yields the literal theorem.

Every field is a restatement of a premise that an already accepted consumer
demands. No new paper premise is introduced here. -/
namespace NearCubicWires.RepairSource.CloseoutFinal

open CloseoutLanguage Closeout CloseoutWeakRuntime SelectedRecoveryIntegration
open RepairOrdinary.CloseoutWitness SourceInterfaces RepairOrdinary
open RepairRepresentation CircuitRestriction

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- Dyadic sampled completeness at the meaning level. Identical to
`CloseoutLanguage.SampledCompleteness` except that the conclusion
`M.accepts (2^s) input` is replaced by the existential that
`Weak.accepts_exact` converts into it. -/
def Completeness (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (meaning : (n : Nat) → BitInput n → List Bool → Prop)
    (degree copies clauseDegree : Nat) (delta : ℚ)
    (family : SizedFunctionFamily) (logExponent : Nat) (cap : ℝ) : Prop :=
  ∃ onset, ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
    ∀ hsmall : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input,
    let oracle := (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
    let request := CloseoutWitnessPolicy.request sources k clock input oracle
    let pcpp := (selectedPCPP sources).output request
    let cb := clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s))
    ∀ hc : pcpp.clauseBits ≤ cb,
    SampledXorSum family delta (request.arity+cb+1) copies
      ⌊wireScale cap logExponent ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊
      (paddedUnsigned pcpp hc) →
    ∃ w : BitInput (2^s/16), meaning (2^s) input (List.ofFn w)

/-- The runtime split: literally the `bound` premise of `selected_littleO`. -/
def RuntimeSplit (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (M : OrdinaryWeakMachine)
    (A B a sigma : Nat) (hot : Nat → Nat) : Prop :=
  ∃ onset, ∀ N, onset ≤ N →
    M.runtime N ≤ A*(N+1)^a+hot N ∧
    hot N*((outer sources k clock).result.pcp.nativeWidth N)^sigma ≤
      B*2^((outer sources k clock).result.pcp.nativeWidth N)

/-- Everything chosen after one fixed gamma, in the paper's order. -/
structure ClosureAt (sources : EightSources) (gamma : ℝ) where
  degree : Nat
  copies : Nat
  clauseDegree : Nat
  delta : ℚ
  symCap : ℝ
  thrCap : ℝ
  hdegree : 17*sources.amplification.stvExponent ≤ degree
  hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies
  hD : 1 ≤ clauseDegree
  clauses : ClauseReady sources degree clauseDegree
  hd : 0 < delta
  hh : delta < 1/2
  heps : xorEpsilon (delta : ℝ) copies < gamma
  hsym : 0 < symCap
  hthr : 0 < thrCap
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  tapes : Nat
  states : Nat
  worker : LocalBitMultitape.Machine tapes states
  htapes : 2 ≤ tapes
  result : Fin tapes
  fuel : Nat → Nat
  meaning : (n : Nat) → BitInput n → List Bool → Prop
  supplier : Weak.AllInputRun worker htapes result fuel meaning
  sound : ∀ n (x : BitInput n) (bits : List Bool), meaning n x bits →
    (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.timedView.accepts n x = true
  complSym : Completeness sources k clock meaning degree copies clauseDegree delta
    symmetricWireFamily 5 symCap
  complThr : Completeness sources k clock meaning degree copies clauseDegree delta
    thresholdWireFamily 9 thrCap
  A : Nat
  B : Nat
  a : Nat
  sigma : Nat
  hot : Nat → Nat
  ha : a ≤ k+1
  hsigma : 6+(fixedProjection sources).degrees.proofLog ≤ sigma
  split : RuntimeSplit sources k clock
    (Weak.machine worker htapes result fuel meaning supplier) A B a sigma hot

namespace ClosureAt

variable {sources : EightSources} {gamma : ℝ} (c : ClosureAt sources gamma)

/-- The one weak machine for both classes at this gamma. -/
def M : OrdinaryWeakMachine :=
  Weak.machine c.worker c.htapes c.result c.fuel c.meaning c.supplier

def factor : Nat := 3*(c.copies*(2*c.clauseDegree+2))+2
def symC : ℝ := headlineCoefficient c.symCap c.factor
def thrC : ℝ := headlineCoefficient c.thrCap c.factor

theorem littleO : OrdinaryLittleO c.M (fun n => n^(c.k+2)) :=
  selected_littleO sources c.k c.clock c.M c.A c.B c.a c.sigma c.hot c.ha c.hsigma c.split

theorem oneSided : ∀ n (x : BitInput n), c.M.accepts n x →
    (sources.hierarchy (fun n => n^(c.k+2)) c.clock).hierarchy.timedView.accepts n x = true :=
  Weak.one_sided c.worker c.htapes c.result c.fuel c.meaning c.supplier
    (fun n x => (sources.hierarchy (fun n => n^(c.k+2)) c.clock).hierarchy.timedView.accepts n x = true)
    c.sound

/-- Meaning-level completeness becomes the consumer's `SampledCompleteness`
through `Weak.accepts_exact`. -/
theorem sampled (family : SizedFunctionFamily) (e : Nat) (cap : ℝ)
    (h : Completeness sources c.k c.clock c.meaning c.degree c.copies c.clauseDegree c.delta family e cap) :
    SampledCompleteness sources c.k c.clock c.M c.degree c.copies c.clauseDegree c.delta family e cap := by
  obtain ⟨onset,hon⟩ := h
  refine ⟨onset,?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb hc sample
  exact (Weak.accepts_exact c.worker c.htapes c.result c.fuel c.meaning c.supplier
    (2^s) input).mpr (hon s hs input hsmall hc sample)

/-- The onset is produced by `exists_certificate` and consumed by
`hardness_pair`, so both cuts describe the SAME language. -/
theorem selected (hg : 0 < gamma) (_hh : gamma < 1/2) :
    ∃ onset,
      Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
        (language sources c.k c.clock c.M c.degree c.copies c.clauseDegree onset)) ∧
      0 < c.symC ∧ 0 < c.thrC ∧ ∃ start, ∀ n, start ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          (circuit.wireCount : ℝ) ≤ wireScale c.symC 5 n →
          agreement circuit.eval
            (language sources c.k c.clock c.M c.degree c.copies c.clauseDegree onset n) < 1/2+gamma) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          (circuit.wireCount : ℝ) ≤ wireScale c.thrC 9 n →
          agreement circuit.eval
            (language sources c.k c.clock c.M c.degree c.copies c.clauseDegree onset n) < 1/2+gamma) := by
  obtain ⟨cutoff,_,_⟩ :=
    live_clause_fit sources c.degree c.copies c.clauseDegree c.clauses
  obtain ⟨onset,_,cert⟩ :=
    CloseoutCommonProgram.exists_certificate sources c.k c.clock c.degree c.clauseDegree
      c.copies cutoff c.hD c.clauses c.hcopies c.M c.littleO
  refine ⟨onset,cert,?_⟩
  exact hardness_pair sources c.k c.clock c.M c.littleO c.oneSided
    c.degree c.copies c.clauseDegree onset c.hdegree c.hcopies c.clauses
    c.delta c.hd c.hh gamma hg c.heps c.symCap c.thrCap c.hsym c.hthr
    (c.sampled symmetricWireFamily 5 c.symCap c.complSym)
    (c.sampled thresholdWireFamily 9 c.thrCap c.complThr)

/-- The selected language at this gamma. -/
def lang (hg : 0 < gamma) (hh : gamma < 1/2) : Language :=
  language sources c.k c.clock c.M c.degree c.copies c.clauseDegree
    (Classical.choose (c.selected hg hh))

end ClosureAt

/-- Per-gamma supply is exactly what the literal theorem needs. -/
def Supply (sources : EightSources) : Type :=
  ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 → ClosureAt sources gamma

variable {sources : EightSources}

def langOf (s : Supply sources) (gamma : ℝ) : Language := by
  classical
  exact if h : 0 < gamma ∧ gamma < 1/2 then (s gamma h.1 h.2).lang h.1 h.2 else fun _ _ => false

def symOf (s : Supply sources) (gamma : ℝ) : ℝ := by
  classical
  exact if h : 0 < gamma ∧ gamma < 1/2 then (s gamma h.1 h.2).symC else 1

def thrOf (s : Supply sources) (gamma : ℝ) : ℝ := by
  classical
  exact if h : 0 < gamma ∧ gamma < 1/2 then (s gamma h.1 h.2).thrC else 1

theorem localSuppliers_of_supply (s : Supply sources) : LocalSuppliers := by
  classical
  refine ⟨langOf s,symOf s,thrOf s,?_,?_,?_⟩
  · intro gamma hg hh
    have hl : langOf s gamma = (s gamma hg hh).lang hg hh := dif_pos ⟨hg,hh⟩
    rw [hl]
    exact (Classical.choose_spec ((s gamma hg hh).selected hg hh)).1
  · intro gamma hg hh
    have hl : langOf s gamma = (s gamma hg hh).lang hg hh := dif_pos ⟨hg,hh⟩
    have hc : symOf s gamma = (s gamma hg hh).symC := dif_pos ⟨hg,hh⟩
    obtain ⟨_,hsym,_,start,hstart⟩ := Classical.choose_spec ((s gamma hg hh).selected hg hh)
    rw [hl,hc]
    exact ⟨hsym,start,fun n hn circuit hw => (hstart n hn).1 circuit hw⟩
  · intro gamma hg hh
    have hl : langOf s gamma = (s gamma hg hh).lang hg hh := dif_pos ⟨hg,hh⟩
    have hc : thrOf s gamma = (s gamma hg hh).thrC := dif_pos ⟨hg,hh⟩
    obtain ⟨_,_,hthr,start,hstart⟩ := Classical.choose_spec ((s gamma hg hh).selected hg hh)
    rw [hl,hc]
    exact ⟨hthr,start,fun n hn circuit hw => (hstart n hn).2 circuit hw⟩

/-- THE LITERAL ENDPOINT, conditional on one per-gamma supply. -/
theorem theorem25_of_supply (supply : (sources : EightSources) → Supply sources)
    (sources : EightSources) : OrdinaryHeadlineTheorem25 :=
  Closeout.from_local_suppliers (fun s => localSuppliers_of_supply (supply s)) sources

end
end NearCubicWires.RepairSource.CloseoutFinal
