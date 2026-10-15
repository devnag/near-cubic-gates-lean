import Proof.Gates.Main.Application
import Proof.Gates.Interfaces.Counter
import Proof.CaseAnalysis.Language
import Proof.Foundations.BooleanCircuitSizePadding
import Proof.Gates.ENP.UnitPCP

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.ExecutableInterfaces
open NearCubicWires.CanonicalBinary NearCubicWires.RecoveryScheduleEnvelope

/-- The underlying coordinate of a literal (its sign stays in the verifier). -/
def literalVar {a : ℕ} : Literal a → Fin a
  | .positive i => i
  | .negative i => i

/-- The number written by `m` bits, least significant first. -/
def natOfBits {m : ℕ} (f : Fin m → Bool) : ℕ := ∑ i : Fin m, if f i then 2 ^ i.val else 0

noncomputable def hardTable (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (cl pl : ℕ) :
    BoolFunction (D.n + cl + pl) := fun address =>
  let x : BitInput D.n := fun i => address (Fin.castAdd pl (Fin.castAdd cl i))
  let a : ℕ := natOfBits (fun i : Fin cl => address (Fin.castAdd pl (Fin.natAdd D.n i)))
  let j : ℕ := natOfBits (fun i : Fin pl => address (Fin.natAdd (D.n + cl) i))
  let raw := P.output (checkedCircuit P.code D)
  let assignment : BitInput ((checkedCircuit P.code D).n + raw.proofBits) :=
    Fin.addCases (sysEnc P.code D.n x) (P.honest (acceptedInput P.code D x (hD x)))
  let clause : Fin 3 → Literal ((checkedCircuit P.code D).n + raw.proofBits) :=
    raw.clause ⟨a % 2 ^ raw.randomBits, Nat.mod_lt _ (by positivity)⟩
  if h : j % 5 < 3 then assignment (literalVar (clause ⟨j % 5, h⟩))
  else (List.ofFn fun t => (clause t).eval assignment).all id

/-! ## Honest oracles as tables -/

/-- The oracle given by a table in address order (`binaryAddress`, low bit first, as `boolFunctionTable`). -/
def tableOracle {ℓ : ℕ} (t : BitInput (2 ^ ℓ)) : BitInput ℓ → Bool := fun a => t (binaryAddress a)

/-- `t` is an honest oracle table for `C`: `C^{O_t}` is unsatisfiable (imp:short-pcp's completeness convention). -/
def HonestTable {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) (t : BitInput (2 ^ ℓ)) : Prop :=
  ∀ w, C.eval (tableOracle t) w = false

/-- The false-first least honest table (paper v2 §11.6 stage 2: one variable per oracle address, prefix
self-reduction). -/
structure FirstTable {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) where
  table : BitInput (2 ^ ℓ)
  honest : HonestTable C table
  minimal : ∀ t, HonestTable C t → CanonicalBoolListLE (List.ofFn table) (List.ofFn t)

theorem existsFirstTable {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ)
    (h : ∃ t, HonestTable C t) : Nonempty (FirstTable C) := by
  classical
  letI : LinearOrder (BitInput (2 ^ ℓ)) := LinearOrder.lift' List.ofFn List.ofFn_injective
  let eligible : Finset (BitInput (2 ^ ℓ)) := Finset.univ.filter fun t => HonestTable C t
  have hne : eligible.Nonempty := by
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by simp [eligible, ht]⟩
  refine ⟨{ table := eligible.min' hne, honest := ?_, minimal := ?_ }⟩
  · have hm := eligible.min'_mem hne
    simpa only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · intro t ht
    exact eligible.min'_le t (by simp [eligible, ht])

/-- `boolFunctionTable` of a table oracle is the table itself. -/
theorem boolFunctionTable_tableOracle {ℓ : ℕ} (t : BitInput (2 ^ ℓ)) :
    boolFunctionTable (tableOracle t) = List.ofFn t := by
  apply List.ext_getElem
  · simp [boolFunctionTable]
  · intro i h1 h2
    have hi : i < 2 ^ ℓ := by simpa using h2
    simp only [boolFunctionTable, List.getElem_map, List.getElem_range, List.getElem_ofFn, tableOracle]
    rw [binaryAddress_testBit hi]

/-- An oracle making `C^O` unsatisfiable gives an honest table. -/
theorem honestTable_of_oracle {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) (O : BitInput ℓ → Bool)
    (hO : ∀ w, C.eval O w = false) : ∃ t, HonestTable C t := by
  refine ⟨fun i => O (NearCubicWires.Bindings.CLW20Lemma310.decodeAddress i), fun w => ?_⟩
  have hO' : tableOracle (fun i => O (NearCubicWires.Bindings.CLW20Lemma310.decodeAddress i)) = O := by
    funext a
    simp only [tableOracle, NearCubicWires.Bindings.CLW20Lemma310.decodeAddress_binaryAddress]
  rw [hO']
  exact hO w

/-! ## The width schedule and the canonical choices (paper v2 §11.4–§11.6) -/

open NearCubicWires.RepairSource.CloseoutLanguage in

structure GateParams where
  k : ℕ
  clock : OrdinaryClock (fun n => n ^ (k + 2))
  degree : ℕ
  lenRoot : ℕ
  clauseDegree : ℕ
  positionLog : ℕ
  ampFactor : ℕ
  sourceOnset : ℕ

namespace GateParams
open NearCubicWires.RepairSource.CloseoutLanguage

/-- The instance-length exponent: `L_ν = ν^{lenExp + 2} = (ν^{lenRoot+1})^{10}`. -/
def lenExp (g : GateParams) : ℕ := 10 * g.lenRoot + 8

/-- `L_ν` is the tenth power of the precision base `ν^{lenRoot+1}`. -/
theorem instLength_eq (g : GateParams) (ν : ℕ) :
    Outer.instLength g.lenExp ν = (ν ^ (g.lenRoot + 1)) ^ 10 := by
  unfold Outer.instLength lenExp
  rw [← pow_mul]
  congr 1
  ring

variable (s : GateSources) (g : GateParams)

/-- lem:succinct-verifier at this clock and instance-length exponent. -/
noncomputable def sv := s.sv g.k g.clock g.lenExp

/-- The native width `q(N_ν)` at source length `N_ν = 2^ν` (paper v2 §11.4). -/
noncomputable def width (ν : ℕ) : ℕ := Outer.width s.mw (g.sv s) (2 ^ ν)

theorem nu_lt_width (ν : ℕ) : ν < g.width s ν := by
  have := Outer.succ_le_widthOf g.k (Outer.apad s.mw (g.sv s)) ν (by unfold Outer.apad; omega)
  unfold width Outer.width
  omega

noncomputable def bound (ν : ℕ) : ℕ := oracleSizeBound g.degree (g.width s ν)

/-- The oracle circuit `C_{⟨B⟩_ν}` of the import for a source circuit `B`. -/
noncomputable def outC (ν : ℕ) (B : BooleanCircuit (g.width s ν)) := Outer.outC s.mw (g.sv s) ν B

/-- `D_B` for a pair `B = (B_src, B_pf)`. -/
noncomputable def D (ν : ℕ) (B : Outer.OuterGuess (g.width s ν)) : Circuit := Outer.D s.mw (g.sv s) ν B

noncomputable def checkPCP (ν : ℕ) (z : BitInput (2 ^ ν)) :=
  ENP.unitOuter ν (g.width s ν) (List.ofFn z) (g.nu_lt_width s ν).le

/-- Some source circuit of at most `q^G` gates passes CHECK (stage 1). -/
def SrcExists (ν : ℕ) (z : BitInput (2 ^ ν)) : Prop := RecoveryChoice.SmallOracle (g.checkPCP s ν z) g.degree z

/-- `B*_src`. -/
noncomputable def firstSrc (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.SrcExists s ν z) : BooleanCircuit (g.width s ν) :=
  (RecoveryChoice.oracleSelector (g.checkPCP s ν z) g.degree z h).circuit

/-- The match PCP of stage 3: `B(a0^{q−ℓ}) = O*(a)` for every `a`. -/
noncomputable def matchPCP (ν : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ g.width s ν) (t : BitInput (2 ^ ℓ)) :=
  ENP.unitOuter ℓ (g.width s ν) (boolFunctionTable (tableOracle t)) hℓ

/-- `X_z`: the source input as a function of `q` bits (its first `ν` bits address `z`); Case 1 (i). -/
noncomputable def srcFn (ν : ℕ) (z : BitInput (2 ^ ν)) : BoolFunction (g.width s ν) := fun r =>
  z (binaryAddress fun j : Fin ν => r (Fin.castLE (g.nu_lt_width s ν).le j))

/-- `O*` as a function of `q` bits (it ignores the last `q − ℓ`); Case 1 (iii). -/
def pfFn {q ℓ : ℕ} (t : BitInput (2 ^ ℓ)) : BoolFunction q := fun r => tableOracle t (Outer.truncInput r)

/-- The amplified, padded Case 1 function. -/
noncomputable def amplified {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (q : ℕ) (f : BoolFunction q)
    (target : ℕ) : BoolFunction target := by
  classical
  exact
    let gen := amplifier.output q f
    if ht : gen.arity ≤ target then padCore gen.function ht else fun _ => false

/-- **Case 2** at source index `ν` (paper v2 §11.5 with the canonical choices of §11.6). -/
def IsCaseTwo (ν : ℕ) (z : BitInput (2 ^ ν)) : Prop :=
  ∃ h1 : g.SrcExists s ν z,
    ∃ h2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t,
      ∃ hℓ : (g.outC s ν (g.firstSrc s ν z h1)).ell ≤ g.width s ν,
        RecoveryChoice.SmallOracle
          (g.matchPCP s ν hℓ (Classical.choice (existsFirstTable _ h2)).table) g.degree z

/-- The Case 2 pair `B* = (B*_src, B*_pf)`. -/
noncomputable def selectedPair (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.IsCaseTwo s ν z) :
    Outer.OuterGuess (g.width s ν) :=
  ⟨g.firstSrc s ν z h.1, (RecoveryChoice.oracleSelector _ g.degree z h.2.2.2).circuit⟩

/-- `D_{B*}` is a tautology. -/
theorem selected_taut (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.IsCaseTwo s ν z) :
    ∀ x, (g.D s ν (g.selectedPair s ν z h)).D.eval x = true := by
  intro x
  have hmatch := (ENP.unitOuter_match _ _ h.2.2.1
    (tableOracle (Classical.choice (existsFirstTable _ h.2.1)).table) z _ (fun _ => false)).mp
    ((RecoveryChoice.oracleSelector _ g.degree z h.2.2.2).accepts (fun _ => false))
  exact Outer.D_eval_true s.mw (g.sv s) ν (g.selectedPair s ν z h) _ hmatch
    (Classical.choice (existsFirstTable _ h.2.1)).honest x

/-- **The gate core** at source index `ν` on the refuter's source input `z` (paper v2 §11.5 and §11.6): Case 2's padded
hard table, or Case 1's amplified hard function ((i) the source input, (iii) the first honest oracle), padded to
`target` inputs; `false` in the exceptional branch without an honest oracle. -/
noncomputable def gateCore (P : ThreeQueryPCPP) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ)
    (z : BitInput (2 ^ ν)) (cl pl target : ℕ) : BoolFunction target := by
  classical
  exact
    if h1 : g.SrcExists s ν z then
      if h2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t then
        let O := (Classical.choice (existsFirstTable _ h2)).table
        if h : g.IsCaseTwo s ν z then
          let D := g.D s ν (g.selectedPair s ν z h)
          if ht : D.n + cl + pl ≤ target then
            padCore (hardTable P D (g.selected_taut s ν z h) cl pl) ht
          else fun _ => false
        else amplified amplifier (g.width s ν) (pfFn O) target
      else fun _ => false
    else amplified amplifier (g.width s ν) (g.srcFn s ν z) target

/-- `q₀(q) = q + ⌈d_G lg(q+2)⌉ + log₂ P` (eq:gadget-table-arity). -/
noncomputable def tableArity (ν : ℕ) : ℕ := g.width s ν + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog

/-- `m(q) = K_amp q₀(q)`. -/
noncomputable def coreArity (ν : ℕ) : ℕ := g.ampFactor * g.tableArity s ν

/-- The largest `ν` with `m(q(N_ν)) ≤ n/2` (zero when none). -/
noncomputable def selected (n : ℕ) : ℕ := selectedIndex (g.coreArity s) n

/-- The native length `q(n)`. -/
noncomputable def nativeLength (n : ℕ) : ℕ := min (g.coreArity s (g.selected s n)) n

theorem nativeLength_le (n : ℕ) : g.nativeLength s n ≤ n := min_le_right _ _

/-- The native function at final length `n`, for the weak machine `M`. -/
noncomputable def native (P : ThreeQueryPCPP) (M : OrdinaryWeakMachine) (n : ℕ) :
    BoolFunction (g.nativeLength s n) := by
  classical
  exact
    let ν := g.selected s n
    if 1 ≤ ν ∧ g.sourceOnset ≤ 2 ^ ν then
      g.gateCore s P (selectedAmplifier s.amplification g.degree) ν
        ((s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).output M (2 ^ ν))
        (clauseWidth g.clauseDegree (g.width s ν)) g.positionLog (g.nativeLength s n)
    else fun _ => false

end GateParams

/-! ## The closure record -/

/-- Parameter constraints the transfer proofs need (Case 1: `G/b_amp > h_sim + 1`, `K_amp ≥ a_G`; Case 2 and §11.6:
`P = 128/ε`, `b(q)`, `K_d`; the source-circuit descriptions fit in `L_ν`). -/
structure GateParamsReady (s : GateSources) (_P : ThreeQueryPCPP) (_ε : ℝ) (g : GateParams) (_budget : ℕ → ℕ) :
    Prop where
  /-- `K_amp ≥ 1`, so the hard table fits inside the core arity (v2 §11.6). -/
  ampPos : 1 ≤ g.ampFactor
  /-- The weight budget is at least a fixed fraction of `𝒜₃(q)` at large `q` (`b(q) = ⌊η₀ ε 𝒜₃(q)⌋`). -/
  budgetLower : ∃ η : ℝ, 0 < η ∧ ∃ q0 : ℕ, ∀ q, q0 ≤ q → η * NearCubicGates.Close.Interfaces.A3 q ≤ (_budget q : ℝ)
  /-- The weight budget stays polynomial: `b(q) ≤ q³` eventually (`𝒜₃(q) ≤ q³`). -/
  budgetUpper : ∃ q1 : ℕ, ∀ q, q1 ≤ q → _budget q ≤ q ^ 3
  /-- `G ≥ 17 c_STV` ("Choose a fixed integer G with G/b_amp > h_sim + 1"). -/
  degreeLarge : 17 * s.amplification.stvExponent ≤ g.degree
  /-- `K_amp ≥ a_G`. -/
  ampLarge : (selectedAmplifier s.amplification g.degree).arityCoefficient ≤
    g.ampFactor
  /-- `log₂ P ≥ 1` (`P = 128/ε ≥ 2`). -/
  positionPos : 1 ≤ g.positionLog
  /-- `d_G ≥ 1`. -/
  clausePos : 1 ≤ g.clauseDegree
  /-- "it rejects unless every general circuit with `q` inputs and at most `q^G` gates has a description of at most `L_ν`
  bits ... these guards fail at only finitely many lengths" (paper v2 §11.4). -/
  lenFit : ∃ ν₀ : ℕ, ∀ ν, ν₀ ≤ ν → ∀ B : BooleanCircuit (g.width s ν), B.size ≤ g.bound s ν →
    Outer.SrcFits g.lenExp ν B

open NearCubicWires.RepairSource.CloseoutLanguage in
/-- What the weak-machine side supplies at one `ε`, mirroring the shared `CloseoutFinal.ClosureAt`. -/
structure GateClosure (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ) where
  g : GateParams
  budget : ℕ → ℕ
  ready : GateParamsReady s P ε g budget
  M : OrdinaryWeakMachine
  littleO : OrdinaryLittleO M (fun n => n ^ (g.k + 2))
  oneSided : ∀ n x, M.accepts n x →
    (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.timedView.accepts n x = true
  /-- Case 2 completeness (paper v2 §11.5): for a CHECK-passing pair of `q^G`-gate circuits whose `D_B` is a tautology,
  an approximator of the hard table within the native weight budget makes the weak machine accept the source input. -/
  complete : ∃ onset : ℕ, ∀ ν : ℕ, onset ≤ ν → ∀ z : BitInput (2 ^ ν),
    ∀ B : Outer.OuterGuess (g.width s ν), B.src.size ≤ g.bound s ν → B.pf.size ≤ g.bound s ν →
    Outer.Check ν z B.src →
    ∀ hD : ∀ x, (g.D s ν B).D.eval x = true,
    ∀ C : NearCubicGates.Target.WeightedSymmetricCircuit
        ((g.D s ν B).n + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog),
      C.topWeight ≤ budget (g.width s ν) →
      1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicGates.FiniteAverages.agreement C.eval
        (hardTable P (g.D s ν B) hD (clauseWidth g.clauseDegree (g.width s ν)) g.positionLog) →
      M.accepts (2 ^ ν) z

def FrontierOfClosure : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ), 0 < ε → ε < (P.gamma : ℝ) / 5 →
    GateClosure s P ε → Nonempty (NearCubicGates.HeadlineAssembly.NativeFrontier (P.gamma : ℝ) ε)

def ClosureSupply : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ), 0 < ε → ε < (P.gamma : ℝ) / 5 → Nonempty (GateClosure s P ε)

theorem frontierSupply_of (h1 : FrontierOfClosure) (h2 : ClosureSupply) : NearCubicGates.Close.FrontierSupply := by
  intro s P ε hε hεγ
  obtain ⟨c⟩ := h2 s P ε hε hεγ
  exact h1 s P ε hε hεγ c

end NearCubicGates.Close.Transfer
