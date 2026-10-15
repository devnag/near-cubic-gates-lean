import Proof.Assembly.Front
import Proof.CaseAnalysis.RowsOriginalSwitch

/-! One fixed runtime flag selects the native producer or a paid terminal
prefix. Both branches retain the original initializer bank and complete costs.
The terminal provider is uniform in the source-fixed code parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace NativeTerminalDispatch
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NativeRecipes FamilyInitGenerator
open NativeFamilyGenerator PrefixInitializerFront
open P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

/-- Fixed policy room for linear terminal preparation and initialization.
This is a duty of the chosen global policy, not a new runtime/final premise. -/
noncomputable def SourceSlack (g : PrefixCode) : Prop :=
 100000*(r_tapes g.printer+1)*(g.policy.inputCoefficient+1) ≤
   g.policy.sourceCoefficient ∧ g.policy.inputDegree ≤ g.policy.sourceDegree

noncomputable abbrev LiveWithDispatch (sources : EightSources) (g : PrefixCode) : Prop :=
 ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat) (mode : Bool),
 Admissible sources g.policy atoms L target recordWidth mode →
 let i := inputOf atoms L target recordWidth mode true
 let r := g.result i
 FrontProduced g i ∧
 NativeRows sources L target mode atoms g.printer r.S r.R r.B r.rowWidth r.ds r.total r.denominator ∧
 r.rowWidth ≤ recordWidth ∧ r.total < 2^recordWidth ∧
 r.residual = (if mode then
   (normalizedLiveSet (symmetricFourfoldOccurrences
     (⟨q,atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩ : FourfoldRequest NormalizedSymmetricThresholdCircuit)) L)ᶜ.card
  else (normalizedLiveSet (thresholdFourfoldOccurrences
     (⟨q,atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩ : FourfoldRequest NormalizedThresholdThresholdCircuit)) L)ᶜ.card) ∧
 r.S=workspace g.printer (driverCapacity g.printer q r.residual g.policy.cacheCoefficient g.policy.cacheDegree) ∧
 r.R=rewind g.printer (driverCapacity g.printer q r.residual g.policy.cacheCoefficient g.policy.cacheDegree) ∧
 r.B=buffer (driverCapacity g.printer q r.residual g.policy.cacheCoefficient g.policy.cacheDegree) ∧
 (r.fuel+2+1+initFuel g.printer (scalars g i)) ≤ (r.ds.length+1)*(rowBudget g.policy i r.residual+5)+3 ∧
 f_budget g.printer r.S r.rowWidth recordWidth r.ds.length ≤
  (r.ds.length+1)*(rowBudget g.policy i r.residual+5)+3

noncomputable abbrev TerminalWithDispatch (g : PrefixCode) : Prop :=
 ∀ (q L target recordWidth : Nat) (mode : Bool),
 let i : Input := ⟨[],[],[],q,L,target,recordWidth,mode,false⟩
 FrontEnvelope g i →
 let r := g.result i
 FrontProduced g i ∧ r.ds=[] ∧ r.residual=0 ∧
 (r.fuel+2+1+initFuel g.printer (scalars g i)) ≤ g.policy.sourceCoefficient*(q+1)^g.policy.sourceDegree

structure Branch (g : PrefixCode) where
 states : Nat
 machine : Machine (tapes g.printer (7+g.scratch)) states
 result : Input → Result (tapes g.printer (7+g.scratch))

noncomputable def branchCode (g : PrefixCode) (t : Branch g) : PrefixCode :=
 { g with states := t.states, machine := t.machine, result := t.result }

/-- No native producer work is assigned to the terminal component. It starts
from the actual inactive nine-word input and pays every required output bit. -/
abbrev TerminalProvider := (g : PrefixCode) → SourceSlack g →
 { t : Branch g // TerminalWithDispatch (branchCode g t) }

structure Live (sources : EightSources) where
 code : PrefixCode
 slack : SourceSlack code
 live : LiveWithDispatch sources code

abbrev GlobalLive := (sources : EightSources) → (gamma : Real) →
 (hg : 0<gamma) → (hh : gamma<1/2) → (p : Parameters sources gamma) → Live sources

noncomputable def activeSlot (g : PrefixCode) : Fin (tapes g.printer (7+g.scratch)) := by
 unfold tapes
 exact Fin.natAdd (r_tapes g.printer) ⟨8, by omega⟩

noncomputable def combined (g : PrefixCode) (t : Branch g) : PrefixCode :=
 { printer := g.printer
   scratch := g.scratch
   states := _
   machine := CloseoutRowsOriginalSwitch.machine g.machine t.machine (activeSlot g)
   policy := g.policy
   result := fun i =>
     let r := if i.active then g.result i else t.result i
     { r with fuel := r.fuel+2 } }

theorem active_bit (g : PrefixCode) (i : Input) :
 readTapeBit (inputBank g.printer (7+g.scratch) i (activeSlot g)) 0 = i.active := by
 have field : inputBank g.printer (7+g.scratch) i (activeSlot g) = [i.active] := by
   change Fin.addCases (fun _ : Fin (r_tapes g.printer) => [])
     (fun j : Fin (10+(7+g.scratch)) =>
       if h : j.val<9 then inputWords i ⟨j.val,h⟩ else [])
     (Fin.natAdd (r_tapes g.printer) ⟨8, by omega⟩) = [i.active]
   rw [Fin.addCases_right]
   simp [inputWords]
 rw [field]
 rfl

theorem active_produced (g : PrefixCode) (t : Branch g) (i : Input)
 (hi : i.active=true) (h : FrontProduced g i) : FrontProduced (combined g t) i := by
 rcases h with ⟨run,ready⟩
 constructor
 · have hb : readTapeBit (inputBank g.printer (7+g.scratch) i (activeSlot g)) 0=true :=
     (active_bit g i).trans hi
   simpa [combined,hi] using
     CloseoutRowsOriginalSwitch.true_run g.machine t.machine (activeSlot g) run hb
 · simpa [PrefixReady,combined,scalars,descriptor,hi] using ready

theorem inactive_produced (g : PrefixCode) (t : Branch g) (i : Input)
 (hi : i.active=false) (h : FrontProduced (branchCode g t) i) :
 FrontProduced (combined g t) i := by
 rcases h with ⟨run,ready⟩
 constructor
 · have hb : readTapeBit (inputBank g.printer (7+g.scratch) i (activeSlot g)) 0=false :=
     (active_bit g i).trans hi
   simpa [combined,branchCode,hi] using
     CloseoutRowsOriginalSwitch.false_run g.machine t.machine (activeSlot g) run hb
 · simpa [PrefixReady,combined,branchCode,scalars,descriptor,hi] using ready

theorem combined_live (sources : EightSources) (g : PrefixCode) (t : Branch g)
 (h : LiveWithDispatch sources g) : LiveFront sources (combined g t) := by
 intro q circuit pcpp atoms L target recordWidth mode hAd
 have out := h atoms L target recordWidth mode hAd
 exact ⟨active_produced g t _ rfl out.1, out.2⟩

theorem combined_terminal (g : PrefixCode) (t : Branch g)
 (h : TerminalWithDispatch (branchCode g t)) : TerminalFront (combined g t) := by
 intro q L target recordWidth mode
 dsimp only
 intro hEnvelope
 have out := h q L target recordWidth mode hEnvelope
 exact ⟨inactive_produced g t _ rfl out.1, out.2⟩

noncomputable def globalFront (terminal : TerminalProvider) (active : GlobalLive) :
 GlobalFront := fun sources gamma hg hh p =>
 let a := active sources gamma hg hh p
 let t := terminal a.code a.slack
 { code := combined a.code t.val
   live := combined_live sources a.code t.val a.live
   terminal := combined_terminal a.code t.val t.property }

end NativeTerminalDispatch
