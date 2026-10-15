import Proof.CaseAnalysis.RowsGateSourceRequest
import Proof.Amplification.RecoveryFocusRetained

/-! The complete original decomposition supplier on every raw gate word:
invalid gates stop at the checked verdict; accepted gates invoke the SAME
source once. Both branches have one source-fixed raw-width bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces RecoveryRootRound
open CanonicalBinary CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsGateSupport CloseoutRowsGatePairHeads DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceBound (a : DecompositionAlgorithm) (bits : List Bool) :=
  DecompositionSource.coefficient a*(bits.length+3)^(2*DecompositionSource.degree a)
def rawBudget (a : DecompositionAlgorithm) (bits : List Bool) :=
  CloseoutRowsGateGuard.budget bits+1+sourceBound a bits+1

theorem source_bound {core : ℕ} (a : DecompositionAlgorithm) (compressed : Bool)
    (g : SupportedNormalizedGate core) (bits : List Bool)
    (h : decodeSupportedNormalizedGate core (value bits)=some g) :
    Entry.budget a (request compressed g) ≤ sourceBound a bits := by
  have bounded := Nat.mul_le_mul_left (DecompositionSource.coefficient a)
    (Nat.pow_le_pow_left (request_parameter compressed g bits h) (DecompositionSource.degree a))
  rw [←pow_mul] at bounded
  exact (DecompositionSource.entry_budget a (request compressed g)).trans bounded

theorem outside (a : DecompositionAlgorithm) (i : Fin 1038) (hi : i≠1033) :
    ∀ j,slots a j≠old a i := by
  intro j hj
  have hv := congrArg Fin.val hj
  by_cases hz : j.val=0
  · simp only [slots,if_pos hz,old,Fin.val_castAdd] at hv
    exact hi (Fin.ext hv.symm)
  · simp only [slots,if_neg hz,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    have bound := i.isLt
    omega

def RawOutput {s : ℕ} (a : DecompositionAlgorithm) (compressed : Bool) (core : ℕ) (bits : List Bool)
    (out : Configuration (tapes a) s) : Prop :=
  (readTapeBit (out.tapes (old a 1037)) 0=true ↔ (decodeSupportedNormalizedGate core (value bits)).isSome) ∧
    ∀ g,decodeSupportedNormalizedGate core (value bits)=some g → Output a (request compressed g) out

theorem accepted_raw {core : ℕ} (a : DecompositionAlgorithm) (compressed : Bool)
    (bits : List Bool) (g : SupportedNormalizedGate core)
    (h : decodeSupportedNormalizedGate core (value bits)=some g)
    (decoded : Fin 1038 → List Bool)
    (hd : ReadyAt (CloseoutRowsGateGuard.machine compressed) (CloseoutRowsGateGuard.budget bits)
      CloseoutRowsGateGuard.heads (CloseoutRowsGateGuard.input core bits) decoded)
    (meaning : CloseoutRowsGateGuard.Output compressed core bits decoded) :
    ∃ r,runFrom (machine a compressed) (rawBudget a bits)
      (RecoveryCalls.restarted (machine a compressed) (heads a) (input a core bits))=some r ∧
      r.steps≤rawBudget a bits ∧ RawOutput a compressed core bits r.final := by
  have native : decoded 1033=frame (thresholdWord (request compressed g).gate) := by
    rw [meaning.2.2 g h,request_word compressed g _ (CloseoutRowsGateGuard.sign_of_gate g bits h)]
  obtain ⟨source,hs,_ss,fields⟩ := source_run a (request compressed g) decoded native
  have flag := RecoveryFocus.run_other (slots a) (Entry.machine a) (old a 1037)
    (outside a 1037 (by decide)) _ _ source hs
  obtain ⟨r,hr,rt,rh,rs⟩ := CloseoutRowsGateSourceCalls.joined (first a compressed) (second a)
    (fun scanned => scanned (old a 1037)) _ _ (heads a) _ _
    (first_run a compressed core bits decoded hd) source hs (by
      change readTapeBit (decoded 1037) 0=true
      exact meaning.2.1.mpr (by rw [h];rfl))
  have bound : budget a bits (request compressed g)≤rawBudget a bits := by
    have hb := source_bound a compressed g bits h
    unfold budget rawBudget
    omega
  have more := runFrom_moreFuel (machine a compressed) (budget a bits (request compressed g))
    (rawBudget a bits-budget a bits (request compressed g)) _ r hr
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨r,more,rs.trans bound,?_,?_⟩
  · rw [rt,flag]
    exact meaning.2.1
  · intro other ho
    have he : g=other := Option.some.inj (h.symm.trans ho)
    subst other
    unfold Output at fields ⊢
    rw [rt,rh]
    exact fields

theorem allraw (a : DecompositionAlgorithm) (compressed : Bool) (core : ℕ) (bits : List Bool) :
    ∃ r,runFrom (machine a compressed) (rawBudget a bits)
      (RecoveryCalls.restarted (machine a compressed) (heads a) (input a core bits))=some r ∧
      r.steps≤rawBudget a bits ∧ RawOutput a compressed core bits r.final := by
  obtain ⟨decoded,hd,meaning⟩ := CloseoutRowsGateGuard.guard_run compressed core bits
  by_cases pass : (decodeSupportedNormalizedGate core (value bits)).isSome
  · obtain ⟨g,hg⟩ := Option.isSome_iff_exists.mp pass
    exact accepted_raw a compressed bits g hg decoded hd meaning
  · have rejected := CloseoutRowsGatePairHeads.rejected (first a compressed) (second a)
      (fun scanned => scanned (old a 1037)) _ (heads a) _ _
      (first_run a compressed core bits decoded hd) (by
        change readTapeBit (decoded 1037) 0=false
        exact Bool.eq_false_iff.mpr (fun hf => pass (meaning.2.1.mp hf)))
    have more := enlarge _ _ (rawBudget a bits) (heads a) _ _ rejected (by unfold rawBudget;omega)
    obtain ⟨r,hr,rt,_rh,rs⟩ := more
    refine ⟨r,hr,rs,?_,?_⟩
    · rw [rt]
      exact meaning.2.1
    · intro g hg
      exact False.elim (pass (by rw [hg];rfl))

theorem raw_budget_bound (a : DecompositionAlgorithm) (bits : List Bool) :
    rawBudget a bits≤4000000000000000000001020*(bits.length+2)^26+2+
      DecompositionSource.coefficient a*(bits.length+3)^(2*DecompositionSource.degree a) := by
  have guard := CloseoutRowsGateGuard.budget_bound bits
  unfold rawBudget sourceBound
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
