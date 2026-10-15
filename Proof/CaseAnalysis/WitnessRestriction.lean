import Proof.CaseAnalysis.WitnessPadding
import Proof.CaseAnalysis.WitnessAverage

/-! Restrict normalized atoms to a native occurrence after selecting the
redundant clause bits.  Coefficients and wire counts are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Restriction
open SourceInterfaces ExecutableInterfaces CanonicalWitnessCodec RecoveryPipeline
open ComponentwiseCircuitRestriction OccurrenceSliceTransport SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def suffix {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (clause : BitInput c) (position : Bool) : BitInput ((n+r+1)-n) := fun i=>
  if hc : i.val<c then clause ⟨i.val,hc⟩
  else if hr : i.val<r then padding ⟨i.val-c,by omega⟩
  else position

theorem address_eq {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (clause : BitInput c) (position : Bool) (u : BitInput n) :
    (fun i=>Sum.elim u (suffix h padding clause position)
      ((finSplitEquiv (show n ≤ n+r+1 by omega)).symm i))=
      Padding.extend h padding (occurrenceAddress u clause position) := by
  funext i
  obtain ⟨s,rfl⟩:=(finSplitEquiv (show n ≤ n+r+1 by omega)).surjective i
  cases s with
  | inl i=>
    simp only [Equiv.symm_apply_apply,Sum.elim_inl]
    have hn:i.val<n:=i.isLt
    simp [Padding.extend,occurrenceAddress,finSplitEquiv,hn,show i.val<n+c by omega]
  | inr i=>
    simp only [Equiv.symm_apply_apply,Sum.elim_inr]
    have hn:¬n+i.val<n:=by omega
    by_cases hc:i.val<c
    · have hp:n+i.val<n+c:=by omega
      simp only [suffix,hc,↓reduceDIte,Padding.extend,finSplitEquiv,Equiv.trans_apply,
        finCongr_apply,Fin.val_cast,finSumFinEquiv_apply_right,Fin.val_natAdd,hp,
        occurrenceAddress,hn]
      apply congrArg clause
      apply Fin.ext
      change i.val=n+i.val-n
      omega
    · have hp:¬n+i.val<n+c:=by omega
      by_cases hr:i.val<r
      · have he:n+i.val<n+r:=by omega
        simp only [suffix,hc,hr,↓reduceDIte,Padding.extend,finSplitEquiv,Equiv.trans_apply,
          finCongr_apply,Fin.val_cast,finSumFinEquiv_apply_right,Fin.val_natAdd,hp,he]
        apply congrArg padding
        apply Fin.ext
        change i.val-c=n+i.val-(n+c)
        omega
      · have he:¬n+i.val<n+r:=by omega
        simp [suffix,hc,hr,Padding.extend,finSplitEquiv,hp,he,occurrenceAddress]

def symmetric {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (clause : BitInput c) (position : Bool) (atom : NormalizedSymmetricThresholdCircuit (n+r+1)) :=
  restrictNormalizedSymmetricCircuit atom (by omega) (suffix h padding clause position)

def threshold {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (clause : BitInput c) (position : Bool) (atom : NormalizedThresholdThresholdCircuit (n+r+1)) :=
  restrictNormalizedThresholdCircuit atom (by omega) (suffix h padding clause position)

theorem symmetric_value {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (clause : BitInput c) (position : Bool) (atom : NormalizedSymmetricThresholdCircuit (n+r+1))
    (u : BitInput n) : (symmetric h padding clause position atom).eval u=
      atom.eval (Padding.extend h padding (occurrenceAddress u clause position)) := by
  rw [symmetric,restrictNormalizedSymmetricCircuit_eval,address_eq]

theorem threshold_value {n c r : ℕ} (h : c ≤ r) (padding : BitInput (r-c))
    (clause : BitInput c) (position : Bool) (atom : NormalizedThresholdThresholdCircuit (n+r+1))
    (u : BitInput n) : (threshold h padding clause position atom).eval u=
      atom.eval (Padding.extend h padding (occurrenceAddress u clause position)) := by
  rw [threshold,restrictNormalizedThresholdCircuit_eval,address_eq]

theorem map_mass {Circuit : CanonicalWitnessCodec.CircuitFamily} {n m : ℕ}
    (restrictAtom : Circuit m→Circuit n) (ts : List (LegalCircuitTerm Circuit m)) :
    Average.mass (ts.map (mapLegalCircuitTerm restrictAtom))=Average.mass ts := by
  simp only [Average.mass,List.map_map,Function.comp_def,mapLegalCircuitTerm_coefficient]

theorem map_value {Circuit : CanonicalWitnessCodec.CircuitFamily} {n m : ℕ}
    (evaluate : {n : ℕ}→Circuit n→BitInput n→Bool)
    (restrictAtom : Circuit m→Circuit n) (input : BitInput n→BitInput m)
    (h : ∀ atom u,evaluate (restrictAtom atom) u=evaluate atom (input u))
    (ts : List (LegalCircuitTerm Circuit m)) (u : BitInput n) :
    Average.value evaluate (ts.map (mapLegalCircuitTerm restrictAtom)) u=
      Average.value evaluate ts (input u) := by
  simp only [Average.value,List.map_map,Function.comp_def,mapLegalCircuitTerm]
  simp only [h]

end NearCubicWires.RepairOrdinary.CloseoutWitness.Restriction
