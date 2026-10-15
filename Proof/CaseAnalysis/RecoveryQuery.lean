import Proof.CaseAnalysis.RecoveryMeaning

/-! The one shared query may already contain false padding from the refuter
prefix. The original cold recovery trace runs on that padding with unchanged
cost; its final query length is bounded by the maximum of both paid lengths. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedCold
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem padded_fields {t s : ℕ} (q : Fin t) (length cost : ℕ)
    (final : Configuration t s) (hq:(final.tapes q).length ≤ cost) :
    let padded:=ZeroPadding.config (fun i=>if i=q then length else 0) final
    padded.heads=final.heads ∧ (padded.tapes q).length ≤ max length cost ∧
      (∀ i,i≠q → padded.tapes i=final.tapes i):=by
  refine ⟨rfl,?_,?_⟩
  · simp only [ZeroPadding.config,if_true,ZeroPadding.pad_length]
    exact max_le_max_left length hq
  · intro i hi
    simp only [ZeroPadding.config,if_neg hi,ZeroPadding.pad_zero]

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def queryPort (k d : ℕ) : Fin (tapes source k d):=
  (356 : Fin 790).natAdd (oldTapes source k d)
def queryCaps (k d length : ℕ) (i : Fin (tapes source k d)):=
  if i=queryPort source k d then length else 0
def queryInput (k d : ℕ) (word : List Bool) (W length : ℕ):=
  Function.update (input source k d word W) (queryPort source k d) (List.replicate length false)

theorem input_query (k d : ℕ) (word : List Bool) (W : ℕ) :
    input source k d word W (queryPort source k d)=[]:=Fin.addCases_right _

theorem input_padding (k d : ℕ) (word : List Bool) (W length : ℕ) :
    (fun i=>ZeroPadding.pad (queryCaps source k d length i) (input source k d word W i))=
      queryInput source k d word W length:=by
  funext i
  by_cases hi:i=queryPort source k d
  · subst i
    simp only [queryCaps,if_true,input_query,ZeroPadding.pad,List.length_nil,Nat.sub_zero,
      List.nil_append,queryInput,Function.update_self]
  · simp only [queryCaps,if_neg hi,ZeroPadding.pad_zero,queryInput,Function.update_of_ne hi]

theorem query_padded_trace (k d CH Cpad : ℕ) (code word : List Bool) (W length cost : ℕ)
    (final : (program source k d CH Cpad code).Config)
    (trace:OrdinaryOracleTrace RecoveryOracle.correctedSat (program source k d CH Cpad code) cost
      (initialConfiguration (program source k d CH Cpad code).base.machine (input source k d word W)) final)
    (hq:(final.tapes (queryPort source k d)).length ≤ cost) :
    let padded:=ZeroPadding.config (queryCaps source k d length) final
    OrdinaryOracleTrace RecoveryOracle.correctedSat (program source k d CH Cpad code) cost
      (initialConfiguration (program source k d CH Cpad code).base.machine
        (queryInput source k d word W length)) padded ∧
      padded.heads=final.heads ∧
      (padded.tapes (queryPort source k d)).length ≤ max length cost ∧
      (∀ i,i≠queryPort source k d → padded.tapes i=final.tapes i):=by
  dsimp only
  have h:=OrdinaryOracleCompose.trace_padding (queryCaps source k d length) trace
  have hi:ZeroPadding.config (queryCaps source k d length)
      (initialConfiguration (program source k d CH Cpad code).base.machine (input source k d word W))=
      initialConfiguration (program source k d CH Cpad code).base.machine
        (queryInput source k d word W length):=by
    apply configuration_ext
    · rfl
    · rfl
    · exact input_padding source k d word W length
  exact ⟨hi ▸ h,padded_fields (queryPort source k d) length cost final hq⟩

end
end NearCubicWires.RepairSource.RecoveryBoundedCold
