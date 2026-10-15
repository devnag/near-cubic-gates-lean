import Proof.CaseAnalysis.WitnessLegalFields

/-! Typed projections expose the exact four retained inputs without
reducing the enclosing cold controller's concrete state space. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem project_tapes (a : PointwisePCPPAlgorithm) (k D G : ℕ) {s : ℕ}
    (cfg : Configuration (ColdNative.tapes source a k D G) s) (i : Fin (SourcePolicy.tapes D)) :
    (ColdNative.project source a k D G cfg).tapes (SourcePolicy.Call.slots D (NativePolicy.fields a) i)=
      cfg.tapes (sourceSlots source a k D G i):=by
  simp only [ColdNative.project,NativePolicy.Call.project,sourceSlots,Function.comp_apply]
  rfl

theorem project_heads (a : PointwisePCPPAlgorithm) (k D G : ℕ) {s : ℕ}
    (cfg : Configuration (ColdNative.tapes source a k D G) s) (i : Fin (SourcePolicy.tapes D)) :
    (ColdNative.project source a k D G cfg).heads (SourcePolicy.Call.slots D (NativePolicy.fields a) i)=
      cfg.heads (sourceSlots source a k D G i):=by
  simp only [ColdNative.project,NativePolicy.Call.project,sourceSlots,Function.comp_apply]
  rfl

theorem retained_fields (a : PointwisePCPPAlgorithm) (k D G copies : ℕ) (delta : ℚ) {s : ℕ}
    (cfg : Configuration (ColdNative.tapes source a k D G) s) (r : PCPPRequest a.minimumArity)
    (hdom:cfg.tapes (ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a 13))=UnaryTemplate.tape r.arity)
    (hs:SourcePolicy.Call.Fields D copies delta (NativePolicy.fields a) r (a.output r)
      (ColdNative.project source a k D G cfg)) :
    (∀ i,cfg.tapes (fields source a k D G i)=LegalTemplate.Call.values r.arity (CorePolicy.q0 D r.arity)
      (a.output r).clauseBits (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D r.arity) copies*
        max 1 (2*2^(a.output r).clauseBits))) i) ∧
    (∀ i,cfg.heads (fields source a k D G i)=LegalTemplate.Call.cursors i):=by
  have count:=hs.clause
  have q0:=hs.q0
  have cap:=hs.cap
  rw [project_tapes] at count q0 cap
  constructor
  · intro i
    refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun l=>Fin.cases ?_ (fun m=>?_) l) j) i
    · rw [domain_slot]
      exact hdom
    · simpa only [fields,Function.comp_apply,localFields,Matrix.cons_val_succ,Matrix.cons_val_zero,LegalTemplate.Call.values] using q0
    · simpa only [fields,Function.comp_apply,localFields,Matrix.cons_val_succ,Matrix.cons_val_zero,LegalTemplate.Call.values] using count
    · have hm:m=0:=Fin.eq_zero m
      subst m
      simpa only [fields,Function.comp_apply,localFields,Matrix.cons_val_succ,Matrix.cons_val_zero,LegalTemplate.Call.values] using cap
  · intro i
    have hh:=hs.cursor (localFields D i)
    rw [project_heads] at hh
    change cfg.heads (fields source a k D G i)=_ at hh
    rw [hh,SourcePolicy.heads,local_val]
    have hw:36 ≤ CorePolicy.W D:=by dsimp [CorePolicy.W,CloseoutSchedule.Width.tapes,CloseoutSchedule.Clause.tapes];omega
    fin_cases i <;> simp [LegalTemplate.Call.cursors]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
