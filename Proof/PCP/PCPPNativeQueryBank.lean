import Proof.PCP.PCPPNativeQueryLoopMeaning

/-! The complete shared query bank consumes the actual Q template and
retained hierarchy projection fields. Its output is exactly queryBank's
native node list; the final actual raw DAG counter is base+Q*(2*size+1). -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templateCaps (count : ℕ) (i : Fin 174) := if i=173 then count+2 else 0
noncomputable def templateConfiguration (phase : Fin 5) (bits fields : List Bool)
    (cursor base C F G : ℕ) (out : List Bool) (width total driverHead : ℕ) :=
  ZeroPadding.config (templateCaps total) (configuration phase bits fields cursor base C F G out width total driverHead)
theorem template_count (phase : Fin 5) (bits fields : List Bool)
    (cursor base C F G : ℕ) (out : List Bool) (width total driverHead : ℕ) :
    (templateConfiguration phase bits fields cursor base C F G out width total driverHead).tapes 173=UnaryTemplate.tape total ∧
      (templateConfiguration phase bits fields cursor base C F G out width total driverHead).heads 173=driverHead := by
  constructor
  · change ZeroPadding.pad (total+2) (CompareMachine.word total)=UnaryTemplate.tape total
    exact DecompositionSerializerCount.padded_count total
  · rfl

theorem template_lower (phase : Fin 5) (bits fields : List Bool)
    (cursor base C F G : ℕ) (out : List Bool) (width total driverHead : ℕ) (i : Fin 171) :
    (templateConfiguration phase bits fields cursor base C F G out width total driverHead).heads (i.castAdd 3)=
      PCPPNativeQueryReusable.heads out i ∧
    (templateConfiguration phase bits fields cursor base C F G out width total driverHead).tapes (i.castAdd 3)=
      PCPPNativeQueryReusable.data bits [] base C F G out i := by
  have hi : (i.castAdd 2).castAdd 1≠(173 : Fin 174) := by
    intro h
    have hv : i.val=173 := congrArg (fun j : Fin 174 => j.val) h
    omega
  change (templateConfiguration phase bits fields cursor base C F G out width total driverHead).heads ((i.castAdd 2).castAdd 1)=_ ∧
    (templateConfiguration phase bits fields cursor base C F G out width total driverHead).tapes ((i.castAdd 2).castAdd 1)=_
  simp only [templateConfiguration,ZeroPadding.config,templateCaps,hi,ite_false,ZeroPadding.pad_zero,
    configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,
    PCPPNativeQueryIteration.entry,PCPPNativeQueryIteration.heads,PCPPNativeQueryIteration.data,and_self]

theorem bank_run {n r q : ℕ} (pre suffix : List Bool) (base C F G : ℕ) (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hFG : F+1 ≤ G)
    (hreq : requirements base 0 C F G oracle (List.ofFn projections)) :
    ∃ result,runFrom machine (q*(6*G+9)+3)
      (templateConfiguration 0 (PCPPNative.descriptor oracle) (source pre suffix (List.ofFn projections)) pre.length
        base C F G out n q 1)=some result ∧ result.steps ≤ q*(6*G+9)+3 ∧
      result.final=templateConfiguration 3 (PCPPNative.descriptor oracle) (source pre suffix (List.ofFn projections))
        (pre.length+(stream (List.ofFn projections)).length) (base+q*(2*oracle.size+1)) C F G
        (out++(PCPPNative.queryNodesPrefix base oracle projections q).flatMap PCPPRequestNodeSchema.native) n q 1 := by
  obtain ⟨raw,hr,rs,rf⟩ := loop_run (List.ofFn projections) pre suffix base 0 C F G oracle out hCF hFG hreq q 0
    (by simp only [List.length_ofFn,Nat.zero_add])
  rw [List.length_ofFn] at hr rs rf
  have ht : q*(6*G+8)+q+3=q*(6*G+9)+3 := by ring
  rw [ht] at hr rs
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at hr rf
  obtain ⟨result,run,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine (templateCaps q) _ _ raw hr
  refine ⟨result,run,by omega,?_⟩
  rw [hfinal,rf,emitted_queryNodes]
  rfl

end NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
