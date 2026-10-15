import Proof.MachineModel.OrdinaryMatrixPacketCapacityNative

/-! The native bootstrap supplies the finite tape bounds and zero local
heads consumed by the next physical erase. Capacity-generation scratch is
outside this bound and is never swept in the per-plane loop. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketCapacityEndpoint
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixWilliamsProduct (source)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem endpoint_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (negative : Bool) (bit : ℕ) (out : List Bool)
    (ht : bit<r.p)
    (hC : MatrixVariablePacketWorkspace.footprint a r bit negative≤C*(r.U+1)^2*(r.d+r.p+1)^E) : ∃ actual,
    runFrom (MatrixPacketCapacityNative.machine a E C negative) (MatrixPacketCapacityNative.budget a E C r negative bit)
      (MatrixPacketCapacityNative.input a E C r bit out)=some actual ∧
    actual.final.tapes (MatrixPacketCapacityNative.outputTape a E)=List.replicate (C*(r.U+1)^2*(r.d+r.p+1)^E) true ∧
    actual.final.heads (MatrixPacketCapacityNative.outputTape a E)=0 ∧
    actual.final.tapes (((MatrixVariablePacket.outputTape a).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=out++packet r negative bit ∧
    actual.final.heads (((MatrixVariablePacket.outputTape a).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=(out++packet r negative bit).length ∧
    actual.final.tapes (((MatrixVariablePacket.offset a).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=UnaryTemplate.tape (2*bit) ∧
    actual.final.heads (((MatrixVariablePacket.offset a).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=1 ∧
    (∀ i : Fin (MatrixVariablePacketWorkspace.tapes a),MatrixVariablePacketWorkspace.working a i →
      actual.final.heads (i.castAdd (MatrixPacketCapacityNative.extra E))=0 ∧
      (actual.final.tapes (i.castAdd (MatrixPacketCapacityNative.extra E))).length≤C*(r.U+1)^2*(r.d+r.p+1)^E) ∧
    actual.steps≤MatrixPacketCapacityNative.budget a E C r negative bit := by
  obtain ⟨actual,ha,capT,capH,outT,outH,offsetT,offsetH,steps,small,base,hbase,other⟩ :=
    MatrixPacketCapacityNative.native_run a E C r negative bit out ht
  obtain ⟨reset,hr,_,_,fields,heads,logH,_,bs⟩ := MatrixVariablePacketReset.reset_run a r negative bit out ht
  have he : base=reset := Option.some.inj (hbase.symm.trans hr)
  subst reset
  have base_zero (i : Fin (MatrixVariablePacketWorkspace.tapes a)) (hi : MatrixVariablePacketWorkspace.working a i) :
      base.final.heads i=0 := by
    revert hi
    refine Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (fun j => ?_) (fun j => ?_) i
    · intro hi
      have h:=heads j
      split at h
      · rename_i he
        have hv:=congrArg Fin.val he
        have h0:=hi.1
        exact False.elim (h0 hv)
      · split at h
        · rename_i he
          have hv:=congrArg Fin.val he
          have h1:=hi.2
          exact False.elim (h1 hv)
        · exact h
    · intro _
      fin_cases j
      exact logH
  have base_bound (i : Fin (MatrixVariablePacketWorkspace.tapes a)) (hi : MatrixVariablePacketWorkspace.working a i) :
      (base.final.tapes i).length≤C*(r.U+1)^2*(r.d+r.p+1)^E := by
    obtain ⟨hh,hl⟩ := MatrixVariablePacketWorkspace.entry_bounds a r bit out i hi
    have supp := PCPSerializerReuse.tape_support (MatrixVariablePacketReset.machine a negative) _ _ base hbase i
      ((physicalInput r).length+2*bit+2) 0 hh.le (hl.trans (Nat.le_max_left _ _))
    have hmax : max ((physicalInput r).length+2*bit+2) (0+base.steps+1)≤MatrixVariablePacketWorkspace.footprint a r bit negative := by
      unfold MatrixVariablePacketWorkspace.footprint
      omega
    exact supp.trans (hmax.trans hC)
  refine ⟨actual,ha,capT,capH,outT,outH,offsetT,offsetH,?_,steps⟩
  intro i hi
  by_cases h400 : i.val=400
  · have ei : i=((((400 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1) := Fin.ext h400
    subst i
    have st := (small 0).1
    have sh := (small 0).2
    change actual.final.tapes (((((400 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=UnaryTemplate.tape r.U at st
    refine ⟨sh,?_⟩
    have hlen := congrArg List.length (st.trans (fields 2).symm)
    exact hlen.le.trans (base_bound _ hi)
  by_cases h12 : i.val=12
  · have ei : i=((((12 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1) := Fin.ext h12
    subst i
    have st := (small 1).1
    have sh := (small 1).2
    change actual.final.tapes (((((12 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=UnaryTemplate.tape r.d at st
    refine ⟨sh,?_⟩
    have hlen := congrArg List.length (st.trans (fields 0).symm)
    exact hlen.le.trans (base_bound _ hi)
  by_cases h22 : i.val=22
  · have ei : i=((((22 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1) := Fin.ext h22
    subst i
    have st := (small 2).1
    have sh := (small 2).2
    change actual.final.tapes (((((22 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17).castAdd 1).castAdd (MatrixPacketCapacityNative.extra E))=UnaryTemplate.tape r.p at st
    refine ⟨sh,?_⟩
    have hlen := congrArg List.length (st.trans (fields 1).symm)
    exact hlen.le.trans (base_bound _ hi)
  obtain ⟨keepT,keepH⟩ := other i ⟨h400,h12,h22⟩
  exact ⟨keepH.trans (base_zero i hi),by rw [keepT]; exact base_bound i hi⟩

end NearCubicWires.RepairOrdinary.MatrixPacketCapacityEndpoint
