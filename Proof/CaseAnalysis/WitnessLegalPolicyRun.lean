import Proof.CaseAnalysis.WitnessLegalPolicy

/-! One cold run produces the complete exact family policy and its zero
mass store. Every consumer uses the same produced fields directly. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalPolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem policy_run (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ)
    (hden : 0<den) (hR : 0<R) : ∃ output,
    ClockJoin.ReadyRun (machine e den delta copies sym) (budget e den delta copies sym R q0 cb b)
      (input e R q0 cb b) output ∧
      output (modeSlots e (ModeWire.dimensionSlots e 1))=List.replicate R true ∧
      output (modeSlots e (ModeWire.dimensionSlots e 3))=UnaryTemplate.tape R ∧
      output (modeSlots e (ModeWire.dimensionSlots e 5))=frame (SignedSortKey.binary (natBitLength R) R) ∧
      output (wireSlot e)=List.replicate (W e den R) true ∧
      output (descriptionSlots e 91)=List.replicate (DescriptionPolicy.value sym R q0 (W e den R)) true ∧
      output (termSlots e 0)=List.replicate q0 true ∧
      output (termSlots e 42)=List.replicate (T delta copies q0 cb) true ∧
      output (massSlots e 1)=List.replicate b true ∧
      Store (CompetitorSumWidth.width (T delta copies q0 cb) b) CompetitorSumWidth.zero [] (project e output) := by
  have me:M e=60+2*e:=by dsimp [M,ModeWire.tapes,ModeDivide.tapes];omega
  obtain ⟨m,hm,mR,mtemplate,mframe,_mwidth,mW⟩:=ModeWire.wire_run e den R hden hR
  have hmf:=hm.focus (modeSlots e) (mode_injective e) (input e R q0 cb b) (by
    intro i
    have hi:i.val<M e:=i.isLt
    simp only [input,modeSlots,Fin.val_castAdd,ModeWire.input,
      if_neg (show i.val≠M e by omega),if_neg (show i.val≠M e+16 by omega),
      if_neg (show i.val≠M e+138 by omega)])
  let A:=install (modeSlots e) (input e R q0 cb b) m
  have ma (i : Fin (M e)):A (modeSlots e i)=m i:=install_slot _ (mode_injective e) _ _ _
  have afresh (i : Fin (tapes e)) (hi : M e ≤ i.val):A i=input e R q0 cb b i:=
    install_other _ _ _ _ (mode_outside e i hi)
  obtain ⟨t,ht,tq,_tj,tT⟩:=TermPolicy.policy_run delta copies q0 cb
  have htf:=ht.focus (termSlots e) (term_injective e) A (by
    intro i
    rw [afresh _ (by dsimp [termSlots];omega)]
    simp only [input,termSlots,TermPolicy.input,
      if_neg (show M e+i.val≠0 by omega),Nat.add_eq_left,
      Nat.add_left_cancel_iff,if_neg (show i.val≠138 by omega)])
  let B:=install (termSlots e) A t
  have tb (i : Fin 44):B (termSlots e i)=t i:=install_slot _ (term_injective e) _ _ _
  have mold (i : Fin (M e)):B (modeSlots e i)=m i:=by
    rw [show B=install _ _ _ by rfl,install_other _ _ _ _ (term_outside e _ (Or.inl i.isLt))]
    exact ma i
  have bfresh (i : Fin (tapes e)) (hi : M e+44 ≤ i.val):B i=input e R q0 cb b i:=by
    rw [show B=install _ _ _ by rfl,install_other _ _ _ _ (term_outside e _ (Or.inr hi))]
    exact afresh i (by omega)
  obtain ⟨d,hd,dq,dW,dR,dL⟩:=DescriptionPolicy.description_run sym R q0 (W e den R)
  have hdf:=hd.focus (descriptionSlots e) (description_injective e) B (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0
      subst i;exact (tb 0).trans tq
    by_cases h34:i.val=34
    · have he:i=34:=Fin.ext h34
      subst i;exact (mold (ModeWire.valueSlot e)).trans mW
    by_cases h76:i.val=76
    · have he:i=76:=Fin.ext h76
      subst i;exact (mold (ModeWire.dimensionSlots e 1)).trans mR
    rw [bfresh _ (by rw [description_val,if_neg h0,if_neg h34,if_neg h76];omega)]
    rw [DescriptionPolicy.input,if_neg h0,if_neg h34,if_neg h76]
    simp only [input,description_val,if_neg h0,if_neg h34,if_neg h76,
      if_neg (show M e+44+i.val≠0 by omega),if_neg (show M e+44+i.val≠M e by omega),
      if_neg (show M e+44+i.val≠M e+16 by omega),if_neg (show M e+44+i.val≠M e+138 by omega)])
  let D:=install (descriptionSlots e) B d
  have dd (i : Fin 93):D (descriptionSlots e i)=d i:=install_slot _ (description_injective e) _ _ _
  have dfresh (i : Fin (tapes e)) (hi : M e+137 ≤ i.val):D i=input e R q0 cb b i:=by
    rw [show D=install _ _ _ by rfl,install_other _ _ _ _ (description_outside e i
      ⟨by omega,by omega,by omega,Or.inr hi⟩)]
    exact bfresh i (by omega)
  have actualT:D (termSlots e 42)=List.replicate (T delta copies q0 cb) true:=by
    rw [show D=install _ _ _ by rfl,install_other _ _ _ _ (description_outside e _ (by
      change M e+42≠M e ∧ M e+42≠58+2*e ∧ M e+42≠1 ∧ (M e+42<M e+44 ∨ M e+137 ≤ M e+42)
      omega))]
    exact (tb 42).trans tT
  obtain ⟨mout,hmass,mt,mb,mstore⟩:=MassCold.cold_run (T delta copies q0 cb) b
  have hmassf:=hmass.focus (massSlots e) (mass_injective e) D (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0
      subst i;exact actualT
    rw [dfresh _ (by rw [mass_val,if_neg h0];omega)]
    simp only [input,mass_val,if_neg h0,MassCold.input,
      if_neg (show M e+137+i.val≠0 by omega),if_neg (show M e+137+i.val≠M e by omega),
      if_neg (show M e+137+i.val≠M e+16 by omega)]
    have he:(M e+137+i.val=M e+138) ↔ i.val=1:=by omega
    simp only [he])
  let final:=install (massSlots e) D mout
  have kept (i : Fin (tapes e)) (hi : i.val≠M e+42 ∧ i.val<M e+137):final i=D i:=
    install_other _ _ _ _ (mass_outside e i hi)
  have desc (i : Fin 93) (hi : (descriptionSlots e i).val≠M e+42 ∧ (descriptionSlots e i).val<M e+137):
      final (descriptionSlots e i)=d i:=(kept _ hi).trans (dd i)
  have modeKept (i : Fin (M e)) (hi : i.val≠1 ∧ i.val≠58+2*e):final (modeSlots e i)=m i:=by
    rw [kept _ (by change i.val≠M e+42 ∧ i.val<M e+137;omega),show D=install _ _ _ by rfl,
      install_other _ _ _ _ (description_outside e _ (by
        change i.val≠M e ∧ i.val≠58+2*e ∧ i.val≠1 ∧ (i.val<M e+44 ∨ M e+137 ≤ i.val)
        omega))]
    exact mold i
  have joined:=ClockJoin.join (second e den delta copies sym) (mass e) _ _ _ _ _
    (ClockJoin.join (first e den delta copies) (description e sym) _ _ _ _ _
      (ClockJoin.join (mode e den) (terms e delta copies) _ _ _ _ _ hmf htf) hdf) hmassf
  refine ⟨final,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (desc 76 (by change 1≠M e+42 ∧ 1<M e+137;omega)).trans dR
  · exact (modeKept (ModeWire.dimensionSlots e 3) (by change 3≠1 ∧ 3≠58+2*e;omega)).trans mtemplate
  · exact (modeKept (ModeWire.dimensionSlots e 5) (by change 5≠1 ∧ 5≠58+2*e;omega)).trans mframe
  · exact (desc 34 (by
      change (wireSlot e).val≠M e+42 ∧ (wireSlot e).val<M e+137
      simp only [wire_val];omega)).trans dW
  · exact (desc 91 (by change M e+44+91≠M e+42 ∧ M e+44+91<M e+137;omega)).trans dL
  · exact (desc 0 (by change M e≠M e+42 ∧ M e<M e+137;omega)).trans dq
  · exact (install_slot (massSlots e) (mass_injective e) D mout 0).trans mt
  · exact (install_slot (massSlots e) (mass_injective e) D mout 1).trans mb
  · have he:project e final=MassCold.project mout:=by
      funext i;exact install_slot (massSlots e) (mass_injective e) D mout (MassCold.nativeSlots i)
    rw [he];exact mstore

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalPolicy
