import Proof.Supplier.EquationScalarStreamLayout

namespace NearCubicWires.RepairOrdinary.EquationScalarStream
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def isolated (C : Nat) (source out bits : List Bool) :=
  Function.update (tapes C source out) 1 (ZeroPadding.pad C (frame bits))

theorem move_run (pre bits suffix out : List Bool) (C : Nat) (hC : 2*bits.length+1 ≤ C) :
    ∃ r,runFrom moveProgram (4*bits.length+4)
      ⟨moveProgram.start,heads pre.length out.length,tapes C (pre++frame bits++suffix) out⟩=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) out.length ∧
      r.final.tapes=isolated C (pre++frame bits++suffix) out bits ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,bt,bh,bs⟩ := PCPFieldMoves.advance_run pre bits suffix C C
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config moveSlots (by decide) PCPFieldMoves.advanceMachine
    (heads pre.length out.length) (tapes C (pre++frame bits++suffix) out) _ _ base hb
  have hi : RecoveryFocus.config moveSlots (heads pre.length out.length)
      (tapes C (pre++frame bits++suffix) out) (PCPFieldMoves.entry pre bits suffix C C)=
      (⟨moveProgram.start,heads pre.length out.length,tapes C (pre++frame bits++suffix) out⟩ : Configuration 17 5) := by
    apply WilliamsSourceCrop.focus_same moveSlots
      (⟨moveProgram.start,heads pre.length out.length,tapes C (pre++frame bits++suffix) out⟩ : Configuration 17 5)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;>
        simp [tapes,moveSlots,PCPFieldMoves.entry,ZeroPadding.config,PCPFieldMoves.caps,
          Rewind.recording,Rewind.config,RepairSource.ProjectionNormalization.Field.cfg,ZeroPadding.pad,Fin.addCases]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hs.trans bs⟩
  · rw [hf]
    simp only [RecoveryFocus.config]
    rw [bh]
    funext i; fin_cases i <;> simp [pick_move,heads]
  · rw [hf]
    change install moveSlots (tapes C (pre++frame bits++suffix) out) base.final.tapes=_
    rw [bt]
    funext i; fin_cases i <;>
      simp [install,pick_move,isolated,tapes,PCPFieldMoves.output,max_eq_left hC]

theorem first_run (negate : Bool) (pre suffix out : List Bool) (C p : Nat) (z : Int)
    (hz : z.natAbs<2^p) (hC : 65*(p+1) ≤ C) :
    ∃ time a r,time ≤ 68*p+73 ∧
      runFrom (first negate) time
        ⟨(first negate).start,heads pre.length out.length,tapes C (pre++frame (signMagnitude p z)++suffix) out⟩=some r ∧
      r.final.heads=heads (pre.length+2*p+3) out.length ∧ r.final.tapes=a ∧
      a 0=pre++frame (signMagnitude p z)++suffix ∧
      a 10=ZeroPadding.pad C (frame (signMagnitude (p+1) (EquationScalar.target negate z))) ∧
      a 13=List.replicate C false ∧ a 14=out ∧ a 15=List.replicate C true ∧
      a 16=List.replicate (C+1) false ∧
      (∀ j,(a (scratchSlots j)).length=C) ∧ r.steps=time := by
  let source := pre++frame (signMagnitude p z)++suffix
  let a := isolated C source out (signMagnitude p z)
  have hcap : 2*(signMagnitude p z).length+1 ≤ C := by simp; omega
  obtain ⟨base,hb,bh,bt,bs⟩ := move_run pre (signMagnitude p z) suffix out C hcap
  obtain ⟨cost,localOut,hcost,hready,_h0,h9,hlen⟩ := EquationScalar.padded_run negate C p z hz hC
  let h := heads (pre.length+2*p+3) out.length
  have ha (j : Fin 12) : a (scalarSlots j)=EquationScalar.paddedInput C p z j := by
    fin_cases j <;>
      simp [a,isolated,tapes,scalarSlots,EquationScalar.paddedInput,EquationScalar.input,ZeroPadding.pad]
  have hh (j : Fin 12) : h (scalarSlots j)=0 := by
    have hn0 : scalarSlots j≠0 := scalar_other _ (Or.inl rfl) j
    have hn14 : scalarSlots j≠14 := scalar_other _ (Or.inr (Or.inr (Or.inl rfl))) j
    simp only [h,heads,hn0,hn14,ite_false]
  obtain ⟨last,hl,lh,lt,ls⟩ := hready.focus_at scalarSlots scalar_injective h a ha hh
  have he : Composition.restart base.final (scalarProgram negate).start=
      (⟨(scalarProgram negate).start,h,a⟩ : Configuration 17 _) := by
    apply configuration_ext
    · rfl
    · change base.final.heads=h
      simpa only [h,signMagnitude_length,Nat.mul_add,Nat.mul_one,Nat.add_assoc,
        show 2+1=3 from rfl] using bh
    · exact bt
  change runFrom (scalarProgram negate) cost ⟨(scalarProgram negate).start,h,a⟩=some last at hl
  rw [←he] at hl
  have joined := Composition.run_join moveProgram (scalarProgram negate) _ _ _ base last hb hl
  let b := install scalarSlots a localOut
  refine ⟨(4*(signMagnitude p z).length+4)+1+cost,b,Composition.joinedReceipt base last,?_,joined,lh,lt,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [signMagnitude_length]; omega
  · change install scalarSlots a localOut 0=_
    rw [install_other _ _ _ _ (scalar_other _ (Or.inl rfl))]
    simp [a,source,isolated,tapes]
  · exact (install_slot scalarSlots scalar_injective a localOut 9).trans h9
  · change install scalarSlots a localOut 13=_
    rw [install_other _ _ _ _ (scalar_other _ (Or.inr (Or.inl rfl)))]
    simp [a,isolated,tapes]
  · change install scalarSlots a localOut 14=_
    rw [install_other _ _ _ _ (scalar_other _ (Or.inr (Or.inr (Or.inl rfl))))]
    simp [a,isolated,tapes]
  · change install scalarSlots a localOut 15=_
    rw [install_other _ _ _ _ (scalar_other _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
    simp [a,isolated,tapes]
  · change install scalarSlots a localOut 16=_
    rw [install_other _ _ _ _ (scalar_other _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]
    simp [a,isolated,tapes]
  · intro j
    by_cases hj : j.val<12
    · let i : Fin 12 := ⟨j.val,hj⟩
      have he : scratchSlots j=scalarSlots i := rfl
      change (install scalarSlots a localOut (scratchSlots j)).length=C
      rw [he,install_slot scalarSlots scalar_injective]
      exact hlen i
    · have he : j=12 := Fin.ext (by omega)
      subst j
      change (install scalarSlots a localOut 13).length=C
      rw [install_other _ _ _ _ (scalar_other _ (Or.inr (Or.inl rfl)))]
      simp [a,isolated,tapes]
  · change base.steps+1+last.steps=_
    rw [bs,ls]

end
end NearCubicWires.RepairOrdinary.EquationScalarStream
