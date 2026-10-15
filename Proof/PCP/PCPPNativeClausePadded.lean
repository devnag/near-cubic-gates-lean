import Proof.PCP.PCPPNativeClauseFieldRead
import Proof.PCP.PCPSerializerTapeSupport

/-! Reuse the original literal trace on physically allocated work tapes.
The support bound is local to blank work, independent of the source prefix. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseField
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev work (i : Fin 19) : Prop := i≠4 ∧ i≠5 ∧ i≠6 ∧ i≠13
def caps (C : ℕ) (i : Fin 19) := if work i then C else 0
def paddedInput (source : List Bool) (stride p n C : ℕ) (i : Fin 19) :=
  ZeroPadding.pad (caps C i) (input source stride p n i)

theorem work_input (source : List Bool) (stride p n : ℕ) (i : Fin 19) (hi : work i) :
    input source stride p n i=[] := by
  rcases hi with ⟨h4,h5,h6,h13⟩
  simp only [input,h13,h4,h5,h6,ite_false]

theorem padded_run (pre bits tail : List Bool) (index : ℕ) (sign : Bool)
    (stride p n C : ℕ) (hv : value bits=2*index+sign.toNat)
    (hC : budget bits index sign stride p n+1 ≤ C) : ∃ r,
    runFrom machine (budget bits index sign stride p n)
      (entry machine pre.length (paddedInput (pre++frame bits++tail) stride p n C))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes 11=ZeroPadding.pad C (List.replicate
        (index*stride+PCPPNativeClauseReference.offset sign p n) true) ∧
      r.final.tapes 13=pre++frame bits++tail ∧
      r.final.tapes 4=UnaryTemplate.tape stride ∧
      r.final.tapes 5=List.replicate p true ∧
      r.final.tapes 6=List.replicate n true ∧
      (∀ i,work i → (r.final.tapes i).length ≤ C) ∧
      r.steps ≤ budget bits index sign stride p n := by
  obtain ⟨base,hb,bh,b11,b13,b4,b5,b6,bs⟩ := field_run pre bits tail index sign stride p n hv
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config machine (caps C) _ _ base hb
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_,rs.le.trans bs⟩
  · rw [rf]
    exact bh
  · rw [rf]
    change ZeroPadding.pad C (base.final.tapes 11)=_
    rw [b11]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 13)=_
    rw [ZeroPadding.pad_zero,b13]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 4)=_
    rw [ZeroPadding.pad_zero,b4]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 5)=_
    rw [ZeroPadding.pad_zero,b5]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 6)=_
    rw [ZeroPadding.pad_zero,b6]
  · intro i hi
    have ht := PCPSerializerReuse.tape_support machine _ _ base hb i 0 0
      (by change heads pre.length i ≤ 0; simp only [heads,hi.2.2.2,ite_false]; rfl)
      (by change (input _ stride p n i).length ≤ max 0 (0+1); rw [work_input _ _ _ _ i hi]; decide)
    rw [rf]
    change (ZeroPadding.pad (caps C i) (base.final.tapes i)).length ≤ C
    rw [ZeroPadding.pad_length,caps,if_pos hi]
    exact max_le le_rfl (ht.trans (by omega))

end NearCubicWires.RepairOrdinary.PCPPNativeClauseField
