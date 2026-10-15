import Proof.PCP.PCPPRequestNodeFieldsJoin

/-! Cold three-field native descriptor parsing and canonical natural coding.
The original native stream is consumed continuously, once per field. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeFields
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source (pre tail : List Bool) (a b c : ℕ) := pre++natWord a++natWord b++natWord c++tail
def budget (a b c : ℕ) :=
  (PCPPRequestNatural.budget a+1+PCPPRequestNatural.budget b)+1+PCPPRequestNatural.budget c

theorem cold_run (pre tail : List Bool) (a b c : ℕ) :
    ∃ r,runFrom machine (budget a b c) (entry (source pre tail a b c) pre.length)=some r ∧
      r.steps≤budget a b c ∧ r.final.tapes 0=source pre tail a b c ∧
      r.final.heads 0=pre.length+(natWord a).length+(natWord b).length+(natWord c).length ∧
      (∀ i : Fin 3,∃ padding,r.final.tapes (outputSlot i)=
        frame (CanonicalBinary.encodeNat (![a,b,c] i)).bits++List.replicate padding false) ∧
      (∀ i : Fin 3,r.final.heads (outputSlot i)=0) := by
  let initial := entry (source pre tail a b c) pre.length
  have fresh (i : Fin 3) (j : Fin 136) (hj : j≠0) :
      initial.tapes (slots i j)=[] ∧ initial.heads (slots i j)=0 := by
    have h := slots_nonzero i j hj
    simp only [initial,entry,inputTapes,inputHeads,h,ite_false,and_self]
  obtain ⟨first,hfirst,fs,fout,foh,f0,fh0,fkeep⟩ := stage_run initial 0 pre
    (natWord b++natWord c++tail) a (by simp [initial,entry,inputTapes,source,List.append_assoc])
    (by rfl) (fresh 0)
  obtain ⟨second,hsecond,ss,sout,soh,s0,sh0,skeep⟩ := stage_run first.final 1
    (pre++natWord a) (natWord c++tail) b (by simpa only [List.append_assoc] using f0)
    (by simpa only [List.length_append] using fh0) (by
      intro j hj
      exact ⟨((fkeep 1 (by decide) j hj).1).trans (fresh 1 j hj).1,
        ((fkeep 1 (by decide) j hj).2).trans (fresh 1 j hj).2⟩)
  obtain ⟨third,hthird,ts,tout,toh,t0,th0,tkeep⟩ := stage_run second.final 2
    (pre++natWord a++natWord b) tail c (by simpa only [List.append_assoc] using s0)
    (by simpa only [List.length_append] using sh0) (by
      intro j hj
      exact ⟨((skeep 2 (by decide) j hj).1).trans
          (((fkeep 2 (by decide) j hj).1).trans (fresh 2 j hj).1),
        ((skeep 2 (by decide) j hj).2).trans
          (((fkeep 2 (by decide) j hj).2).trans (fresh 2 j hj).2)⟩)
  obtain ⟨result,hresult,rheads,rtapes,rsteps⟩ := join_three_run (field 0) (field 1) (field 2)
    _ _ _ _ first second third hfirst hsecond hthird
  refine ⟨result,hresult,?_,?_,?_,?_,?_⟩
  · rw [rsteps]
    unfold budget
    omega
  · rw [rtapes]
    exact t0
  · rw [rheads]
    simpa only [List.length_append] using th0
  · intro i
    rw [rtapes]
    fin_cases i
    · obtain ⟨padding,hp⟩ := fout
      refine ⟨padding,?_⟩
      change third.final.tapes (slots 0 85)=_
      rw [(tkeep 0 (by decide) 85 (by decide)).1,(skeep 0 (by decide) 85 (by decide)).1]
      exact hp
    · obtain ⟨padding,hp⟩ := sout
      refine ⟨padding,?_⟩
      change third.final.tapes (slots 1 85)=_
      rw [(tkeep 1 (by decide) 85 (by decide)).1]
      exact hp
    · exact tout
  · intro i
    rw [rheads]
    fin_cases i
    · change third.final.heads (slots 0 85)=0
      rw [(tkeep 0 (by decide) 85 (by decide)).2,(skeep 0 (by decide) 85 (by decide)).2]
      exact foh
    · change third.final.heads (slots 1 85)=0
      rw [(tkeep 1 (by decide) 85 (by decide)).2]
      exact soh
    · exact toh

theorem budget_envelope (a b c : ℕ) :
    budget a b c≤4000000000000000000*(natBitLength a+natBitLength b+natBitLength c+1)^12 := by
  have ha := PCPPRequestNatural.budget_envelope a
  have hb := PCPPRequestNatural.budget_envelope b
  have hc := PCPPRequestNatural.budget_envelope c
  have hpa : (natBitLength a+1)^12≤(natBitLength a+natBitLength b+natBitLength c+1)^12 :=
    Nat.pow_le_pow_left (by omega) 12
  have hpb : (natBitLength b+1)^12≤(natBitLength a+natBitLength b+natBitLength c+1)^12 :=
    Nat.pow_le_pow_left (by omega) 12
  have hpc : (natBitLength c+1)^12≤(natBitLength a+natBitLength b+natBitLength c+1)^12 :=
    Nat.pow_le_pow_left (by omega) 12
  have hone : 1≤(natBitLength a+natBitLength b+natBitLength c+1)^12 := Nat.one_le_pow _ _ (by omega)
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeFields
