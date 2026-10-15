import Proof.PCP.PCPPNativeQueryTailPadded

/-! Read the two original native descriptor header fields. The actual size
template produced here drives the already checked original-oracle loop. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryHeader
open LocalBitMultitape RepairRepresentation PCPPNativeNodeRead
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine (field 0) (field 1)
def budget (arity size : ℕ) := PCPPQueryNatural.budget arity+1+PCPPQueryNatural.budget size
def source (pre tail : List Bool) (arity size : ℕ) := pre++natWord arity++natWord size++tail
noncomputable def entry (bits : List Bool) (pos : ℕ) :=
  (⟨machine.start,(fun i => if i=0 then pos else 0),(fun i => if i=0 then bits else [])⟩ : Configuration 31 _)

theorem header_run (pre tail : List Bool) (arity size : ℕ) :
    ∃ r,runFrom machine (budget arity size) (entry (source pre tail arity size) pre.length)=some r ∧
      r.steps ≤ budget arity size ∧ r.final.tapes 0=source pre tail arity size ∧
      r.final.heads 0=pre.length+(natWord arity).length+(natWord size).length ∧
      r.final.tapes 10=UnaryTemplate.tape arity ∧ r.final.heads 10=1 ∧
      r.final.tapes 20=UnaryTemplate.tape size ∧ r.final.heads 20=1 := by
  let initial := entry (source pre tail arity size) pre.length
  have fresh (i : Fin 3) (j : Fin 11) (hj : j≠0) :
      initial.tapes (slots i j)=[] ∧ initial.heads (slots i j)=0 := by
    have hn := slots_nonzero i j hj
    simp only [initial,entry,hn,ite_false,and_self]
  obtain ⟨a,ha,as,atapes,ah,a0,ah0,akeep⟩ := stage_run initial 0 pre (natWord size++tail) arity
    (by simp [initial,entry,source,List.append_assoc]) (by rfl) (fresh 0)
  obtain ⟨b,hb,bs,bt,bh,b0,bh0,bkeep⟩ := stage_run a.final 1 (pre++natWord arity) tail size
    (by simpa only [List.append_assoc] using a0)
    (by simpa only [List.length_append] using ah0) (by
      intro j hj
      exact ⟨((akeep 1 (by decide) j hj).1).trans (fresh 1 j hj).1,
        ((akeep 1 (by decide) j hj).2).trans (fresh 1 j hj).2⟩)
  let result := Composition.joinedReceipt a b
  have hr := Composition.run_join (field 0) (field 1) _ _ _ a b ha hb
  refine ⟨result,hr,?_,?_,?_,?_,?_,bt,bh⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · change b.final.tapes 0=_
    simpa only [source,List.append_assoc] using b0
  · change b.final.heads 0=_
    simpa only [List.length_append] using bh0
  · change b.final.tapes (slots 0 10)=_
    rw [(bkeep 0 (by decide) 10 (by decide)).1]
    exact atapes
  · change b.final.heads (slots 0 10)=_
    rw [(bkeep 0 (by decide) 10 (by decide)).2]
    exact ah

end NearCubicWires.RepairOrdinary.PCPPNativeQueryHeader
