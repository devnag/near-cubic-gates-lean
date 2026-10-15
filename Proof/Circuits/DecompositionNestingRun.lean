import Proof.Circuits.DecompositionNestingLayout

/-! One complete native signed-field traversal followed by the same shared
child and outer serializers. Every stream rewind is inside these programs. -/
namespace NearCubicWires.RepairOrdinary.DecompositionNesting
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (C : ℕ) (groups : List (List ℤ)) :=
  DecompositionAtomStreamReady.budget C groups.flatten.length+1+
    DecompositionChildOuter.budget C (fieldGroups groups)

theorem nesting_run (pre : List Bool) (groups : List (List ℤ)) (suffix : List Bool) (k C : ℕ)
    (hcount : ∀ xs∈groups,xs.length=k)
    (hatom : ∀ z∈groups.flatten,DecompositionAtom.budget z+1 ≤ C)
    (hchild : ∀ xs∈groups,PCPTraversal.budget (PCPSerializerMass.mass (atomFields xs))+1 ≤ C) :
    ∃ r,runFrom machine (budget C groups)
      (entry C groups.flatten.length k groups.length
        (pre++DecompositionAtomLoop.stream groups.flatten++suffix) pre.length)=some r ∧
      r.final.tapes 393=(PCPTraversal.code (DecompositionChildOuter.fields (fieldGroups groups))).bits ∧
      r.steps ≤ budget C groups := by
  obtain ⟨base,hb,_,_,bout,bhout,bC,bhC,_,_,bs⟩ :=
    DecompositionAtomStreamReady.atom_run pre groups.flatten suffix C hatom
  let prep := TapeEmbedding.receipt extraHeads (extras k groups.length) base
  have hp := TapeEmbedding.run_embed DecompositionAtomStreamReady.machine extraHeads
    (extras k groups.length) _ _ base hb
  have oldT (i : Fin 181) : prep.final.tapes (i.castAdd 262)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldH (i : Fin 181) : prep.final.heads (i.castAdd 262)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have ef (j : Fin 260) : j.natAdd 183=(⟨j.val+2,by omega⟩ : Fin 262).natAdd 181 := by
    apply Fin.ext
    change 183+j.val=181+(j.val+2)
    omega
  have freshT (j : Fin 260) : prep.final.tapes (j.natAdd 183)=[] := by
    rw [ef]
    have h0 : j.val+2≠0 := by omega
    have h1 : j.val+2≠1 := by omega
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right,extras,h0,h1,ite_false]
  have freshH (j : Fin 260) : prep.final.heads (j.natAdd 183)=0 := by
    rw [ef]
    have h0 : j.val+2≠0 := by omega
    have h1 : j.val+2≠1 := by omega
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right,extraHeads,h0,h1,false_or,ite_false]
  have pt (j : Fin 260) : prep.final.tapes (slots j)=
      (DecompositionChildOuter.entry C k (fieldGroups groups).length
        (DecompositionBalancedGroups.stream (fieldGroups groups))).tapes j := by
    rw [child_entry_tapes]
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldT 176).trans (bout.trans (atom_encoded groups))
    by_cases h2 : j.val=2
    · have he : j=2 := Fin.ext h2
      subst j
      rfl
    by_cases h130 : j.val=130
    · have he : j=130 := Fin.ext h130
      subst j
      exact (oldT 177).trans bC
    by_cases h132 : j.val=132
    · have he : j=132 := Fin.ext h132
      subst j
      simp only [childInput,show (132 : Fin 260).val=132 from rfl,show ¬(132 : ℕ)=0 by decide,
        show ¬(132 : ℕ)=2 by decide,show ¬(132 : ℕ)=130 by decide,ite_false,ite_true,fieldGroups,List.length_map]
      rfl
    simp only [slots,childInput,h0,h2,h130,h132,ite_false]
    exact freshT j
  have ph (j : Fin 260) : prep.final.heads (slots j)=
      (DecompositionChildOuter.entry C k (fieldGroups groups).length
        (DecompositionBalancedGroups.stream (fieldGroups groups))).heads j := by
    rw [child_entry_heads]
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldH 176).trans bhout
    by_cases h2 : j.val=2
    · have he : j=2 := Fin.ext h2
      subst j
      rfl
    by_cases h130 : j.val=130
    · have he : j=130 := Fin.ext h130
      subst j
      exact (oldH 177).trans bhC
    by_cases h132 : j.val=132
    · have he : j=132 := Fin.ext h132
      subst j
      rfl
    simp only [slots,childHeads,h0,h2,h130,h132,false_or,ite_false]
    exact freshH j
  have hc : ∀ xs∈fieldGroups groups,xs.length=k := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    simpa only [atomFields,List.length_map] using hcount ys hy
  have hC : ∀ xs∈fieldGroups groups,PCPTraversal.budget (PCPSerializerMass.mass xs)+1 ≤ C := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    exact hchild ys hy
  obtain ⟨body,hbody,braw,bsteps⟩ := DecompositionChildOuter.child_outer_run (fieldGroups groups) k C hc hC
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config slots slots_injective DecompositionChildOuter.machine
    prep.final.heads prep.final.tapes _ _ body hbody
  have he : RecoveryFocus.config slots prep.final.heads prep.final.tapes
      (DecompositionChildOuter.entry C k (fieldGroups groups).length
        (DecompositionBalancedGroups.stream (fieldGroups groups)))=
      Composition.restart prep.final second.start := by
    apply configuration_ext
    · rfl
    · funext i
      cases hi : RecoveryFocus.pick slots i with
      | none => simp only [RecoveryFocus.config,hi,Composition.restart]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick slots hi
        simp only [RecoveryFocus.config,hi,Composition.restart]
        exact (ph j).symm.trans (congrArg prep.final.heads hj)
    · exact install_existing slots prep.final.tapes _ pt
  rw [he] at hcall
  have whole := Composition.run_join first second _ _ _ prep called hp hcall
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_⟩
  · change called.final.tapes (slots 210)=_
    rw [cf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using braw
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionNesting
