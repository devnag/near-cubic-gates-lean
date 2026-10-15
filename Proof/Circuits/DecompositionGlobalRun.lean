import Proof.Circuits.DecompositionGlobalLayout

/-! The complete original-input decomposition serializer. Capacity remains
abstract at this join; its equality to the physically produced polynomial
is an explicit data equality, not a supplied tape. -/
namespace NearCubicWires.RepairOrdinary.DecompositionGlobal
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flatten_count (groups : List (List ℤ)) (k : ℕ)
    (hc : ∀ xs∈groups,xs.length=k) : groups.flatten.length=k*groups.length := by
  induction groups with
  | nil => simp
  | cons xs groups ih =>
    have hx := hc xs (by simp)
    have ht := ih (fun ys hy => hc ys (by simp [hy]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,hx,ht]
    ring

theorem global_run (D C E a : ℕ) (groups : List (List ℤ))
    (hcount : ∀ xs∈groups,xs.length=a+1)
    (hE : E=C*((frame (DecompositionInputCounts.word a groups.length
      (DecompositionAtomLoop.stream groups.flatten))).length+1)^D)
    (hatom : ∀ z∈groups.flatten,DecompositionAtom.budget z+1 ≤ E)
    (hchild : ∀ xs∈groups,PCPTraversal.budget
      (PCPSerializerMass.mass (DecompositionNesting.atomFields xs))+1 ≤ E) :
    ∃ r,run (machine D C) (budget D C E a groups)
      (input D (DecompositionInputCounts.word a groups.length (DecompositionAtomLoop.stream groups.flatten)))=some r ∧
      r.final.tapes (outputSlot D)=
        (PCPTraversal.code (DecompositionChildOuter.fields (DecompositionNesting.fieldGroups groups))).bits ∧
      r.steps ≤ budget D C E a groups := by
  let source := DecompositionInputCounts.word a groups.length (DecompositionAtomLoop.stream groups.flatten)
  let pre := RepairRepresentation.natWord a++RepairRepresentation.natWord groups.length
  have hT := flatten_count groups (a+1) hcount
  obtain ⟨base,hb,_,_,bsource,bpos,bcount,bheads,bcap,bch,bs⟩ :=
    DecompositionColdPrepare.prepare_run D C a groups.length (DecompositionAtomLoop.stream groups.flatten)
  let prep := TapeEmbedding.receipt (fun _ : Fin 443 => 0) (fun _ : Fin 443 => []) base
  have hp := TapeEmbedding.run_embed (DecompositionColdPrepare.machine D C)
    (fun _ : Fin 443 => 0) (fun _ : Fin 443 => []) _ _ base hb
  have oldT (i : Fin (DecompositionColdPrepare.tapes D)) :
      prep.final.tapes (i.castAdd 443)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin (DecompositionColdPrepare.tapes D)) :
      prep.final.heads (i.castAdd 443)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have pt (j : Fin 443) : prep.final.tapes (slots D j)=
      (DecompositionNesting.entry E groups.flatten.length (a+1) groups.length source pre.length).tapes j := by
    rw [DecompositionNesting.entry_tapes]
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldT _).trans bsource
    by_cases h177 : j.val=177
    · have he : j=177 := Fin.ext h177
      subst j
      exact (oldT _).trans (bcap.trans (congrArg (fun n => List.replicate n true) hE.symm))
    by_cases h179 : j.val=179
    · have he : j=179 := Fin.ext h179
      subst j
      have ht := (oldT _).trans (bcount 12)
      change prep.final.tapes (slots D 179)=RepairSource.VerifierDecoding.CompareMachine.word groups.flatten.length
      rw [hT]
      exact ht
    by_cases h181 : j.val=181
    · have he : j=181 := Fin.ext h181
      subst j
      exact (oldT _).trans (bcount 4)
    by_cases h182 : j.val=182
    · have he : j=182 := Fin.ext h182
      subst j
      exact (oldT _).trans (bcount 6)
    simp only [slots,DecompositionNesting.nativeInput,h0,h177,h179,h181,h182,ite_false,
      prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_right]
  have ph (j : Fin 443) : prep.final.heads (slots D j)=
      (DecompositionNesting.entry E groups.flatten.length (a+1) groups.length source pre.length).heads j := by
    rw [DecompositionNesting.entry_heads]
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldH _).trans bpos
    by_cases h177 : j.val=177
    · have he : j=177 := Fin.ext h177
      subst j
      exact (oldH _).trans bch
    by_cases h179 : j.val=179
    · have he : j=179 := Fin.ext h179
      subst j
      exact (oldH _).trans (bheads 12)
    by_cases h181 : j.val=181
    · have he : j=181 := Fin.ext h181
      subst j
      exact (oldH _).trans (bheads 4)
    by_cases h182 : j.val=182
    · have he : j=182 := Fin.ext h182
      subst j
      exact (oldH _).trans (bheads 6)
    simp only [slots,DecompositionNesting.nativeHeads,h0,h177,h179,h181,h182,false_or,ite_false,
      prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_right]
  obtain ⟨body,hbody,bout,bstep⟩ := DecompositionNesting.nesting_run pre groups [] (a+1) E hcount hatom hchild
  have source_eq : pre++DecompositionAtomLoop.stream groups.flatten++[]=source := by
    simp only [List.append_nil]
    rfl
  rw [source_eq] at hbody
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config (slots D) (slots_injective D)
    DecompositionNesting.machine prep.final.heads prep.final.tapes _ _ body hbody
  have he : RecoveryFocus.config (slots D) prep.final.heads prep.final.tapes
      (DecompositionNesting.entry E groups.flatten.length (a+1) groups.length source pre.length)=
      Composition.restart prep.final (second D).start := by
    apply configuration_ext
    · rfl
    · funext i
      cases hi : RecoveryFocus.pick (slots D) i with
      | none => simp only [RecoveryFocus.config,hi,Composition.restart]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick (slots D) hi
        simp only [RecoveryFocus.config,hi,Composition.restart]
        exact (ph j).symm.trans (congrArg prep.final.heads hj)
    · exact install_existing (slots D) prep.final.tapes _ pt
  rw [he] at hcall
  have whole := Composition.run_join (first D C) (second D) _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 443 => 0)
      (fun _ : Fin 443 => []) (initialConfiguration (DecompositionColdPrepare.machine D C)
        (DecompositionColdPrepare.input D source)))=
      initialConfiguration (machine D C) (input D source) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=DecompositionColdPrepare.tapes D) (n:=443) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_left,initialConfiguration]
      · simp only [Composition.leftConfig,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_right,initialConfiguration]
    · rfl
  rw [hin] at whole
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_⟩
  · change called.final.tapes (slots D 393)=_
    rw [cf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots D) (slots_injective D)] using bout
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionGlobal
