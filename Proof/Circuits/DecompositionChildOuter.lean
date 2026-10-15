import Proof.Circuits.DecompositionChildStreamReady

/-! Complete child grouping and outer-list serialization using the same
balanced serializer. The emitted child stream is physically rewound and
then read by a fresh outer call, with the actual child count retained. -/
namespace NearCubicWires.RepairOrdinary.DecompositionChildOuter
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def packed (j : Fin 128) : Fin 126 := ⟨if j.val=1 then 0 else j.val-2,by split_ifs <;> omega⟩
def slots (j : Fin 128) : Fin 260 :=
  if j=0 then 129 else if j=2 then 132 else (packed j).natAdd 134
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv
  all_goals try simp only [Fin.val_natAdd,packed] at hv
  all_goals simp only [Fin.ext_iff,Fin.val_zero,show (2 : Fin 128).val=2 from rfl] at *
  all_goals first | omega | (split_ifs at hv <;> omega)

def fields (groups : List (List (List Bool))) := groups.map (fun xs => (PCPTraversal.code xs).bits)
noncomputable def first := TapeEmbedding.machine 126 DecompositionChildStreamReady.machine
noncomputable def outer := RecoveryFocus.machine slots PCPTraversal.machine
noncomputable def machine := Composition.machine first outer
noncomputable def entry (C count M : ℕ) (source : List Bool) :=
  (⟨machine.start,
    Fin.addCases (m:=134) (n:=126) (motive:=fun _ => ℕ)
      (DecompositionChildStreamReady.entry C count M source 0).heads (fun _ : Fin 126 => 0),
    Fin.addCases (m:=134) (n:=126) (motive:=fun _ => List Bool)
      (DecompositionChildStreamReady.entry C count M source 0).tapes (fun _ : Fin 126 => [])⟩ : Configuration 260 _)
def budget (C : ℕ) (groups : List (List (List Bool))) :=
  DecompositionChildStreamReady.budget C groups.length+1+PCPTraversal.budget (PCPSerializerMass.mass (fields groups))

theorem child_outer_run (groups : List (List (List Bool))) (count C : ℕ)
    (hcount : ∀ xs∈groups,xs.length=count)
    (hcap : ∀ xs∈groups,PCPTraversal.budget (PCPSerializerMass.mass xs)+1 ≤ C) :
    ∃ r,runFrom machine (budget C groups)
      (entry C count groups.length (DecompositionBalancedGroups.stream groups))=some r ∧
      r.final.tapes 210=(PCPTraversal.code (fields groups)).bits ∧
      r.steps ≤ budget C groups := by
  obtain ⟨base,hb,_,_,bout,bhout,_,_,_,_,bm,bhm,bs⟩ :=
    DecompositionChildStreamReady.child_run [] groups [] count C hcount hcap
  simp only [List.nil_append,List.append_nil,List.length_nil] at hb
  let prep := TapeEmbedding.receipt (fun _ : Fin 126 => 0) (fun _ : Fin 126 => []) base
  have hp := TapeEmbedding.run_embed DecompositionChildStreamReady.machine
    (fun _ : Fin 126 => 0) (fun _ : Fin 126 => []) _ _ base hb
  have pt (j : Fin 128) : prep.final.tapes (slots j)=PCPTraversal.input (DecompositionBalancedGroups.encoded groups)
      (fields groups).length j := by
    by_cases h0 : j=0
    · subst j; exact bout
    by_cases h2 : j=2
    · subst j
      change base.final.tapes 132=CompareMachine.word (fields groups).length
      simpa only [fields,List.length_map] using bm
    simp only [slots,h0,h2,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right,
      PCPTraversal.input]
  have ph (j : Fin 128) : prep.final.heads (slots j)=PCPTraversal.heads 0 j := by
    by_cases h0 : j=0
    · subst j; exact bhout
    by_cases h2 : j=2
    · subst j; exact bhm
    simp only [slots,h0,h2,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right,
      PCPTraversal.heads]
  obtain ⟨body,hbody,_,braw,_,_,_,_,bsteps⟩ := PCPTraversal.cold_run [] (fields groups) []
  simp only [List.nil_append,List.append_nil,List.length_nil] at hbody
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config slots slots_injective PCPTraversal.machine
    prep.final.heads prep.final.tapes _ _ body hbody
  have he : RecoveryFocus.config slots prep.final.heads prep.final.tapes
      (PCPTraversal.entry (FieldList.stream (fields groups)) 0 (fields groups).length)=
      Composition.restart prep.final outer.start := by
    apply configuration_ext
    · rfl
    · funext i
      cases hi : RecoveryFocus.pick slots i with
      | none => simp only [RecoveryFocus.config,hi,Composition.restart]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick slots hi
        simp only [RecoveryFocus.config,hi,PCPTraversal.entry,Composition.restart]
        exact (ph j).symm.trans (congrArg prep.final.heads hj)
    · exact install_existing slots prep.final.tapes _ pt
  rw [he] at hcall
  have whole := Composition.run_join first outer _ _ _ prep called hp hcall
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_⟩
  · change called.final.tapes (slots 78)=_
    rw [cf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using braw
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionChildOuter
