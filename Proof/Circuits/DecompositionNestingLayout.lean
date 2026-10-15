import Proof.Circuits.DecompositionChildOuter

/-! A fixed disjoint workspace for the one native-atom pass followed by the
checked child/outer caller. Four actual fields are shared; all other second
stage tapes are fresh, including four harmless unused positions. -/
namespace NearCubicWires.RepairOrdinary.DecompositionNesting
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 260) : Fin 443 :=
  if j.val=0 then 176 else if j.val=2 then 181 else if j.val=130 then 177
  else if j.val=132 then 182 else j.natAdd 183
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv
  all_goals try simp only [Fin.val_natAdd] at hv
  all_goals omega

def extras (k m : ℕ) (j : Fin 262) : List Bool :=
  if j.val=0 then CompareMachine.word k else if j.val=1 then CompareMachine.word m else []
def extraHeads (j : Fin 262) : ℕ := if j.val=0 ∨ j.val=1 then 1 else 0
noncomputable def first := TapeEmbedding.machine 262 DecompositionAtomStreamReady.machine
noncomputable def second := RecoveryFocus.machine slots DecompositionChildOuter.machine
noncomputable def machine := Composition.machine first second
noncomputable def entry (C T k m : ℕ) (source : List Bool) (pos : ℕ) :=
  (⟨machine.start,
    Fin.addCases (m:=181) (n:=262) (motive:=fun _ => ℕ)
      (DecompositionAtomStreamReady.entry C T source pos).heads extraHeads,
    Fin.addCases (m:=181) (n:=262) (motive:=fun _ => List Bool)
      (DecompositionAtomStreamReady.entry C T source pos).tapes (extras k m)⟩ : Configuration 443 _)

def atomFields (xs : List ℤ) := xs.map (fun z => (CanonicalBinary.encodeInt z).bits)
def fieldGroups (groups : List (List ℤ)) := groups.map atomFields

theorem atom_encoded (groups : List (List ℤ)) :
    DecompositionAtomLoop.encoded groups.flatten=
      DecompositionBalancedGroups.stream (fieldGroups groups) := by
  induction groups with
  | nil => rfl
  | cons xs groups ih =>
    simp only [List.flatten_cons,DecompositionAtomLoop.encoded,List.map_append,
      FieldList.stream,List.flatten_append,fieldGroups,List.map_cons,List.flatten_cons] at ih ⊢
    exact congrArg (fun rest => FieldList.stream (atomFields xs)++rest) ih

def childInput (C k m : ℕ) (source : List Bool) (i : Fin 260) : List Bool :=
  if i.val=0 then source else if i.val=2 then CompareMachine.word k
  else if i.val=130 then List.replicate C true else if i.val=132 then CompareMachine.word m else []
def childHeads (i : Fin 260) : ℕ := if i.val=2 ∨ i.val=132 then 1 else 0

theorem child_entry_tapes (C k m : ℕ) (source : List Bool) :
    (DecompositionChildOuter.entry C k m source).tapes=childInput C k m source := by
  simp only [DecompositionChildOuter.entry,DecompositionChildStreamReady.entry,Rewind.recording,Rewind.config,
    DecompositionGroupsCold.entry]
  funext i
  refine Fin.addCases (m:=134) (n:=126) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=133) (n:=1) (fun q => ?_) (fun q => ?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (m:=132) (n:=1) (fun p => ?_) (fun p => ?_) q
      · simp only [DecompositionGroupsCold.input,Fin.addCases_left]
        change DecompositionGroupsStart.input C k source [] p=
          childInput C k m source (((p.castAdd 1).castAdd 1).castAdd 126)
        simp only [DecompositionGroupsStart.input,childInput,Fin.val_castAdd,
          Fin.ext_iff,Fin.val_zero,show (2 : Fin 132).val=2 from rfl,
          show (129 : Fin 132).val=129 from rfl,show (130 : Fin 132).val=130 from rfl]
        have hp := p.isLt
        split_ifs <;> first | rfl | omega
      · fin_cases p; rfl
    · fin_cases q; rfl
  · have hj : 134+j.val≠0 ∧ 134+j.val≠2 ∧ 134+j.val≠130 ∧ 134+j.val≠132 := by omega
    simp only [Fin.addCases_right,childInput,Fin.val_natAdd,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2,ite_false]

theorem body_heads (p : Fin 132) : PCPSerializerReuse.bodyHeads 0 0 p=if p.val=2 then 1 else 0 := by
  simp only [PCPSerializerReuse.bodyHeads]
  refine Fin.addCases (m:=129) (n:=3) (fun j => ?_) (fun j => ?_) p
  · simp only [Fin.addCases_left,PCPSerializerReuse.serializerHeads,Fin.val_castAdd]
    refine Fin.addCases (m:=128) (n:=1) (fun q => ?_) (fun q => ?_) j
    · simp only [Fin.addCases_left,PCPTraversal.heads,Fin.val_castAdd,Fin.ext_iff,
        Fin.val_zero,show (2 : Fin 128).val=2 from rfl]
      split_ifs <;> omega
    · fin_cases q; rfl
  · fin_cases j <;> rfl

theorem child_entry_heads (C k m : ℕ) (source : List Bool) :
    (DecompositionChildOuter.entry C k m source).heads=childHeads := by
  simp only [DecompositionChildOuter.entry,DecompositionChildStreamReady.entry,Rewind.recording,Rewind.config,
    DecompositionGroupsCold.entry]
  funext i
  refine Fin.addCases (m:=134) (n:=126) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=133) (n:=1) (fun q => ?_) (fun q => ?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (m:=132) (n:=1) (fun p => ?_) (fun p => ?_) q
      · simp only [DecompositionGroupsCold.heads,Fin.addCases_left,List.length_nil]
        change PCPSerializerReuse.bodyHeads 0 0 p=childHeads (((p.castAdd 1).castAdd 1).castAdd 126)
        simp only [body_heads,childHeads,Fin.val_castAdd]
        have hp := p.isLt
        split_ifs <;> omega
      · fin_cases p; rfl
    · fin_cases q; rfl
  · have hj : 134+j.val≠2 ∧ 134+j.val≠132 := by omega
    simp only [Fin.addCases_right,childHeads,Fin.val_natAdd,hj.1,hj.2,false_or,ite_false]

end NearCubicWires.RepairOrdinary.DecompositionNesting
