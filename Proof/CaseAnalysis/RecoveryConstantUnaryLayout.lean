import Proof.CaseAnalysis.RecoveryConstantBank

/-! The exact unary call ports inside the retained child-results bank.
Its one log is the already allocated cubic D tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def unarySlots (j : Fin 37) : Fin 48:=if j=36 then 39 else j.castAdd 11
theorem unary_injective : Function.Injective unarySlots := by decide
theorem unary_slot_old (j : Fin 36) : unarySlots (j.castAdd 1)=j.castAdd 12 := by
  have hn : j.castAdd 1≠(36 : Fin 37) := by
    intro he
    have h:=congrArg Fin.val he
    have hj:=j.isLt
    change j.val=36 at h
    omega
  rw [unarySlots,if_neg hn]
  rfl
noncomputable def unary:=RecoveryFocus.machine unarySlots RecoveryBoundedUnaryReuse.machine

theorem unary_heads (out : List Bool) : ∀ j,heads out (unarySlots j)=RecoveryBoundedUnaryReuse.heads out j := by
  intro j
  fin_cases j <;> rfl

theorem unary_tapes (index base C D limit total L : ℕ) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (savedFirst savedSecond : List Bool) (hC : 1 ≤ C) :
    ∀ j,data index base C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond (unarySlots j)=
      RecoveryBoundedUnaryReuse.data index base C D 1 limit false out j := by
  intro j
  fin_cases j
  all_goals first | rfl |
    (change List.replicate C false=ZeroPadding.pad C (List.replicate 1 false);
      exact (RecoveryBoundedSelectorLoop.pad_erased C 1 hC).symm)

def afterUnary (index base C D limit total L : ℕ) (flag : Bool) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (savedFirst savedSecond : List Bool) (i : Fin 48):=
  if i=1 then List.replicate C false else if i=29 then ZeroPadding.pad C [flag]
  else data index base C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond i

theorem unary_output (index base C D limit total L : ℕ) (flag : Bool) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (savedFirst savedSecond : List Bool) :
    ∀ j,afterUnary index base C D limit total L flag out source secondIndex firstIndex savedFirst savedSecond (unarySlots j)=
      RecoveryBoundedUnaryReuse.data 0 base C D 1 limit flag out j := by
  intro j
  fin_cases j <;> rfl

theorem heads_other (before after : List Bool) (i : Fin 48) (hi : i≠20) : heads before i=heads after i := by
  fin_cases i
  all_goals first | exact False.elim (hi rfl) | (change (0 : ℕ)=0;rfl) | (change (1 : ℕ)=1;rfl)

theorem unary_final_heads (before after : List Bool) :
    (fun i=>match RecoveryFocus.pick unarySlots i with
      | some j=>RecoveryBoundedUnaryReuse.heads after j | none=>heads before i)=heads after := by
  funext i
  cases hp : RecoveryFocus.pick unarySlots i with
  | none=>
    have hi : i≠20 := by
      intro he
      subst i
      have h:=RecoveryFocus.pick_slot unarySlots unary_injective 20
      change RecoveryFocus.pick unarySlots (20 : Fin 48)=some 20 at h
      rw [hp] at h
      contradiction
    exact heads_other before after i hi
  | some j=>
    have he:=RecoveryFocus.slot_of_pick unarySlots hp
    rw [←he]
    exact (unary_heads after j).symm

theorem unary_install (index base acc C D limit total L : ℕ) (flag : Bool) (out resultOut source : List Bool)
    (secondIndex firstIndex : ℕ) (savedFirst savedSecond : List Bool) :
    install unarySlots (data index base C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond)
      (RecoveryBoundedUnaryReuse.data 0 acc C D 1 limit flag resultOut)=
      afterUnary index acc C D limit total L flag resultOut source secondIndex firstIndex savedFirst savedSecond := by
  apply HierarchyWidth.install_eq unarySlots unary_injective
  · exact unary_output index acc C D limit total L flag resultOut source secondIndex firstIndex savedFirst savedSecond
  · intro i
    refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
    · intro hi
      exact False.elim (hi (j.castAdd 1) (unary_slot_old j))
    · intro hi
      fin_cases j
      all_goals first | exact False.elim (hi 36 rfl) |
        (change List.replicate C false=List.replicate C false;rfl) |
        (change source=source;rfl) |
        (change ZeroPadding.pad C (List.replicate index true)=ZeroPadding.pad C (List.replicate index true);rfl) |
        (change RepairSource.VerifierDecoding.CompareMachine.word total=RepairSource.VerifierDecoding.CompareMachine.word total;rfl) |
        (change List.replicate L false=List.replicate L false;rfl) |
        (change List.replicate secondIndex true=List.replicate secondIndex true;rfl) |
        (change List.replicate firstIndex true=List.replicate firstIndex true;rfl) |
        (change savedFirst=savedFirst;rfl) | (change savedSecond=savedSecond;rfl)

end NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
