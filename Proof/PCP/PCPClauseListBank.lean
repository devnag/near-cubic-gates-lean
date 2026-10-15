import Proof.PCP.PCPClauseListFocused

/-! The whole clause-list supplier consumes the retained native fields in
a fresh309-tape bank; all other caller data and heads are preserved. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseBank
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {u : ℕ} (source count : Fin u) (i : Fin 309) : Fin (u+309) :=
  if i=0 then count.castAdd 309 else if i=5 then source.castAdd 309 else i.natAdd u
theorem slots_injective {u : ℕ} (source count : Fin u) (hne : source≠count) :
    Function.Injective (slots source count) := by
  intro i j he
  have hv := congrArg Fin.val he
  have hs := source.isLt
  have hc := count.isLt
  have hne' : source.val≠count.val := fun h => hne (Fin.ext h)
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

noncomputable def machine {u : ℕ} (source count : Fin u) :=
  RecoveryFocus.machine (slots source count) PCPClauseList.machine
def heads {u : ℕ} (h : Fin u → ℕ) : Fin (u+309) → ℕ := Fin.addCases h (fun _ => 0)
def tapes {u : ℕ} (t : Fin u → List Bool) : Fin (u+309) → List Bool := Fin.addCases t (fun _ => [])

theorem bank_run {u : ℕ} (source count : Fin u) (hne : source≠count)
    (groups : List (List (List Bool))) (hthree : ∀ fs∈groups,fs.length=3)
    (h : Fin u → ℕ) (t : Fin u → List Bool)
    (hs : h source=0) (hc : h count=1)
    (ts : t source=PCPTripleLoop.stream groups)
    (tc : t count=RepairSource.VerifierDecoding.CompareMachine.word groups.length) :
    ∃ r,runFrom (machine source count) (PCPClauseList.budget groups)
      ⟨PCPClauseList.machine.start,heads h,tapes t⟩=some r ∧
      r.final.tapes ((258 : Fin 309).natAdd u)=
        ZeroPadding.pad (PCPPairReusable.capacity (mass (PCPClauseList.fields groups)))
          (frame (PCPTraversal.code (PCPClauseList.fields groups)).bits) ∧
      r.final.tapes ((259 : Fin 309).natAdd u)=(PCPTraversal.code (PCPClauseList.fields groups)).bits ∧
      r.final.heads ((258 : Fin 309).natAdd u)=0 ∧
      r.final.heads ((259 : Fin 309).natAdd u)=0 ∧
      (∀ i : Fin u,i≠source → i≠count →
        r.final.tapes (i.castAdd 309)=t i ∧ r.final.heads (i.castAdd 309)=h i) ∧
      r.steps ≤ PCPClauseList.budget groups := by
  have hiH : ∀ j,heads h (slots source count j)=PCPClauseList.inputHeads j := by
    intro j
    by_cases h0 : j=0
    · subst j
      simpa only [slots,ite_true,heads,Fin.addCases_left,PCPClauseList.inputHeads] using hc
    by_cases h5 : j=5
    · subst j
      simpa only [slots,h0,ite_false,ite_true,heads,Fin.addCases_left,PCPClauseList.inputHeads] using hs
    · simp only [slots,h0,h5,ite_false,heads,Fin.addCases_right,PCPClauseList.inputHeads]
  have hiT : ∀ j,tapes t (slots source count j)=
      PCPClauseList.inputTapes groups.length (PCPTripleLoop.stream groups) j := by
    intro j
    by_cases h0 : j=0
    · subst j
      simpa only [slots,ite_true,tapes,Fin.addCases_left,PCPClauseList.inputTapes] using tc
    by_cases h5 : j=5
    · subst j
      simpa only [slots,h0,ite_false,ite_true,tapes,Fin.addCases_left,PCPClauseList.inputTapes] using ts
    · simp only [slots,h0,h5,ite_false,tapes,Fin.addCases_right,PCPClauseList.inputTapes]
  obtain ⟨r,hr,r258,r259,rh258,rh259,other,rs⟩ := PCPClauseList.focused_run
    (slots source count) (slots_injective source count hne) groups hthree (heads h) (tapes t) hiH hiT
  have hother (i : Fin u) (hsi : i≠source) (hci : i≠count) :
      ∀ j,slots source count j≠i.castAdd 309 := by
    intro j he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    have hs' : source.val≠i.val := fun h => hsi (Fin.ext h.symm)
    have hc' : count.val≠i.val := fun h => hci (Fin.ext h.symm)
    dsimp only [slots] at hv
    split_ifs at hv <;> dsimp at hv <;> omega
  refine ⟨r,hr,r258,r259,rh258,rh259,?_,rs⟩
  intro i his hic
  simpa only [tapes,heads,Fin.addCases_left] using other (i.castAdd 309) (hother i his hic)

end NearCubicWires.RepairOrdinary.PCPClauseBank
