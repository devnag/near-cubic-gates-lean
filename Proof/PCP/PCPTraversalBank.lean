import Proof.PCP.PCPTraversalFocused

/-! One fresh bank for a counted field stream already produced by the
caller. The source/count slots remain physical; all128 new tapes start blank. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversalBank
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {u : ℕ} (source count : Fin u) (i : Fin 128) : Fin (u+128) :=
  if i=0 then source.castAdd 128 else if i=2 then count.castAdd 128 else i.natAdd u

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
  RecoveryFocus.machine (slots source count) PCPTraversal.machine
def heads {u : ℕ} (h : Fin u → ℕ) : Fin (u+128) → ℕ := Fin.addCases h (fun _ => 0)
def tapes {u : ℕ} (t : Fin u → List Bool) : Fin (u+128) → List Bool := Fin.addCases t (fun _ => [])

theorem bank_run {u : ℕ} (source count : Fin u) (hne : source≠count)
    (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (h : Fin u → ℕ) (t : Fin u → List Bool)
    (hs : h source=pre.length) (hc : h count=1)
    (ts : t source=pre++FieldList.stream fields++suffix)
    (tc : t count=RepairSource.VerifierDecoding.CompareMachine.word fields.length) :
    ∃ r,runFrom (machine source count) (PCPTraversal.budget (mass fields))
      ⟨PCPTraversal.machine.start,heads h,tapes t⟩=some r ∧
      r.final.tapes ((77 : Fin 128).natAdd u)=
        ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (PCPTraversal.code fields).bits) ∧
      r.final.tapes ((78 : Fin 128).natAdd u)=(PCPTraversal.code fields).bits ∧
      r.final.heads ((77 : Fin 128).natAdd u)=0 ∧
      r.final.heads ((78 : Fin 128).natAdd u)=0 ∧
      (∀ i : Fin u,r.final.tapes (i.castAdd 128)=t i) ∧
      (∀ i : Fin u,i≠source → r.final.heads (i.castAdd 128)=h i) ∧
      r.steps ≤ PCPTraversal.budget (mass fields) := by
  have hiH : ∀ j,heads h (slots source count j)=PCPTraversal.heads pre.length j := by
    intro j
    by_cases h0 : j=0
    · subst j
      simpa only [slots,ite_true,heads,Fin.addCases_left,PCPTraversal.heads] using hs
    by_cases h2 : j=2
    · subst j
      simpa only [slots,h0,ite_false,ite_true,heads,Fin.addCases_left,PCPTraversal.heads] using hc
    · simp only [slots,h0,h2,ite_false,heads,Fin.addCases_right,PCPTraversal.heads]
  have hiT : ∀ j,tapes t (slots source count j)=
      PCPTraversal.input (pre++FieldList.stream fields++suffix) fields.length j := by
    intro j
    by_cases h0 : j=0
    · subst j
      simpa only [slots,ite_true,tapes,Fin.addCases_left,PCPTraversal.input] using ts
    by_cases h2 : j=2
    · subst j
      simpa only [slots,h0,ite_false,ite_true,tapes,Fin.addCases_left,PCPTraversal.input] using tc
    · simp only [slots,h0,h2,ite_false,tapes,Fin.addCases_right,PCPTraversal.input]
  obtain ⟨r,hr,r77,r78,r0,r2,rh,other,rs⟩ := PCPTraversal.focused_run
    (slots source count) (slots_injective source count hne) pre fields suffix (heads h) (tapes t) hiH hiT
  have hother (i : Fin u) (hsi : i≠source) (hci : i≠count) :
      ∀ j,slots source count j≠i.castAdd 128 := by
    intro j he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    have hs' : source.val≠i.val := fun h => hsi (Fin.ext h.symm)
    have hc' : count.val≠i.val := fun h => hci (Fin.ext h.symm)
    dsimp only [slots] at hv
    split_ifs at hv <;> dsimp at hv <;> omega
  refine ⟨r,hr,r77,r78,rh 77,rh 78,?_,?_,rs⟩
  · intro i
    by_cases his : i=source
    · subst i
      exact r0.trans ts.symm
    by_cases hic : i=count
    · subst i
      exact r2.trans tc.symm
    · simpa only [tapes,Fin.addCases_left] using (other (i.castAdd 128) (hother i his hic)).1
  · intro i his
    by_cases hic : i=count
    · subst i
      exact (rh 2).trans hc.symm
    · simpa only [heads,Fin.addCases_left] using (other (i.castAdd 128) (hother i his hic)).2

end NearCubicWires.RepairOrdinary.PCPTraversalBank
