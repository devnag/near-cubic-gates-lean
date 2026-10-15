import Proof.PCP.PCPSerializerReuseCopy
import Proof.PCP.PCPTraversalWhole

/-! The accepted whole serializer now runs in the repeated caller's finite
backing. Its result is framed for the paid append, with the source/count
cursors live and every selected scratch head physically restored. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def serializerMachine := machine PCPTraversal.machine
noncomputable def serializerEntry (capacity : ℕ) (source : List Bool) (pos count : ℕ) :=
  ZeroPadding.config (caps capacity) (Rewind.recording (PCPTraversal.entry source pos count) 0)
def serializerHeads (pos : ℕ) (i : Fin 129) : ℕ :=
  Fin.addCases (m:=128) (n:=1) (motive:=fun _ => ℕ)
    (PCPTraversal.heads pos) (fun _ : Fin 1 => 0) i

theorem capacity_le_budget (B : ℕ) : PCPPairReusable.capacity B ≤ PCPTraversal.budget B := by
  have hp : (B+1)^10 ≤ (B+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  unfold PCPPairReusable.capacity PCPTraversal.budget
  omega

theorem serializer_run (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (capacity : ℕ) (hcap : PCPTraversal.budget (mass fields)+1 ≤ capacity) :
    ∃ r,runFrom serializerMachine (2*PCPTraversal.budget (mass fields)+2)
      (serializerEntry capacity (pre++FieldList.stream fields++suffix) pre.length fields.length)=some r ∧
      r.final.heads=serializerHeads (pre.length+(FieldList.stream fields).length) ∧
      r.final.tapes 0=pre++FieldList.stream fields++suffix ∧
      r.final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      r.final.tapes 77=ZeroPadding.pad capacity (frame (PCPTraversal.code fields).bits) ∧
      (∀ i : Fin 129,i≠0 → i≠2 → (r.final.tapes i).length=capacity) ∧
      r.final.tapes 128=List.replicate capacity false ∧
      r.steps ≤ 2*PCPTraversal.budget (mass fields)+2 := by
  obtain ⟨source,hr,h77,_,h0,h2,hh,_,hs⟩ := PCPTraversal.cold_run pre fields suffix
  have hi (i : Fin 128) (hsel : selected i=true) : i≠0 ∧ i≠2 := by
    simpa only [selected,Bool.decide_iff] using hsel
  obtain ⟨r,hrun,hrt,hrh,ht,hsize,hlogHead,hlog⟩ := reset_run PCPTraversal.machine _ capacity
    _ source hr
    (by intro i hsel; simp [PCPTraversal.entry,PCPTraversal.heads,(hi i hsel).1,(hi i hsel).2])
    (by intro i hsel; simp [PCPTraversal.entry,PCPTraversal.input,(hi i hsel).1,(hi i hsel).2])
    (by omega)
  have hrun' := runFrom_moreFuel serializerMachine _
    (2*PCPTraversal.budget (mass fields)+2-(2*source.steps+2)) _ r hrun
  have htime : 2*source.steps+2+
      (2*PCPTraversal.budget (mass fields)+2-(2*source.steps+2))=
      2*PCPTraversal.budget (mass fields)+2 := by omega
  rw [htime] at hrun'
  refine ⟨r,hrun',?_,?_,?_,?_,?_,hlog,by omega⟩
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hrh,hh]
      simp only [serializerHeads,Fin.addCases_left]
      by_cases hj0 : j=0
      · subst j; rfl
      by_cases hj2 : j=2
      · subst j; rfl
      simp [selected,PCPTraversal.heads,hj0,hj2]
    · fin_cases j
      exact hlogHead
  · exact (ht 0).trans ((ZeroPadding.pad_zero _).trans h0)
  · exact (ht 2).trans ((ZeroPadding.pad_zero _).trans h2)
  · have hout := ht 77
    change r.final.tapes 77=ZeroPadding.pad capacity (source.final.tapes 77) at hout
    rw [h77] at hout
    exact hout.trans (PCPPairReusable.pad_nested capacity _ _
      ((capacity_le_budget (mass fields)).trans (by omega)))
  · intro i
    refine Fin.addCases (m:=128) (n:=1)
      (motive:=fun k => k≠0 → k≠2 → (r.final.tapes k).length=capacity)
      (fun j h0 h2 => ?_) (fun j _ _ => ?_) i
    · exact hsize j (by
        simp only [selected,Bool.decide_iff]
        constructor
        · intro hj; subst j; exact h0 rfl
        · intro hj; subst j; exact h2 rfl)
    · fin_cases j
      change (r.final.tapes 128).length=capacity
      rw [hlog,List.length_replicate]

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
