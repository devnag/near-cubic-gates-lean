import Proof.Amplification.RecoveryBoundedNativeFoldNode

/-! Paid stack pop, accumulator increment and clearing for the exact fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem first_run (ref acc C z : ℕ) (flag : Bool) (out pre : List Bool) (hC : 2*ref+2 ≤ C) :
    ∃ r, runFrom first (8*ref+9)
      ⟨first.start,heads out (pre.length+2*ref+1),
        data 0 acc C flag out (pre++(frame (List.replicate ref true)).reverse++List.replicate z false) []⟩=some r ∧
      r.final.heads=heads out pre.length ∧
      r.final.tapes=data ref acc C flag out (pre++List.replicate (2*ref+1+z) false)
        (frame (List.replicate ref true)) ∧ r.steps=8*ref+9 := by
  obtain ⟨a,ha,ah,atapes,as⟩:=pop_run ref C z pre hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock popSlots (by decide) PCPUnaryStackPop.machine _
    (heads out (pre.length+2*ref+1))
    (data 0 acc C flag out (pre++(frame (List.replicate ref true)).reverse++List.replicate z false) [])
    (⟨PCPUnaryStackPop.machine.start,![pre.length+2*ref+1,0,0,0,0],
      ![pre++(frame (List.replicate ref true)).reverse++List.replicate z false,
        List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false]⟩ : Configuration 5 _)
    (fun j=>(pop_input ref acc C z flag out pre j).1)
    (fun j=>(pop_input ref acc C z flag out pre j).2) a ha
  refine ⟨r,hr,?_,?_,rs.trans as⟩
  · funext i
    by_cases hs : ∃ j,popSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh j,ah]
      fin_cases j <;> rfl
    · rw [(rkeep i (by simpa using hs)).1]
      have h : i≠31 := by intro he; apply hs; exact ⟨0,he.symm⟩
      fin_cases i
      all_goals first | exact False.elim (h rfl) | simp [heads,Fin.addCases]
  · have he:=HierarchyWidth.install_eq popSlots (by decide)
      (data 0 acc C flag out (pre++(frame (List.replicate ref true)).reverse++List.replicate z false) [])
      r.final.tapes
      ![pre++List.replicate (2*ref+1+z) false,ZeroPadding.pad C (frame (List.replicate ref true)),
        List.replicate C false,ZeroPadding.pad C (List.replicate ref true),List.replicate C false]
      (by intro j; rw [rt j,atapes]) (by intro i hi; exact (rkeep i hi).2)
    rw [pop_tapes] at he
    exact he.symm

theorem increment_run (ref acc C live : ℕ) (flag : Bool) (out stack framed : List Bool)
    (hC : acc+1 ≤ C) :
    ∃ r, runFrom third (2*acc+4)
      ⟨third.start,heads out live,data ref acc C flag out stack framed⟩=some r ∧
      r.final.heads=heads out live ∧ r.final.tapes=data ref (acc+1) C flag out stack framed ∧
      r.steps=2*acc+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready acc C hC).focus_at
    incrementSlots (by decide) (heads out live) (data ref acc C flag out stack framed)
    (fun j=>(increment_input ref acc C live flag out stack framed j).2)
    (fun j=>(increment_input ref acc C live flag out stack framed j).1)
  rw [increment_tapes] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem erase_ready (ref C : ℕ) (framed : List Bool) (hr : ref ≤ C) (hf : framed.length ≤ C) :
    ReadyRun (RecoveryScratchErase.resetMachine 2) (2*C+4)
      ![ZeroPadding.pad C (List.replicate ref true),ZeroPadding.pad C framed,
        List.replicate C true,List.replicate (C+1) false]
      ![List.replicate C false,List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
  have h:=RecoveryScratchErase.erase_ready C (C+1)
    ![ZeroPadding.pad C (List.replicate ref true),ZeroPadding.pad C framed]
    (by
      intro i
      fin_cases i
      · change (ZeroPadding.pad C (List.replicate ref true)).length ≤ C
        simp only [ZeroPadding.pad_length,List.length_replicate]
        omega
      · change (ZeroPadding.pad C framed).length ≤ C
        simp only [ZeroPadding.pad_length]
        omega)
  have hi : (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
        ![ZeroPadding.pad C (List.replicate ref true),ZeroPadding.pad C framed] (fun _=>List.replicate C true))
      (fun _=>List.replicate (C+1) false))=
      ![ZeroPadding.pad C (List.replicate ref true),ZeroPadding.pad C framed,List.replicate C true,List.replicate (C+1) false] := by
    funext i; fin_cases i <;> rfl
  have ho : (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>List.replicate C false) (fun _=>List.replicate C true))
      (fun _=>List.replicate (max (C+1) (C+1)) false))=
      ![List.replicate C false,List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
    simp only [max_self]
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at h
  exact h

theorem erase_run (ref acc C live : ℕ) (flag : Bool) (out stack framed : List Bool)
    (hr : ref ≤ C) (hf : framed.length ≤ C) :
    ∃ r, runFrom last (2*C+4)
      ⟨last.start,heads out live,data ref acc C flag out stack framed⟩=some r ∧
      r.final.heads=heads out live ∧ r.final.tapes=data 0 acc C flag out stack [] ∧ r.steps=2*C+4 := by
  obtain ⟨r,hrun,rh,rt,rs⟩:=(erase_ready ref C framed hr hf).focus_at
    eraseSlots (by decide) (heads out live) (data ref acc C flag out stack framed)
    (fun j=>(erase_input ref acc C live flag out stack framed j).2)
    (fun j=>(erase_input ref acc C live flag out stack framed j).1)
  rw [erase_tapes] at rt
  exact ⟨r,hrun,rh,rt,rs⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
