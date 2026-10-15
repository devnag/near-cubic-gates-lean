import Proof.CaseAnalysis.RecoveryQueryAppend
import Proof.Circuits.DecompositionCountPosition

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryClear
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions (up : Bool) (i : Fin 60) : HeadMove:=
  if i=42 then if up then .right else .left else .stay
def position (up : Bool):=DecompositionCountPosition.move (directions up)
def heads (H : Fin 60→ℕ) (up : Bool):=Function.update H 42 (if up then 1 else 0)

theorem position_run (up : Bool) (H : Fin 60→ℕ) (A : Fin 60→List Bool)
    (h42 : H 42=if up then 0 else 1) :
    ∃ r,runFrom (position up) 1 ⟨(position up).start,H,A⟩=some r ∧
      r.steps=1 ∧ r.final.heads=heads H up ∧ r.final.tapes=A := by
  obtain ⟨r,hr,hf,hs⟩:=DecompositionCountPosition.move_run (directions up) H A
  refine ⟨r,hr,hs,?_,?_⟩
  · rw [hf]
    funext i
    by_cases hi : i=42
    · subst i
      cases up <;> simp only [directions,heads,Function.update_self,if_true,Bool.false_eq_true,if_false,h42] <;> rfl
    · simp only [directions,if_neg hi,heads,Function.update_of_ne hi]
      rfl
  · rw [hf]

def saved : Fin 6→Fin 60:=![37,42,44,46,49,52]
def slots : Fin 8→Fin 60:=![37,42,44,46,49,52,22,23]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def clear:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 6)
def output (A : Fin 60→List Bool) (C : ℕ) (i : Fin 60):=
  if i=37∨i=42∨i=44∨i=46∨i=49∨i=52 then List.replicate C false else A i

theorem clear_run (H : Fin 60→ℕ) (A : Fin 60→List Bool) (C : ℕ)
    (hH : ∀ j,H (slots j)=0) (hT : A 22=List.replicate C true) (hZ : A 23=List.replicate (C+1) false)
    (hfit : ∀ j,(A (saved j)).length ≤ C) :
    ∃ r,runFrom clear (2*C+4) ⟨clear.start,H,A⟩=some r ∧
      r.steps=2*C+4 ∧ r.final.heads=H ∧ r.final.tapes=output A C := by
  let backing : Fin 6→List Bool:=fun j=>A (saved j)
  have hA : ∀ j,A (slots j)=
      (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate C true))
        (fun _=>List.replicate (C+1) false)) j := by
    intro j
    fin_cases j <;> first | rfl | exact hT | exact hZ
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryScratchErase.erase_ready C (C+1) backing hfit).focus_at slots slots_injective H A hA hH
  have he : install slots A
      (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=output A C := by
    apply HierarchyWidth.install_eq slots slots_injective
    · intro j
      fin_cases j
      all_goals first | rfl | exact hT |
        (change A 23=List.replicate (max (C+1) (C+1)) false;rw [max_self];exact hZ)
    · intro i hi
      have h37 : i≠37:=fun h=>hi 0 h.symm
      have h42 : i≠42:=fun h=>hi 1 h.symm
      have h44 : i≠44:=fun h=>hi 2 h.symm
      have h46 : i≠46:=fun h=>hi 3 h.symm
      have h49 : i≠49:=fun h=>hi 4 h.symm
      have h52 : i≠52:=fun h=>hi 5 h.symm
      simp only [output,h37,h42,h44,h46,h49,h52,or_self,if_false]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

noncomputable def machine:=Composition.machine (position false) clear
theorem retreat_clear_run (H : Fin 60→ℕ) (A : Fin 60→List Bool) (C : ℕ)
    (h42 : H 42=1) (hH : ∀ j,H (slots j)=if j=1 then 1 else 0)
    (hT : A 22=List.replicate C true) (hZ : A 23=List.replicate (C+1) false)
    (hfit : ∀ j,(A (saved j)).length ≤ C) :
    ∃ r,runFrom machine (2*C+6) ⟨machine.start,H,A⟩=some r ∧
      r.steps=2*C+6 ∧ r.final.heads=heads H false ∧ r.final.tapes=output A C := by
  obtain ⟨p,pr,ps,ph,pt⟩:=position_run false H A h42
  have hH' : ∀ j,heads H false (slots j)=0 := by
    intro j
    have h:=hH j
    fin_cases j <;> first | rfl | exact h
  obtain ⟨q,qr,qs,qh,qt⟩:=clear_run (heads H false) A C hH' hT hZ hfit
  have qr' : runFrom clear (2*C+4) (restart p.final clear.start)=some q := by
    change runFrom clear _ ⟨clear.start,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join (position false) clear _ _ _ p q pr qr'
  have he : 1+1+(2*C+4)=2*C+6:=by omega
  rw [he] at full
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps=2*C+6
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryClear
