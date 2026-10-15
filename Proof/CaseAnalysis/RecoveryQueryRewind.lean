import Proof.CaseAnalysis.RecoveryQueryRepeat
import Proof.Hierarchy.CompetitorRecordRewind

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryRewind
open LocalBitMultitape RepairRepresentation Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) : Fin 3→ℕ:=![0,0,C]
def padded (phase : Fin 3) (source : List Bool) (pos C : ℕ) : Configuration 3 3:=
  ⟨phase,![pos,0,0],![source,List.replicate C true,List.replicate C false]⟩
theorem padded_input (source : List Bool) (pos C : ℕ) :
    ZeroPadding.config (caps C) (CompetitorRecordRewind.cfg 0 source pos C 0 0 [])=padded 0 source pos C := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero source
    · exact ZeroPadding.pad_zero (List.replicate C true)
    · rfl
theorem padded_output (source : List Bool) (C : ℕ) :
    ZeroPadding.config (caps C) (CompetitorRecordRewind.cfg 2 source 0 C 0 0 (List.replicate C false))=
      padded 2 source 0 C := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero source
    · exact ZeroPadding.pad_zero (List.replicate C true)
    · change ZeroPadding.pad C (List.replicate C false)=List.replicate C false
      simp only [ZeroPadding.pad,List.length_replicate,Nat.sub_self,List.replicate_zero,List.append_nil]

theorem padded_run (source : List Bool) (C pos : ℕ) (hp : pos ≤ C) :
    ∃ r,runFrom CompetitorRecordRewind.machine (2*C+2) (padded 0 source pos C)=some r ∧
      r.steps=2*C+2 ∧ r.final=padded 2 source 0 C := by
  obtain ⟨p,pr,pf,ps⟩:=CompetitorRecordRewind.rewind_run source C pos hp
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CompetitorRecordRewind.machine (caps C) _ _ p pr
  rw [padded_input] at hr
  rw [pf,padded_output] at rf
  exact ⟨r,hr,rs.trans ps,rf⟩

def selected (address : Bool) : Fin 61:=if address then 58 else 59
def slots (address : Bool) : Fin 3→Fin 61:=![selected address,22,32]
theorem slots_injective (address : Bool) : Function.Injective (slots address):=by cases address <;> decide
noncomputable def rewind (address : Bool):=RecoveryFocus.machine (slots address) CompetitorRecordRewind.machine
def heads (H : Fin 61→ℕ) (address : Bool):=Function.update H (selected address) 0

theorem rewind_run (address : Bool) (H : Fin 61→ℕ) (A : Fin 61→List Bool)
    (source : List Bool) (C pos : ℕ)
    (hH : ∀ j,H (slots address j)=(![pos,0,0] : Fin 3→ℕ) j)
    (hA : ∀ j,A (slots address j)=(![source,List.replicate C true,List.replicate C false] : Fin 3→List Bool) j)
    (hp : pos ≤ C) :
    ∃ r,runFrom (rewind address) (2*C+2) ⟨(rewind address).start,H,A⟩=some r ∧
      r.steps=2*C+2 ∧ r.final.heads=heads H address ∧ r.final.tapes=A := by
  obtain ⟨p,pr,ps,pf⟩:=padded_run source C pos hp
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (slots address) (slots_injective address)
    CompetitorRecordRewind.machine _ H A (padded 0 source pos C) hH hA p pr
  refine ⟨r,hr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots address j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,pf]
      fin_cases j
      · cases address <;> rfl
      · cases address <;> exact (hH 1).symm
      · cases address <;> exact (hH 2).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have hsel : i≠selected address:=fun h=>hi ⟨0,h.symm⟩
      simp only [heads,Function.update_of_ne hsel]
  · funext i
    by_cases hi : ∃ j,slots address j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pf]
      exact (hA j).symm
    · exact (rkeep i (by intro j h;exact hi ⟨j,h⟩)).2

noncomputable def machine:=Composition.machine (rewind false) (rewind true)
theorem both_run (H : Fin 61→ℕ) (A : Fin 61→List Bool) (source refs : List Bool) (C sourcePos refPos : ℕ)
    (h58 : H 58=sourcePos) (h59 : H 59=refPos) (h22 : H 22=0) (h32 : H 32=0)
    (a58 : A 58=source) (a59 : A 59=refs) (a22 : A 22=List.replicate C true) (a32 : A 32=List.replicate C false)
    (hs : sourcePos ≤ C) (hr : refPos ≤ C) :
    ∃ r,runFrom machine (4*C+5) ⟨machine.start,H,A⟩=some r ∧
      r.steps=4*C+5 ∧ r.final.heads=heads (heads H false) true ∧ r.final.tapes=A := by
  obtain ⟨p,pr,ps,ph,pt⟩:=rewind_run false H A refs C refPos
    (by intro j;fin_cases j;exact h59;exact h22;exact h32)
    (by intro j;fin_cases j;exact a59;exact a22;exact a32) hr
  obtain ⟨q,qr,qs,qh,qt⟩:=rewind_run true (heads H false) A source C sourcePos
    (by intro j;fin_cases j;exact h58;exact h22;exact h32)
    (by intro j;fin_cases j;exact a58;exact a22;exact a32) hs
  have qr' : runFrom (rewind true) (2*C+2) (restart p.final (rewind true).start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join (rewind false) (rewind true) _ _ _ p q pr qr'
  have he : (2*C+2)+1+(2*C+2)=4*C+5:=by omega
  rw [he] at full
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps=4*C+5
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryRewind
