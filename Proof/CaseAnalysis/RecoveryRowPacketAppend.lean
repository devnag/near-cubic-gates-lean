import Proof.CaseAnalysis.RecoveryRowPacketPadded
import Proof.CaseAnalysis.RecoveryGrammarFrame

/-! Scalar and literal appends for the exact original row prototype.
The existing scalar worker is focused into its retained scalar bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputHeads (H : Fin 88→ℕ) (out : List Bool):=Function.update H 75 out.length
def outputData (A : Fin 88→List Bool) (out : List Bool):=Function.update A 75 out
def Appends {s : ℕ} (p : Machine 88 s) (fuel : ℕ) (H : Fin 88→ℕ)
    (A : Fin 88→List Bool) (out result : List Bool) : Prop:=
  ∃ r,runFrom p fuel ⟨p.start,outputHeads H out,outputData A out⟩=some r ∧
    r.steps≤fuel ∧ r.final.heads=outputHeads H result ∧ r.final.tapes=outputData A result

theorem Appends.join {s t u v : ℕ} {p : Machine 88 s} {q : Machine 88 t}
    {H : Fin 88→ℕ} {A : Fin 88→List Bool} {out mid result : List Bool}
    (hp : Appends p u H A out mid) (hq : Appends q v H A mid result) :
    Appends (Composition.machine p q) (u+1+v) H A out result := by
  obtain ⟨r,rr,rs,rh,rt⟩:=hp
  obtain ⟨a,ar,as,ah,aData⟩:=hq
  have ar' : runFrom q v (restart r.final q.start)=some a := by
    change runFrom _ _ ⟨_,r.final.heads,r.final.tapes⟩=some a
    rw [rh,rt]
    exact ar
  have whole:=Composition.run_join p q _ _ _ r a rr ar'
  refine ⟨joinedReceipt r a,whole,?_,ah,aData⟩
  change r.steps+1+a.steps≤_
  omega

def slots (source : Fin 88) : Fin 3→Fin 88:=![source,75,73]
noncomputable def scalar (source : Fin 88):=RecoveryFocus.machine (slots source) RecoveryBoundedGrammarFrame.machine

theorem scalar_run (source : Fin 88) (n B : ℕ) (out : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool) (hs : source≠75) (hl : source≠73)
    (hHs : H source=0) (hHl : H 73=0) (hAs : A source=List.replicate n true)
    (hAl : A 73=List.replicate B false) (hB : 2*n+4≤B) :
    Appends (scalar source) (4*n+8) H A out (out++frame (List.replicate n true)) := by
  have hinj : Function.Injective (slots source) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slots]
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedGrammarFrame.append_run n B out hB
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (slots source) hinj RecoveryBoundedGrammarFrame.machine
    _ (outputHeads H out) (outputData A out) (RecoveryBoundedGrammarFrame.input n B out)
    (by intro j;fin_cases j
        · change Function.update H 75 out.length source=0
          rw [Function.update_of_ne hs]
          exact hHs
        · rfl
        · change Function.update H 75 out.length 73=0
          rw [Function.update_of_ne (by decide)]
          exact hHl)
    (by intro j;fin_cases j
        · change Function.update A 75 out source=ZeroPadding.pad 0 (List.replicate n true)
          rw [Function.update_of_ne hs,ZeroPadding.pad_zero]
          exact hAs
        · change out=ZeroPadding.pad 0 out
          exact (ZeroPadding.pad_zero out).symm
        · change Function.update A 75 out 73=ZeroPadding.pad B []
          rw [Function.update_of_ne (by decide),hAl]
          simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots source j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      · change 0=Function.update H 75 _ source
        rw [Function.update_of_ne hs]
        exact hHs.symm
      · rfl
      · change 0=Function.update H 75 _ 73
        rw [Function.update_of_ne (by decide)]
        exact hHl.symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      have h75 : i≠75:=fun he=>hi ⟨1,he.symm⟩
      simp only [outputHeads,Function.update_of_ne h75]
  · funext i
    by_cases hi : ∃ j,slots source j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · change List.replicate n true=Function.update A 75 _ source
        rw [Function.update_of_ne hs]
        exact hAs.symm
      · rfl
      · change List.replicate B false=Function.update A 75 _ 73
        rw [Function.update_of_ne (by decide)]
        exact hAl.symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).2]
      have h75 : i≠75:=fun he=>hi ⟨1,he.symm⟩
      simp only [outputData,Function.update_of_ne h75]

def wordSlots : Fin 1→Fin 88:=fun _=>75
noncomputable def write (bits : List Bool):=RecoveryFocus.machine wordSlots (HierarchyFixedWord.raw bits)

theorem write_run (bits out : List Bool) (H : Fin 88→ℕ) (A : Fin 88→List Bool) :
    Appends (write bits) bits.length H A out (out++bits) := by
  obtain ⟨p,pr,pf,ps⟩:=RepairSource.ProjectionNormalization.Constants.write_run bits out
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock wordSlots (by decide)
    (HierarchyFixedWord.raw bits) _ (outputHeads H out) (outputData A out)
    (RepairSource.ProjectionNormalization.Constants.cfg bits out 0 (by omega))
    (by intro j;fin_cases j;rfl)
    (by intro j;fin_cases j;change out=out++bits.take 0;simp) p pr
  refine ⟨r,rr,rs.le.trans ps.le,?_,?_⟩
  · funext i
    by_cases hi : i=75
    · subst i
      change r.final.heads (wordSlots 0)=_
      rw [rh 0,pf]
      change out.length+bits.length=(out++bits).length
      exact List.length_append.symm
    · rw [(rkeep i (by intro j;fin_cases j;exact fun he=>hi he.symm)).1]
      simp only [outputHeads,Function.update_of_ne hi]
  · funext i
    by_cases hi : i=75
    · subst i
      change r.final.tapes (wordSlots 0)=_
      rw [rt 0,pf]
      change out++bits.take bits.length=out++bits
      rw [List.take_length]
    · rw [(rkeep i (by intro j;fin_cases j;exact fun he=>hi he.symm)).2]
      simp only [outputData,Function.update_of_ne hi]

def header (sentinel : Bool) : List Bool:=if sentinel then [true,false] else []
def field (sentinel : Bool) (n : ℕ):=header sentinel++frame (List.replicate n true)
noncomputable def scalarField (source : Fin 88) (sentinel : Bool):=
  Composition.machine (write (header sentinel)) (scalar source)
def fieldBudget (sentinel : Bool) (n : ℕ):=(header sentinel).length+1+(4*n+8)

theorem field_run (source : Fin 88) (sentinel : Bool) (n B : ℕ) (out : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool) (hs : source≠75) (hl : source≠73)
    (hHs : H source=0) (hHl : H 73=0) (hAs : A source=List.replicate n true)
    (hAl : A 73=List.replicate B false) (hB : 2*n+4≤B) :
    Appends (scalarField source sentinel) (fieldBudget sentinel n) H A out (out++field sentinel n) := by
  have a:=write_run (header sentinel) out H A
  have b:=scalar_run source n B (out++header sentinel) H A hs hl hHs hHl hAs hAl hB
  simpa only [scalarField,fieldBudget,field,List.append_assoc] using a.join b

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
