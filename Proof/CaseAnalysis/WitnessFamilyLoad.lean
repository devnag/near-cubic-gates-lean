import Proof.CaseAnalysis.WitnessSumRound

/-! Each accepted outer-family field is loaded once into the shared sum
bank. Its verdict cell is then reset in one real step before the sum
header starts; previous logical output prefixes are never traversed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (position : ℕ) (base : Fin 3061 → ℕ) : Fin 3063 → ℕ :=
  Fin.addCases (m:=3061) (n:=2) (motive:=fun _=>ℕ) base ![position,0]
def data (H : ℕ) (base : Fin 3061 → List Bool) (source : List Bool) : Fin 3063 → List Bool :=
  Fin.addCases (m:=3061) (n:=2) (motive:=fun _=>List Bool) base ![source,List.replicate H false]
def slots : Fin 3 → Fin 3063 := ![3061,2534,3062]
noncomputable def loader:=RecoveryFocus.machine slots FrameLoad.machine

def prime : Machine 3063 2 where
  descriptionBits:=0
  start:=0
  halted:=fun state=>state.val==1
  rule:=fun state _=>if state.val=0 then
    some ⟨1,fun i=>if i=724 then some false else none,fun _=>.stay⟩ else none

theorem prime_run (baseHeads : Fin 3063 → ℕ) (input : Fin 3063 → List Bool)
    (hh : baseHeads 724=0) (ht : input 724=[true]) :
    ∃ r,runFrom prime 1 ⟨0,baseHeads,input⟩=some r ∧ r.steps=1 ∧
      r.final.heads=baseHeads ∧ r.final.tapes=Function.update input 724 [false] := by
  have hs:step prime ⟨0,baseHeads,input⟩=
      some (⟨1,baseHeads,Function.update input 724 [false]⟩ : Configuration 3063 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=724
      · subst i;simp [applyAction,hh,ht,writeTapeBit]
      · simp [applyAction,hi]
  obtain ⟨r,run,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,run,rs,by rw [rf],by rw [rf]⟩

theorem load_run (H : ℕ) (bits pre tail : List Bool) (baseHeads : Fin 3061 → ℕ)
    (base : Fin 3061 → List Bool) (hh : baseHeads 2534=0) (hb : base 2534=List.replicate H false)
    (hraw : 2*bits.length+1 ≤ H) :
    ∃ r,runFrom loader (4*bits.length+3)
      ⟨loader.start,heads pre.length baseHeads,data H base (pre++frame bits++tail)⟩=some r ∧
      r.steps=4*bits.length+3 ∧
      r.final.heads=heads (pre.length+2*bits.length+1) baseHeads ∧
      r.final.tapes=data H (Function.update base 2534 (ZeroPadding.pad H (frame bits))) (pre++frame bits++tail) := by
  let source:=pre++frame bits++tail
  obtain ⟨small,hsmall,ss,sh,st⟩:=CloseoutRowsIntegerRound.padded_load_run H bits pre tail hraw
  obtain ⟨r,run,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots (by decide) FrameLoad.machine _
    (heads pre.length baseHeads) (data H base source) _
    (by intro i;fin_cases i
        · rfl
        · exact hh
        · rfl)
    (by intro i;fin_cases i
        · exact (ZeroPadding.pad_zero source).symm
        · simpa only [data,Fin.addCases_left,hb,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
        · rfl)
    small hsmall
  refine ⟨r,run,rs.trans ss,?_,?_⟩
  · funext i
    by_cases hsource:i=3061
    · subst i;exact (rh 0).trans (sh 0)
    by_cases hdst:i=2534
    · subst i;exact ((rh 1).trans (sh 1)).trans hh.symm
    by_cases hlog:i=3062
    · subst i;exact (rh 2).trans (sh 2)
    refine ((keep i (by intro j;fin_cases j <;>
      first | exact Ne.symm hsource | exact Ne.symm hdst | exact Ne.symm hlog)).1).trans ?_
    revert hsource
    refine Fin.addCases (m:=3061) (n:=2) ?_ ?_ i
    · intro j _;simp only [heads,Fin.addCases_left]
    · intro j hj;fin_cases j <;> first | rfl | exact (hj rfl).elim
  · funext i
    by_cases hsource:i=3061
    · subst i;exact (rt 0).trans (st 0)
    by_cases hdst:i=2534
    · subst i;exact (rt 1).trans (st 1)
    by_cases hlog:i=3062
    · subst i;exact (rt 2).trans (st 2)
    refine ((keep i (by intro j;fin_cases j <;>
      first | exact Ne.symm hsource | exact Ne.symm hdst | exact Ne.symm hlog)).2).trans ?_
    revert hdst
    refine Fin.addCases (m:=3061) (n:=2) ?_ ?_ i
    · intro j hj
      have hn:j≠2534:=by intro h;subst j;exact hj rfl
      simp only [data,Fin.addCases_left,Function.update_of_ne hn]
    · intro j _;simp only [data,Fin.addCases_right];rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
