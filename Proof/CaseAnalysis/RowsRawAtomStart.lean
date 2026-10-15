import Proof.CaseAnalysis.RowsRawAtomBatch

/-! The absolute offset and accumulated monomial count start at zero by
three literal instructions. They are not supplied arithmetic metadata. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomStart
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seed : Machine 2 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q _=>if q=0 then some ⟨1,![some false,some false],fun _=>.right⟩
    else if q=1 then some ⟨2,![some true,none],![.right,.stay]⟩
    else if q=2 then some ⟨3,![some false,none],![.left,.stay]⟩ else none
def seedInput : Configuration 2 4:=⟨0,fun _=>0,fun _=>[]⟩
def seedOutput : Configuration 2 4:=
  ⟨3,fun _=>1,![UnaryTemplate.tape 1,RepairSource.VerifierDecoding.CompareMachine.word 0]⟩

theorem seed_run : ∃ r,runFrom seed 3 seedInput=some r ∧ r.final=seedOutput ∧ r.steps=3 := by
  have trace:Timed seed 3 seedInput seedOutput:=by
    apply Timed.step (d:=⟨1,fun _=>1, ![[false],[false]]⟩) (by rfl)
    · change some (applyAction seedInput
        (⟨1,![some false,some false],fun _=>.right⟩ : Action 2 4))=_
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
    · apply Timed.step (d:=⟨2,![2,1],![[false,true],[false]]⟩) (by rfl)
      · change some (applyAction (⟨1,fun _=>1,![[false],[false]]⟩ : Configuration 2 4)
          (⟨2,![some true,none],![.right,.stay]⟩ : Action 2 4))=_
        apply congrArg some
        apply configuration_ext
        · rfl
        · funext i;fin_cases i <;> rfl
        · funext i;fin_cases i <;> rfl
      · apply Timed.single (by rfl)
        change some (applyAction (⟨2,![2,1],![[false,true],[false]]⟩ : Configuration 2 4)
          (⟨3,![some false,none],![.left,.stay]⟩ : Action 2 4))=_
        apply congrArg some
        apply configuration_ext
        · rfl
        · funext i;fin_cases i <;> rfl
        · funext i;fin_cases i <;> rfl
  exact trace.run (by rfl)

def slots : Fin 2→Fin 17:=![11,13]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots seed
def heads (out : List Bool) (i : Fin 17):=if i=12 then out.length else 0
def data (C : ℕ) (source out : List Bool) (i : Fin 17):=
  if i=11 ∨ i=13 then [] else CloseoutRowsRawAtomReuse.data C source 0 0 out i

theorem start_run (C : ℕ) (source out : List Bool) :
    ∃ r,runFrom machine 3 ⟨machine.start,heads out,data C source out⟩=some r ∧
      r.final.heads=CloseoutRowsRawAtomReuse.heads 0 0 out ∧
      r.final.tapes=CloseoutRowsRawAtomReuse.data C source 0 0 out ∧ r.steps=3 := by
  obtain ⟨raw,hr,rf,rs⟩:=seed_run
  obtain ⟨r,rr,_rc,rsteps,rh,rt,keep⟩:=RecoveryFocus.dock slots slots_injective seed _
    (heads out) (data C source out) seedInput (by intro i;fin_cases i <;> rfl)
      (by intro i;fin_cases i <;> rfl) raw hr
  have h11:=rh 0
  have h13:=rh 1
  have t11:=rt 0
  have t13:=rt 1
  rw [rf] at h11 h13 t11 t13
  refine ⟨r,rr,?_,?_,rsteps.trans rs⟩
  · funext i
    by_cases hi11:i=11
    · subst i;exact h11
    by_cases hi13:i=13
    · subst i;exact h13
    have hk:=keep i (by intro j;fin_cases j <;> simpa only [slots] using Ne.symm (by assumption))
    rw [hk.1]
    simp only [heads,CloseoutRowsRawAtomReuse.heads,hi11,hi13,↓reduceIte]
    split_ifs <;> simp_all
  · funext i
    by_cases hi11:i=11
    · subst i;exact t11
    by_cases hi13:i=13
    · subst i;exact t13
    have hk:=keep i (by intro j;fin_cases j <;> simpa only [slots] using Ne.symm (by assumption))
    rw [hk.2]
    simp only [data,hi11,hi13,or_self,↓reduceIte]

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomStart
