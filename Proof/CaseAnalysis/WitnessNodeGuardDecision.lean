import Proof.CaseAnalysis.WitnessNodeGuardRuns

/-! The physical decision consumes only flags from the checked scalar and
tuple calls, and writes one result bit. Its equivalence to the existing
decoder is preserved exactly, including noncanonical rejection. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorRationalProducts RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def naturalFlags (scan : Fin 746 → Bool) (j : Fin 3):=scan (fieldSlots (NodeFields.slots j 175))
def smallFlags (scan : Fin 746 → Bool) (j : Fin 3) (i : Fin 5):=
  scan (scalarSlots j 6) && scan (scalarSlots j (NodeScalar.smallSlots (NodeSmall.tagSlots (i.succ.castAdd 1))))
def boundFlags (scan : Fin 746 → Bool) (j : Fin 3) : Fin 2 → Bool:=
  ![scan (scalarSlots j 17),scan (scalarSlots j 19)]
def selectedKind (j : Fin 5) : Fin 6:=if j.val<3 then 2 else 1
def shapeFlags (scan : Fin 746 → Bool) (j : Fin 5):=scan (kindSlots j (selectedKind j))
def decision (scan : Fin 746 → Bool):=
  NodeDecision.accept (naturalFlags scan) (smallFlags scan) (boundFlags scan) (shapeFlags scan)
def readings (tapes : Fin 746 → List Bool) (i : Fin 746):=readTapeBit (tapes i) 0
def finish : Machine 746 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q.val=1)
  rule:=fun _ scan=>some ⟨1,fun i=>if i=745 then some (decision scan) else none,fun _=>.stay⟩
def finished (tapes : Fin 746 → List Bool):=Function.update tapes 745 [decision (readings tapes)]

theorem finish_run (tapes : Fin 746 → List Bool) (hb : tapes 745=[]) :
    ClockJoin.ReadyRun finish 1 tapes (finished tapes):=by
  let final : Configuration 746 2:=⟨1,fun _=>0,finished tapes⟩
  have h:step finish (initialConfiguration finish tapes)=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=745
      · subst i
        simp [applyAction,initialConfiguration,finish,final,finished,writeTapeBit,hb]
        all_goals rfl
      · simp [applyAction,initialConfiguration,finish,final,finished,hi]
  obtain ⟨r,hr,hf,hs⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],hs.le⟩

noncomputable def beforeDecision (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool):=kindStage (scalarStage (base fields w left right) out 3) bits 5

theorem before_retained (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool) (i : Fin 668)
    (hs : ∀ j z,scalarSlots j z≠fieldSlots i) (hk : ∀ j z,kindSlots j z≠fieldSlots i) :
    beforeDecision fields w left right bits out (fieldSlots i)=fields i:=by
  rw [beforeDecision,kind_stage_other _ _ _ _ hk,scalar_stage_other _ _ _ _ hs,base_field]

theorem before_scalar (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool) (j : Fin 3) (i : Fin 21) (hi : 4 ≤ i.val) :
    beforeDecision fields w left right bits out (scalarSlots j i)=out j i:=by
  rw [beforeDecision,kind_stage_other _ _ _ _ (by
    intro k z;exact Ne.symm (scalar_kind_disjoint j k i z))]
  exact scalar_stage_done _ _ j 3 j.isLt (by rfl) i hi

theorem before_shape (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool) :
    shapeFlags (readings (beforeDecision fields w left right bits out))=NodeDecision.shapes bits:=by
  funext j
  change readTapeBit (kindStage _ bits 5 (kindSlots j (selectedKind j))) 0=_
  rw [kind_stage_done _ _ j 5 j.isLt (by rfl)]
  fin_cases j <;> rfl

theorem before_blank (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool) : beforeDecision fields w left right bits out 745=[]:=by
  rw [beforeDecision,kind_stage_other _ _ _ _ (by decide),scalar_stage_other _ _ _ _ (by decide)]
  exact base_blank _ _ _ _ _ (by decide)

theorem decision_exact (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool)
    (hn : ∀ j,readTapeBit (fields (NodeFields.slots j 175)) 0=true ↔ BitFields.passes (NodeMeaning.codeWord bits j))
    (hf : ∀ j,out j 6=[decide ((BitFields.payload (NodeMeaning.codeWord bits j)).length ≤ 3)])
    (hs : ∀ j t,out j (NodeScalar.smallSlots (NodeSmall.tagSlots (t.succ.castAdd 1)))=
      [NodeTag.flags (ClockNormalize.resize 3 (BitFields.payload (NodeMeaning.codeWord bits j))) t])
    (hl : ∀ j,out j 17=[decide (value left ≤ NodeMeaning.number bits j)])
    (hr : ∀ j,out j 19=[decide (value right ≤ NodeMeaning.number bits j)]) :
    decision (readings (beforeDecision fields w left right bits out))=true ↔
      NodeMeaning.valid (value left) (value right) bits:=by
  unfold decision
  rw [before_shape]
  apply NodeDecision.accept_exact
  · intro j
    change readTapeBit (beforeDecision fields w left right bits out (fieldSlots (NodeFields.slots j 175))) 0=true ↔ _
    rw [before_retained _ _ _ _ _ _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
    exact hn j
  · intro hp
    funext j t
    unfold smallFlags readings
    rw [before_scalar _ _ _ _ _ _ j 6 (by decide),hf,
      before_scalar _ _ _ _ _ _ j _ (by fin_cases t <;> decide),hs]
    change (decide ((BitFields.payload (NodeMeaning.codeWord bits j)).length ≤ 3) &&
      NodeTag.flags (ClockNormalize.resize 3 (BitFields.payload (NodeMeaning.codeWord bits j))) t)=_
    exact NodeSmall.flags_nat _ (hp j) t
  · funext j i
    fin_cases i
    · change readTapeBit (beforeDecision fields w left right bits out (scalarSlots j 17)) 0=_
      rw [before_scalar _ _ _ _ _ _ j 17 (by decide),hl]
      rfl
    · change readTapeBit (beforeDecision fields w left right bits out (scalarSlots j 19)) 0=_
      rw [before_scalar _ _ _ _ _ _ j 19 (by decide),hr]
      rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
