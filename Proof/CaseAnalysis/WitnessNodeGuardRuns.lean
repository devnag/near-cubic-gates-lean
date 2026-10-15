import Proof.CaseAnalysis.WitnessNodeGuardLayout

/-! Actual sequential calls on the retained fields. Scalar calls share the
same four driver/bound tapes, and all five structural classifiers consume
their original raw-width tuple words. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorRationalProducts RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def scalarPart (j : Fin 3):=RecoveryFocus.machine (scalarSlots j) NodeScalar.machine
noncomputable def scalarFirst:=Composition.machine (scalarPart 0) (scalarPart 1)
noncomputable def scalarMachine:=Composition.machine scalarFirst (scalarPart 2)

theorem scalar_run (fields : Fin 668 → List Bool) (w : ℕ) (left right : List Bool)
    (payload : Fin 3 → List Bool) (hp : ∀ j,fields (NodeFields.slots j 174)=frame (payload j))
    (hl : left.length=w) (hr : right.length=w) (hb : ∀ j,(payload j).length ≤ w) :
    ∃ out : Fin 3 → Fin 21 → List Bool,
      ClockJoin.ReadyRun scalarMachine (36*w+176) (base fields w left right)
        (scalarStage (base fields w left right) out 3) ∧
      (∀ j i,out j (i.castAdd 17)=shared w left right i) ∧
      (∀ j,out j 4=frame (payload j)) ∧
      (∀ j,out j 6=[decide ((payload j).length ≤ 3)]) ∧
      (∀ j t,out j (NodeScalar.smallSlots (NodeSmall.tagSlots (t.succ.castAdd 1)))=
        [NodeTag.flags (ClockNormalize.resize 3 (payload j)) t]) ∧
      (∀ j,out j 17=[decide (value left ≤ value (payload j))]) ∧
      (∀ j,out j 19=[decide (value right ≤ value (payload j))]):=by
  choose out hout h0 h1 h2 h3 h4 hfit hsmall hleft hright using
    fun j : Fin 3=>NodeScalar.scalar_run w left right (payload j) hl hr (hb j)
  have hshared (j : Fin 3) (i : Fin 4):out j (i.castAdd 17)=shared w left right i:=by
    fin_cases i
    · exact h0 j
    · exact h1 j
    · exact h2 j
    · exact h3 j
  have hinput (j : Fin 3) (i : Fin 21) :
      scalarStage (base fields w left right) out j.val (scalarSlots j i)=
        NodeScalar.input w left right (payload j) i:=by
    by_cases hi:i.val<4
    · have he:scalarSlots j i=common ⟨i.val,hi⟩:=by simp [scalarSlots,hi]
      have hs:=scalar_stage_common (base fields w left right) out (shared w left right)
        (base_common fields w left right) hshared j.val ⟨i.val,hi⟩
      rw [he,hs]
      rw [←base_common fields w left right ⟨i.val,hi⟩,←he]
      exact scalar_base_input fields w left right payload hp j i
    · rw [scalar_stage_later _ _ j j.val (by rfl) i (by omega)]
      exact scalar_base_input fields w left right payload hp j i
  have hpart (j : Fin 3) : ClockJoin.ReadyRun (scalarPart j) (NodeScalar.budget w)
      (scalarStage (base fields w left right) out j.val)
      (scalarStage (base fields w left right) out (j.val+1)):=by
    have h:=bounded_focus (scalarSlots j) (scalar_injective j) _ _ _ (hout j)
      (scalarStage (base fields w left right) out j.val) (hinput j)
    simpa only [scalarStage,dif_pos j.isLt,scalarPart] using h
  have hfirst:=ClockJoin.join (scalarPart 0) (scalarPart 1) _ _ _ _ _ (hpart 0) (hpart 1)
  have h:=ClockJoin.join scalarFirst (scalarPart 2) _ _ _ _ _ hfirst (hpart 2)
  have ht:(NodeScalar.budget w+1+NodeScalar.budget w)+1+NodeScalar.budget w=36*w+176:=by
    unfold NodeScalar.budget;omega
  rw [ht] at h
  exact ⟨out,h,hshared,h4,hfit,hsmall,hleft,hright⟩

abbrev kindStates:=Fintype.card (RecoveryCalls.Control CompetitorWitnessKind.sizes)
def kindSizes (_ : Fin 5):=kindStates
noncomputable def kindPart (j : Fin 5):=RecoveryFocus.machine (kindSlots j) CompetitorWitnessKind.machine
noncomputable def kindPrograms (j : Fin 5) : Machine 746 (kindSizes j):=kindPart j
def kindNext (j : Fin 5) (_ : Fin (kindSizes j)) (_ : Fin 746 → Bool) : Option (Fin 5):=
  if h:j.val+1<5 then some ⟨j.val+1,h⟩ else none
noncomputable def kindMachine:=RecoveryCalls.machine kindSizes kindPrograms 0 kindNext

theorem kind_step (start : Fin 746 → List Bool) (bits : List Bool)
    (hi : ∀ j i,start (kindSlots j i)=CompetitorWitnessKind.input (kindValues bits j) i) (j : Fin 5) :
    ReadyRun (kindPart j) (16*bits.length+27) (kindStage start bits j.val)
      (kindStage start bits (j.val+1)):=by
  have h:=(CompetitorWitnessKind.kind_ready (kindValues bits j)).focus (kindSlots j) (kind_injective j)
    (kindStage start bits j.val) (by intro i;rw [kind_stage_later _ _ j j.val (by rfl),hi])
  simpa only [kindStage,dif_pos j.isLt,kindPart,kindResult,kind_lengths] using h

theorem kind_run (start : Fin 746 → List Bool) (bits : List Bool)
    (hi : ∀ j i,start (kindSlots j i)=CompetitorWitnessKind.input (kindValues bits j) i) :
    ReadyRun kindMachine (80*bits.length+140) start (kindStage start bits 5):=by
  have h0:=(kind_step start bits hi 0).call kindSizes kindPrograms 0 kindNext 0 1 (by intro q;rfl)
  have h1:=(kind_step start bits hi 1).call kindSizes kindPrograms 0 kindNext 1 2 (by intro q;rfl)
  have h2:=(kind_step start bits hi 2).call kindSizes kindPrograms 0 kindNext 2 3 (by intro q;rfl)
  have h3:=(kind_step start bits hi 3).call kindSizes kindPrograms 0 kindNext 3 4 (by intro q;rfl)
  have h4:=(kind_step start bits hi 4).stop kindSizes kindPrograms 0 kindNext 4 (by intro q;rfl)
  have h:=(((h0.trans h1).trans h2).trans h3).trans h4
  have ht:(((16*bits.length+27+1+(16*bits.length+27+1))+(16*bits.length+27+1))+
    (16*bits.length+27+1))+(16*bits.length+27+1)=80*bits.length+140:=by omega
  rw [ht] at h
  obtain ⟨r,hr,hf,hs⟩:=h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i;simp [hf,RecoveryCalls.stopped],hs⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
