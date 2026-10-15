import Proof.CaseAnalysis.RecoverySelectorSeed

/-! The existing reverse OR fold runs in the actual retained selector bank.
The shared field index remains on its own tape while the fold uses cleared
reference scratch and the already retained outer count sentinel. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open RecoveryBoundedSelectorLoop RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def foldSlots : Fin 35→Fin 43 :=
  Fin.addCases (m:=29) (n:=6) (motive:=fun _=>Fin 43)
    (fun j=>if j=1 then 36 else j.castAdd 14) ![29,30,40,32,33,42]
def foldCaps (C : ℕ) (i : Fin 35) := if i=29 then C else 0
theorem fold_injective : Function.Injective foldSlots := by decide
noncomputable def reverseMachine:=RecoveryFocus.machine foldSlots (RecoveryBoundedNativeFoldLoop.machine false)
noncomputable def foldInput (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :=
  ZeroPadding.config (foldCaps C)
    (RecoveryBoundedNativeFoldLoop.configuration 0 false C false pre refs.reverse ⟨base,0,0,out⟩ total 1)
noncomputable def foldOutput (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :=
  ZeroPadding.config (foldCaps C)
    (RecoveryBoundedNativeFoldLoop.configuration 3 false C false pre []
      (RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩) total 1)

theorem fold_input_data (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (foldInput base C total out pre refs).tapes=
      fun j=>ZeroPadding.pad (foldCaps C j)
        (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
          (RecoveryBoundedNativeFold.data 0 base C false out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) [])
          (fun _=>CompareMachine.word total) j) := by
  change (fun j=>ZeroPadding.pad (foldCaps C j)
    (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
      (RecoveryBoundedNativeFold.data 0 base C false out
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs.reverse.reverse++List.replicate 0 false) [])
      (fun _=>CompareMachine.word total) j))=_
  simp only [List.reverse_reverse,List.replicate_zero,List.append_nil]

theorem fold_input_heads (base C total pos : ℕ) (out pre : List Bool) (refs : List ℕ) (j : Fin 35) :
    heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos (foldSlots j)=
      (foldInput base C total out pre refs).heads j := by
  fin_cases j
  all_goals simp only [foldInput,ZeroPadding.config,RecoveryBoundedNativeFoldLoop.configuration,
    RepeatMachine.cfg,controlConfig,TapeEmbedding.config,RecoveryBoundedNativeFoldLoop.State.entry,
    RecoveryBoundedNativeFold.entry,RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse]
  all_goals rfl

theorem fold_input_tapes (index base C D value limit total : ℕ) (out source pre : List Bool)
    (refs : List ℕ) (hC : 1 ≤ C) (j : Fin 35) :
    data index base C D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) (foldSlots j)=
      (foldInput base C total out pre refs).tapes j := by
  rw [fold_input_data]
  fin_cases j
  all_goals first | rfl | exact (pad_false C hC).symm |
    (change List.replicate C false=ZeroPadding.pad 0 (List.replicate C false); exact (ZeroPadding.pad_zero _).symm) |
    (change out=ZeroPadding.pad 0 out; exact (ZeroPadding.pad_zero _).symm) |
    (change List.replicate C true=ZeroPadding.pad 0 (List.replicate C true); exact (ZeroPadding.pad_zero _).symm) |
    (change List.replicate (C+1) false=ZeroPadding.pad 0 (List.replicate (C+1) false); exact (ZeroPadding.pad_zero _).symm) |
    (change List.replicate base true=ZeroPadding.pad 0 (List.replicate base true); exact (ZeroPadding.pad_zero _).symm) |
    (change (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)=ZeroPadding.pad 0 (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs);
      exact (ZeroPadding.pad_zero _).symm) |
    (change CompareMachine.word total=ZeroPadding.pad 0 (CompareMachine.word total); exact (ZeroPadding.pad_zero _).symm)

theorem padded_reverse_run (base W total : ℕ) (out pre : List Bool) (refs : List ℕ)
    (htotal : refs.length=total) (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W) :
    ∃ p,runFrom (RecoveryBoundedNativeFoldLoop.machine false)
      (refs.length*(24*capacity W+66)+total+3) (foldInput base (capacity W) total out pre refs)=some p ∧
      p.final=foldOutput base (capacity W) total out pre refs ∧
      p.steps ≤ refs.length*(24*capacity W+66)+total+3 := by
  obtain ⟨a,haRun,af,as⟩:=RecoveryBoundedNativeFoldLoop.loop_run false W (capacity W) total false pre refs.reverse
    ⟨base,0,0,out⟩ (by simpa only [List.length_reverse,Nat.zero_add] using htotal)
    (by intro ref hr; exact href ref (List.mem_reverse.mp hr))
    (by simpa only [List.length_reverse] using ha) (by rfl)
  rw [List.length_reverse] at haRun as
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config (RecoveryBoundedNativeFoldLoop.machine false) (foldCaps (capacity W))
    _ _ a haRun
  refine ⟨p,hp,?_,ps.le.trans as⟩
  rw [pf,af]
  rfl

theorem reverse_run (index base W D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ)
    (htotal : refs.length=total) (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W) :
    ∃ r,runFrom reverseMachine (refs.length*(24*capacity W+66)+total+3)
      ⟨reverseMachine.start,heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos,
        data index base (capacity W) D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩=some r ∧
      r.steps ≤ refs.length*(24*capacity W+66)+total+3 ∧
      (∀ j,r.final.heads (foldSlots j)=(foldOutput base (capacity W) total out pre refs).heads j) ∧
      (∀ j,r.final.tapes (foldSlots j)=(foldOutput base (capacity W) total out pre refs).tapes j) ∧
      (∀ i,(∀ j,foldSlots j≠i) →
        r.final.heads i=heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos i ∧
        r.final.tapes i=data index base (capacity W) D value limit total out source
          (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) i) := by
  have hc : 1 ≤ capacity W := by
    unfold capacity
    have h : 0 < (W+1)^2 := by positivity
    omega
  obtain ⟨p,hp,pf,ps⟩:=padded_reverse_run base W total out pre refs htotal href ha
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock foldSlots fold_injective (RecoveryBoundedNativeFoldLoop.machine false) _
    (heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos)
    (data index base (capacity W) D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs))
    (foldInput base (capacity W) total out pre refs)
    (fold_input_heads base (capacity W) total pos out pre refs)
    (fold_input_tapes index base (capacity W) D value limit total out source pre refs hc) p hp
  refine ⟨r,hr,rs.le.trans ps,?_,?_,rkeep⟩
  · intro j
    rw [rh j,pf]
  · intro j
    rw [rt j,pf]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
