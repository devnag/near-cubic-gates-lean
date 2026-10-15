import Proof.CaseAnalysis.RecoveryAddressMeaning

/-! The existing reverse OR fold consumes the address children's actual
saved references in their original postorder. All41 bank fields are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open RecoveryBoundedAddress RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out stack : List Bool) (pos : ℕ) : Fin 41→ℕ:=
  Fin.addCases (m:=40) (n:=1) (motive:=fun _=>ℕ) (RecoveryBoundedAddress.heads out stack pos) (fun _=>1)
def data (index base C D value limit total : ℕ) (out source stack : List Bool) : Fin 41→List Bool:=
  Fin.addCases (m:=40) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedAddress.data index base C D value limit false out source stack index) (fun _=>CompareMachine.word total)
noncomputable def seed:=TapeEmbedding.machine 1 RecoveryBoundedAddress.seed
def foldSlots : Fin 35→Fin 41:=
  Fin.addCases (m:=29) (n:=6) (motive:=fun _=>Fin 41)
    (fun j=>if j=1 then 31 else j.castAdd 12) ![29,30,38,32,33,40]
theorem fold_injective : Function.Injective foldSlots := by decide
noncomputable def reverseMachine:=RecoveryFocus.machine foldSlots (RecoveryBoundedNativeFoldLoop.machine false)

theorem seed_run (index base C D value limit total pos : ℕ) (out source stack : List Bool) :
    ∃ r,runFrom seed RecoveryBoundedSelectorFinish.falseBits.length
      ⟨seed.start,heads out stack pos,data index base C D value limit total out source stack⟩=some r ∧
      r.steps=RecoveryBoundedSelectorFinish.falseBits.length ∧
      r.final.heads=heads (out++RecoveryBoundedSelectorFinish.falseBits) stack pos ∧
      r.final.tapes=data index base C D value limit total (out++RecoveryBoundedSelectorFinish.falseBits) source stack := by
  obtain ⟨p,hp,ps,ph,pt⟩:=RecoveryBoundedAddress.seed_run index base C D value limit pos index out source stack
  let eh : Fin 1→ℕ:=fun _=>1
  let et : Fin 1→List Bool:=fun _=>CompareMachine.word total
  let r:=TapeEmbedding.receipt eh et p
  have hr:=TapeEmbedding.run_embed RecoveryBoundedAddress.seed eh et _ _ p hp
  refine ⟨r,hr,ps,?_,?_⟩
  · change Fin.addCases (m:=40) (n:=1) (motive:=fun _=>ℕ) p.final.heads eh=_
    rw [ph]
    rfl
  · change Fin.addCases (m:=40) (n:=1) (motive:=fun _=>List Bool) p.final.tapes et=_
    rw [pt]
    rfl

theorem fold_input_heads (base C total pos : ℕ) (out pre : List Bool) (refs : List ℕ) (j : Fin 35) :
    heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos (foldSlots j)=
      (RecoveryBoundedSelectorFinish.foldInput base C total out pre refs).heads j := by
  fin_cases j
  all_goals simp only [RecoveryBoundedSelectorFinish.foldInput,ZeroPadding.config,
    RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse]
  all_goals rfl

theorem fold_input_tapes (index base C D value limit total : ℕ) (out source pre : List Bool)
    (refs : List ℕ) (j : Fin 35) :
    data index base C D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) (foldSlots j)=
      (RecoveryBoundedSelectorFinish.foldInput base C total out pre refs).tapes j := by
  rw [RecoveryBoundedSelectorFinish.fold_input_data]
  fin_cases j
  all_goals first | rfl |
    (change List.replicate C false=ZeroPadding.pad 0 (List.replicate C false);exact (ZeroPadding.pad_zero _).symm) |
    (change out=ZeroPadding.pad 0 out;exact (ZeroPadding.pad_zero _).symm) |
    (change List.replicate C true=ZeroPadding.pad 0 (List.replicate C true);exact (ZeroPadding.pad_zero _).symm) |
    (change List.replicate (C+1) false=ZeroPadding.pad 0 (List.replicate (C+1) false);exact (ZeroPadding.pad_zero _).symm) |
    (change List.replicate base true=ZeroPadding.pad 0 (List.replicate base true);exact (ZeroPadding.pad_zero _).symm) |
    (change (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)=ZeroPadding.pad 0 (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs);
      exact (ZeroPadding.pad_zero _).symm) |
    (change CompareMachine.word total=ZeroPadding.pad 0 (CompareMachine.word total);exact (ZeroPadding.pad_zero _).symm)

noncomputable def reverseOutput (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ):=
  RecoveryFocus.config foldSlots (heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos)
    (data index base C D value limit total out source (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs))
    (RecoveryBoundedSelectorFinish.foldOutput base C total out pre refs)

theorem reverse_run (index base W D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ)
    (htotal : refs.length=total) (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W) :
    ∃ r,runFrom reverseMachine (refs.length*(24*RecoveryBoundedSelectorLoop.capacity W+66)+total+3)
      ⟨reverseMachine.start,heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos,
        data index base (RecoveryBoundedSelectorLoop.capacity W) D value limit total out source
          (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩=some r ∧
      r.steps ≤ refs.length*(24*RecoveryBoundedSelectorLoop.capacity W+66)+total+3 ∧
      r.final=reverseOutput index base (RecoveryBoundedSelectorLoop.capacity W) D value limit total pos out source pre refs := by
  obtain ⟨p,hp,pf,ps⟩:=RecoveryBoundedSelectorFinish.padded_reverse_run base W total out pre refs htotal href ha
  let hh:=heads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) pos
  let tt:=data index base (RecoveryBoundedSelectorLoop.capacity W) D value limit total out source
    (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)
  obtain ⟨r,hr,rf,rs⟩:=RecoveryFocus.run_config foldSlots fold_injective (RecoveryBoundedNativeFoldLoop.machine false)
    hh tt _ _ p hp
  have he : RecoveryFocus.config foldSlots hh tt
      (RecoveryBoundedSelectorFinish.foldInput base (RecoveryBoundedSelectorLoop.capacity W) total out pre refs)=
      (⟨reverseMachine.start,hh,tt⟩ : Configuration 41 _) := by
    exact WilliamsSourceCrop.focus_same foldSlots (⟨reverseMachine.start,hh,tt⟩ : Configuration 41 _)
      (RecoveryBoundedSelectorFinish.foldInput base (RecoveryBoundedSelectorLoop.capacity W) total out pre refs)
      (fold_input_heads base (RecoveryBoundedSelectorLoop.capacity W) total pos out pre refs)
      (fold_input_tapes index base (RecoveryBoundedSelectorLoop.capacity W) D value limit total out source pre refs)
  rw [he] at hr
  refine ⟨r,hr,rs.le.trans ps,?_⟩
  rw [rf,pf]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
