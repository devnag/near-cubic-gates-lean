import Proof.Amplification.RecoveryTseitinNativeCarrier

/-! Advance the physically produced sentinel by one ordinary transition,
then expose the exact initial view required by the original formula machine. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enterMachine : Machine 1370 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun _ _=>some ⟨1,fun _=>none,fun i=>if i=1338 then .right else .stay⟩
def enterHeads (heads : Fin 1370→Nat) (i : Fin 1370) := if i=1338 then heads i+1 else heads i
theorem enter_run (heads : Fin 1370→Nat) (data : Fin 1370→List Bool) : ∃ r,
    runFrom enterMachine 1 ⟨enterMachine.start,heads,data⟩=some r ∧
      r.final.heads=enterHeads heads ∧ r.final.tapes=data ∧ r.steps=1 := by
  have hs : step enterMachine ⟨enterMachine.start,heads,data⟩=
      some (⟨1,enterHeads heads,data⟩ : Configuration 1370 2) := by
    simp only [step,enterMachine,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=1338 <;> simp [applyAction,enterHeads,hi,HeadMove.apply]
    · funext i
      simp only [applyAction]
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads rf,congrArg Configuration.tapes rf,rs⟩

theorem entry_heads (cap n count output : Nat) (word out : List Bool)
    (heads : Fin 1370→Nat) (ho : heads 1333=out.length) (hz : ∀ i,i≠1333 → heads i=0)
    (i : Fin 1342) : enterHeads heads (i.castAdd 28)=
      (Formula.state 0 n 0 0 word out cap count output).heads i := by
  refine Fin.addCases (m:=1338) (n:=4) (fun j=>?_) (fun j=>?_) i
  · rw [Formula.old_heads]
    have hj:=j.isLt
    have hdriver : (j.castAdd 4).castAdd 28≠(1338 : Fin 1370) := by
      intro he; have hv:=congrArg Fin.val he; change j.val=1338 at hv; omega
    rw [enterHeads,if_neg hdriver]
    by_cases h33 : j=1333
    · subst j; exact ho
    · have hg : (j.castAdd 4).castAdd 28≠(1333 : Fin 1370) := by
        intro he; have hv:=congrArg Fin.val he; exact h33 (Fin.ext hv)
      rw [hz _ hg]
      simp only [Reuse.heads,if_neg h33]
      split_ifs <;> rfl
  · fin_cases j
    · have hd : heads 1338=0 := hz 1338 (by decide)
      change enterHeads heads 1338=1
      simp [enterHeads,hd]
    · exact hz 1339 (by decide)
    · exact hz 1340 (by decide)
    · exact hz 1341 (by decide)

theorem entry_tapes (cap n count output : Nat) (word out : List Bool)
    (data : Fin 1370→List Bool)
    (ho : ∀ i : Fin 1338,data (i.castAdd 32)=Reuse.data n 0 word out cap i)
    (he : ∀ i : Fin 4,data ((i.natAdd 1338).castAdd 28)=
      (![CompareMachine.word count,List.replicate output true,[],[]] : Fin 4→List Bool) i)
    (i : Fin 1342) : data (i.castAdd 28)=(Formula.state 0 n 0 0 word out cap count output).tapes i := by
  refine Fin.addCases (m:=1338) (n:=4) (fun j=>?_) (fun j=>?_) i
  · rw [Formula.old_tapes]
    exact ho j
  · fin_cases j
    · exact he 0
    · exact he 1
    · exact he 2
    · exact he 3

theorem enter_forward : CursorRestore.NoLeft enterMachine (1333 : Fin 1370) := by
  intro q bits a ha
  simp only [enterMachine,Option.some.injEq] at ha
  subst a
  decide

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
