import Proof.Amplification.RecoveryTableSliceCopy

/-! A finite count/copy/true-return controller. A malformed count stops
with its retained false cell; only a completed physical copy writes true. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTableSlice
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def writeProgram : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=5 then some true else none,fun _=>.stay⟩ else none

theorem write_run {s : Nat} (c : Configuration 6 s)
    (hh : c.heads 5=0) (ht : c.tapes 5=[false]) :
    ∃ r,runFrom writeProgram 1 (RecoveryCalls.restarted writeProgram c.heads c.tapes)=some r ∧
      r.final=(⟨1,c.heads,Function.update c.tapes 5 [true]⟩ : Configuration 6 2) ∧ r.steps=1 := by
  have hs : step writeProgram (RecoveryCalls.restarted writeProgram c.heads c.tapes)=
      some (⟨1,c.heads,Function.update c.tapes 5 [true]⟩ : Configuration 6 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=5
      · subst i
        simp [applyAction,writeProgram,RecoveryCalls.restarted,hh,ht,writeTapeBit]
      · simp [applyAction,writeProgram,RecoveryCalls.restarted,hi]
  exact (Timed.single (by rfl) hs).run (by rfl)

abbrev sizes : Fin 3→Nat := ![5,5,2]
noncomputable def programs : (j : Fin 3)→Machine 6 (sizes j)
  | ⟨0,_⟩=>countProgram
  | ⟨1,_⟩=>copyProgram
  | ⟨2,_⟩=>writeProgram
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (q : Fin (sizes j)) (_ : Fin 6→Bool) : Option (Fin 3) :=
  if j.val=0 then if q.val=3 then some 1 else none else
  if j.val=1 then some 2 else none
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next
def budget (cap : Nat) (word : List Bool) := 3*cap+4*word.length+12
noncomputable def finished {s : Nat} (c : Configuration 6 s) :=
  RecoveryCalls.stopped sizes c.heads (Function.update c.tapes 5 [true])

theorem write_tail {s : Nat} (c : Configuration 6 s)
    (hh : c.heads 5=0) (ht : c.tapes 5=[false]) :
    ∃ used,used ≤ 2 ∧ Timed machine used
      (controlConfig (RecoveryCalls.code sizes 2) (RecoveryCalls.restarted writeProgram c.heads c.tapes))
      (finished c) := by
  obtain ⟨r,hr,hf,_⟩ := write_run c hh ht
  obtain ⟨used,hused,h⟩ := stop_receipt sizes programs 0 next 2 _ _ r hr (by rfl)
  rw [hf] at h
  exact ⟨used,hused,h⟩

theorem slice_run (cap : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom machine (budget cap word) (cfg machine.start word (2*k) 0 cap)=some r ∧
      r.steps ≤ budget cap word ∧ r.final.heads 5=0 ∧
      r.final.tapes 5=[(readCount cap (word.drop k)).isSome] ∧
      ∀ n rest,readCount cap (word.drop k)=some (n,rest) → n ≤ cap ∧
        r.final.heads=(copied (0 : Fin 1) word rest n cap).heads ∧
        r.final.tapes=Function.update (copied (0 : Fin 1) word rest n cap).tapes 5 [true] := by
  obtain ⟨first,hfirst,_,hc,hh,ht,hready⟩ := count_run cap word k
  cases hp : readCount cap (word.drop k) with
  | none=>
    have hn : first.final.control.val≠3 := by
      intro he
      have heq : first.final.control=3 := Fin.ext he
      have hb := hc.mp heq
      simp [hp] at hb
    obtain ⟨used,hused,h⟩ := stop_receipt sizes programs 0 next 0 _ _ first hfirst
      (by simp [next,hn])
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb : used ≤ budget cap word := by unfold budget; omega
    have hm := runFrom_moreFuel machine used (budget cap word-used) _ r hr
    rw [Nat.add_sub_of_le hb] at hm
    refine ⟨r,hm,by omega,?_,?_,?_⟩
    · rw [hf]; exact hh
    · rw [hf]; exact ht
    · intro n rest he; contradiction
  | some pair=>
    rcases pair with ⟨n,rest⟩
    obtain ⟨hn,hf⟩ := hready n rest hp
    obtain ⟨a,ha,hA⟩ := call_receipt sizes programs 0 next 0 1 _ _ first hfirst
      (by rw [hf]; rfl)
    rw [hf] at hA
    obtain ⟨second,hsecond,hsf,_⟩ := copy_run word rest k n cap hp
    obtain ⟨b,hb,hB⟩ := call_receipt sizes programs 0 next 1 2 _ _ second hsecond (by rfl)
    rw [hsf] at hB
    obtain ⟨c,hc,hC⟩ := write_tail (copied (0 : Fin 1) word rest n cap) rfl rfl
    have h := hA.trans (hB.trans hC)
    obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [finished,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hrest := (suffix_geometry cap n k word rest hp).2.2
    have hbound : a+(b+c) ≤ budget cap word := by unfold budget; omega
    have hm := runFrom_moreFuel machine (a+(b+c)) (budget cap word-(a+(b+c))) _ r hr
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨r,hm,by omega,?_,?_,?_⟩
    · rw [hfinal]; rfl
    · rw [hfinal]
      simp only [finished,RecoveryCalls.stopped,Function.update_self,Option.isSome_some]
    · intro n' rest' he
      have heq := Option.some.inj he
      cases heq
      exact ⟨hn,by rw [hfinal]; rfl,by rw [hfinal]; rfl⟩

end NearCubicWires.RepairOrdinary.RecoveryColdTableSlice
