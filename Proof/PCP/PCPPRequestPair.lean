import Proof.PCP.PCPPRequestNaturalSerializer

/-! The existing positive canonical pair machine with its literal zero/zero
branch. The guard reads actual canonical field delimiters. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pair_positive (a b : ℕ) : 0<Nat.pair a b ↔ 0<a ∨ 0<b := by
  constructor
  · intro hp
    by_contra h
    have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb,Nat.pair] at hp
  · intro h
    have hp := Nat.add_le_pair a b
    omega

theorem frame_first (n : ℕ) : readTapeBit (frame n.bits) 0=decide (0<n) := by
  cases hb : n.bits with
  | nil =>
    have h := CanonicalPositiveOutput.nat_bits_value n
    rw [hb] at h
    change 0=n at h
    subst n
    rfl
  | cons b bits =>
    have hn : 0<n := by
      by_contra hz
      have hn0 : n=0 := by omega
      subst n
      simp at hb
    simp [frame,readTapeBit,hn]

def input (a b : ℕ) := PCPPairCanonical.input a.bits b.bits
def test : Machine 38 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val != 0
  rule := fun _ bs => some ⟨if bs 2 || bs 3 then 1 else 2,fun _ => none,fun _ => .stay⟩
def tested (a b : ℕ) : Configuration 38 3 :=
  ⟨if 0<Nat.pair a b then 1 else 2,fun _ => 0,input a b⟩

theorem test_run (a b : ℕ) :
    ∃ r,run test 1 (input a b)=some r ∧ r.final=tested a b ∧ r.steps=1 := by
  have hscan : (initialConfiguration test (input a b)).scanned 2=decide (0<a) ∧
      (initialConfiguration test (input a b)).scanned 3=decide (0<b) :=
    ⟨frame_first a,frame_first b⟩
  have hs : step test (initialConfiguration test (input a b))=some (tested a b) := by
    simp only [step,test,Option.map_some]
    congr 1
    apply configuration_ext
    · change (if (initialConfiguration test (input a b)).scanned 2 ||
          (initialConfiguration test (input a b)).scanned 3 then 1 else 2)=_
      rw [hscan.1,hscan.2]
      simp [tested,pair_positive,Bool.or_eq_true]
    · funext i; rfl
    · funext i; rfl
  exact (Timed.single (by rfl) hs).run (by
    unfold test tested
    split <;> rfl)

def zeroMachine : Machine 38 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun i => if i=26 then some false else none,fun _ => .stay⟩
def zeroOutput (a b : ℕ) := Function.update (input a b) 26 [false]
theorem zero_run (a b : ℕ) :
    ClockJoin.ReadyRun zeroMachine 1 (input a b) (zeroOutput a b) := by
  have hs : step zeroMachine (initialConfiguration zeroMachine (input a b))=
      some (⟨1,fun _ => 0,zeroOutput a b⟩ : Configuration 38 2) := by
    simp only [step,zeroMachine,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i
      by_cases hi : i=26
      · subst i; simp [applyAction,initialConfiguration,zeroOutput,input,PCPPairCanonical.input,writeTapeBit]
      · simp [applyAction,initialConfiguration,zeroOutput,hi]
  obtain ⟨r,hr,rf,rs⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.tapes rf,fun i => congrArg (fun c => c.heads i) rf,by omega⟩

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 3 → ℕ := ![3,stateCount PCPPairCanonical.machine,2]
noncomputable def programs : (j : Fin 3) → Machine 38 (sizes j)
  | ⟨0,_⟩ => test
  | ⟨1,_⟩ => PCPPairCanonical.machine
  | ⟨2,_⟩ => zeroMachine
  | ⟨n+3,h⟩ => False.elim (by omega)
noncomputable def next (j : Fin 3) (q : Fin (sizes j)) (_ : Fin 38 → Bool) : Option (Fin 3) :=
  if j=0 then some (if q.val=1 then 1 else 2) else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (a b : ℕ) := PCPPairCanonical.budget a.bits b.bits+4

theorem pair_run (a b : ℕ) :
    ∃ out,ClockJoin.ReadyRun machine (budget a b) (input a b) out ∧
      (∃ padding,out 26=frame (Nat.pair a b).bits++List.replicate padding false) ∧
      out 36=(Nat.pair a b).bits := by
  obtain ⟨base,hb,bf,bs⟩ := test_run a b
  have core : ∃ k≤budget a b,∃ out,
      Timed machine k (initialConfiguration machine (input a b))
        (RecoveryCalls.stopped sizes (fun _ => 0) out) ∧
      (∃ padding,out 26=frame (Nat.pair a b).bits++List.replicate padding false) ∧
      out 36=(Nat.pair a b).bits := by
    by_cases hp : 0<Nat.pair a b
    · have hn : next 0 base.final.control base.final.scanned=some 1 := by
        rw [bf]
        simp [next,tested,hp]
      obtain ⟨k,hk,hprefix⟩ := call_receipt sizes programs 0 next 0 1 _ _ base hb hn
      obtain ⟨out,⟨last,hl,lt,lh,ls⟩,lf,lraw⟩ := PCPPairCanonical.pair_run a.bits b.bits
        (by simpa only [CanonicalPositiveOutput.nat_bits_value] using hp)
      have hh : last.final.heads=fun _ => 0 := funext lh
      have hentry : RecoveryCalls.restarted (programs 1) base.final.heads base.final.tapes=
          initialConfiguration PCPPairCanonical.machine (input a b) := by
        rw [bf]
        rfl
      rw [hentry] at hprefix
      obtain ⟨m,hm,stop⟩ := stop_receipt sizes programs 0 next 1 _ _ last hl (by simp [next])
      rw [hh,lt] at stop
      refine ⟨k+m,by unfold budget; omega,out,hprefix.trans stop,?_,?_⟩
      · exact ⟨_,by simpa only [CanonicalPositiveOutput.nat_bits_value,ZeroPadding.pad] using lf⟩
      · simpa only [CanonicalPositiveOutput.nat_bits_value] using lraw
    · have he : Nat.pair a b=0 := by omega
      have hn : next 0 base.final.control base.final.scanned=some 2 := by
        rw [bf]
        simp [next,tested,hp]
      obtain ⟨k,hk,hprefix⟩ := call_receipt sizes programs 0 next 0 2 _ _ base hb hn
      obtain ⟨last,hl,lt,lh,ls⟩ := zero_run a b
      have hh : last.final.heads=fun _ => 0 := funext lh
      have hentry : RecoveryCalls.restarted (programs 2) base.final.heads base.final.tapes=
          initialConfiguration zeroMachine (input a b) := by
        rw [bf]
        rfl
      rw [hentry] at hprefix
      obtain ⟨m,hm,stop⟩ := stop_receipt sizes programs 0 next 2 _ _ last hl (by simp [next])
      rw [hh,lt] at stop
      refine ⟨k+m,by unfold budget; omega,zeroOutput a b,hprefix.trans stop,⟨0,?_⟩,?_⟩
      · rw [he]; rfl
      · rw [he]; rfl
  obtain ⟨k,hk,out,path,ht,hraw⟩ := core
  obtain ⟨r,hr,rf,rs⟩ := path.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine k (budget a b-k) _ r hr
  rw [Nat.add_sub_of_le hk] at more
  refine ⟨out,⟨r,more,?_,?_,by omega⟩,ht,hraw⟩
  · rw [rf]; rfl
  · intro i; rw [rf]; rfl

end NearCubicWires.RepairOrdinary.PCPPRequestPair
