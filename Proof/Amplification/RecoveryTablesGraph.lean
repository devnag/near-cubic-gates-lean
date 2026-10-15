import Proof.Amplification.RecoveryTablesOuter

/-! Whole bounded table-materialization graph: first counted suffix copy,
physical inner-row skip, then second counted suffix copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTables
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev sliceSize := Fintype.card (RecoveryCalls.Control RecoveryColdTableSlice.sizes)
abbrev skipSize := Fintype.card (RepeatMachine.Control 8)
abbrev sizes : Fin 3→Nat := ![sliceSize,skipSize,sliceSize]
noncomputable def programs : (j : Fin 3)→Machine 11 (sizes j)
  | ⟨0,_⟩=>firstProgram
  | ⟨1,_⟩=>skipProgram
  | ⟨2,_⟩=>outerProgram
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 11→Bool) : Option (Fin 3) :=
  if j.val=0 then if bits 5 then some 1 else none else
  if j.val=1 then some 2 else none
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next
def budget (width cap : Nat) (word : List Bool) :=
  2*RecoveryColdTableSlice.budget cap word+RecoveryColdTableSkip.budget width cap+3
def answer (width cap : Nat) (word : List Bool) (k : Nat) :=
  (readCount cap (word.drop k)).any
    (fun pair=>(readCount cap (pair.2.drop (4*width*pair.1))).isSome)

theorem tables_run (width cap : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom machine (budget width cap word) (initial machine.start word k width cap)=some r ∧
      r.steps ≤ budget width cap word ∧ r.final.heads 10=0 ∧
      r.final.tapes 10=[answer width cap word k] ∧
      ∀ n innerBits m outerBits,
        readCount cap (word.drop k)=some (n,innerBits) →
        readCount cap (innerBits.drop (4*width*n))=some (m,outerBits) →
        n ≤ cap ∧ m ≤ cap ∧ r.final=outer r.final.control word innerBits outerBits n m width cap := by
  obtain ⟨first,hfirst,_,hfh,hft,hh,ht,hready⟩ := first_run cap width word k
  have hflag : first.final.scanned 5=(readCount cap (word.drop k)).isSome := by
    change readTapeBit (first.final.tapes 5) (first.final.heads 5)=_
    rw [hfh,hft]
    rfl
  cases hp : readCount cap (word.drop k) with
  | none=>
    obtain ⟨used,hused,h⟩ := stop_receipt sizes programs 0 next 0 _ _ first hfirst
      (by
        change (if first.final.scanned 5 then some (1 : Fin 3) else none)=none
        rw [hflag,hp]
        rfl)
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb : used ≤ budget width cap word := by unfold budget; omega
    have hm := runFrom_moreFuel machine used (budget width cap word-used) _ r hr
    rw [Nat.add_sub_of_le hb] at hm
    refine ⟨r,hm,by omega,?_,?_,?_⟩
    · rw [hf]; exact hh
    · rw [hf]
      simpa only [answer,hp,Option.any_none,RecoveryCalls.stopped] using ht
    · intro n innerBits m outerBits he _; contradiction
  | some pair=>
    rcases pair with ⟨n,innerBits⟩
    obtain ⟨hn,hf⟩ := hready n innerBits hp
    obtain ⟨a,ha,hA⟩ := call_receipt sizes programs 0 next 0 1 _ _ first hfirst
      (by
        change (if first.final.scanned 5 then some (1 : Fin 3) else none)=some 1
        rw [hflag,hp]
        rfl)
    rw [hf] at hA
    obtain ⟨second,hsecond,_,hsf⟩ := skip_run word innerBits n width cap
    obtain ⟨b,hb,hB⟩ := call_receipt sizes programs 0 next 1 2 _ _ second hsecond (by rfl)
    rw [hsf] at hB
    obtain ⟨last,hlast,_,hlh,hlt,hlready⟩ := outer_run word innerBits n width cap
    obtain ⟨c,hc,hC⟩ := stop_receipt sizes programs 0 next 2 _ _ last hlast (by rfl)
    have h := hA.trans (hB.trans hC)
    obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hlen := (RecoveryColdTableSlice.suffix_geometry cap n k word innerBits hp).2.2
    have hcopy : RecoveryColdTableSlice.budget cap innerBits ≤ RecoveryColdTableSlice.budget cap word := by
      unfold RecoveryColdTableSlice.budget
      omega
    have hskip : RecoveryColdTableSkip.budget width n ≤ RecoveryColdTableSkip.budget width cap := by
      unfold RecoveryColdTableSkip.budget
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _
    have hbound : a+(b+c) ≤ budget width cap word := by unfold budget; omega
    have hm := runFrom_moreFuel machine (a+(b+c)) (budget width cap word-(a+(b+c))) _ r hr
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨r,hm,by omega,?_,?_,?_⟩
    · rw [hfinal]; exact hlh
    · rw [hfinal]
      simpa only [answer,hp,Option.any_some,RecoveryCalls.stopped] using hlt
    · intro n' innerBits' m outerBits he hp2
      have heq := Option.some.inj he
      cases heq
      obtain ⟨hm,hout⟩ := hlready m outerBits hp2
      refine ⟨hn,hm,?_⟩
      apply configuration_ext
      · rfl
      · rw [hfinal]
        change last.final.heads=_
        rw [hout]
        rfl
      · rw [hfinal]
        change last.final.tapes=_
        rw [hout]
        rfl

end NearCubicWires.RepairOrdinary.RecoveryColdTables
