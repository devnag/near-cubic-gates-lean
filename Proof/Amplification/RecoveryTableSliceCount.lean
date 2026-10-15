import Proof.Amplification.RecoveryScannerWhole
import Proof.PCP.PCPFieldMoves

/-! Capped table-count parsing on a fresh six-tape slice bank. The following
copy consumes the entire remaining framed suffix, including later fields. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTableSlice
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlots : Fin 3→Fin 6 := ![0,1,2]
theorem countSlots_injective : Function.Injective countSlots := by decide
noncomputable def countProgram := RecoveryFocus.machine countSlots RecoveryCertificateCount.machine
def cfg {s : Nat} (q : Fin s) (word : List Bool) (pos count cap : Nat) : Configuration 6 s :=
  ⟨q,![pos,1,1,0,0,0],![frame word,CompareMachine.word count,CompareMachine.word cap,[],[],[false]]⟩

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem count_layout (q : Fin 5) (word : List Bool) (pos count cap : Nat) :
    RecoveryFocus.config countSlots (cfg q word pos 0 cap).heads (cfg q word pos 0 cap).tapes
      (RecoveryCertificateCount.cfg q (frame word) pos count cap 1)=cfg q word pos count cap := by
  apply focus_configuration countSlots countSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> try rfl
    exact False.elim (hi 1 rfl)

theorem count_output (word : List Bool) (pos count cap : Nat) :
    RecoveryFocus.config countSlots (cfg (0 : Fin 5) word pos 0 cap).heads
      (cfg (0 : Fin 5) word pos 0 cap).tapes
      (RecoveryCertificateCount.cfg 3 (frame word) (pos+2*count+2) count cap 1)=
      cfg 3 word (pos+2*count+2) count cap := by
  apply focus_configuration countSlots countSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i hi; fin_cases i <;> try rfl
    exact False.elim (hi 0 rfl)
  · intro i hi; fin_cases i <;> try rfl
    exact False.elim (hi 1 rfl)

theorem count_run (cap : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom countProgram (3*cap+3) (cfg countProgram.start word (2*k) 0 cap)=some r ∧
      r.steps ≤ 3*cap+3 ∧ (r.final.control=3 ↔ (readCount cap (word.drop k)).isSome=true) ∧
      r.final.heads 5=0 ∧ r.final.tapes 5=[false] ∧
      ∀ n rest,readCount cap (word.drop k)=some (n,rest) →
        n ≤ cap ∧ r.final=cfg 3 word (2*k+2*n+2) n cap := by
  obtain ⟨base,hr,hb,hc,hf⟩ := RecoveryCertificateCount.bounded_at cap word k
  obtain ⟨r,h,hfinal,hsteps⟩ := RecoveryFocus.run_config countSlots countSlots_injective
    RecoveryCertificateCount.machine (cfg (0 : Fin 5) word (2*k) 0 cap).heads
      (cfg (0 : Fin 5) word (2*k) 0 cap).tapes _ _ base hr
  rw [show RecoveryCertificateCount.scan 0 (frame word) (2*k) 0 cap=
    RecoveryCertificateCount.cfg 0 (frame word) (2*k) 0 cap 1 from rfl,count_layout] at h
  have hpick : RecoveryFocus.pick countSlots (5 : Fin 6)=none := by
    have hn : ¬∃ j,countSlots j=(5 : Fin 6) := by decide
    simp only [RecoveryFocus.pick,dif_neg hn]
  refine ⟨r,h,hsteps.le.trans hb,?_,?_,?_,?_⟩
  · simpa only [hfinal,RecoveryFocus.config] using hc
  · rw [hfinal]; simp only [RecoveryFocus.config,hpick]; rfl
  · rw [hfinal]; simp only [RecoveryFocus.config,hpick]; rfl
  · intro n rest hp
    obtain ⟨hn,he⟩ := hf n rest hp
    exact ⟨hn,by rw [hfinal,he]; exact count_output word (2*k) n cap⟩

def before (word : List Bool) (k n : Nat) :=
  Streaming.marks (word.take k)++Streaming.marks (List.replicate n true++[false])

theorem suffix_geometry (cap n k : Nat) (word rest : List Bool)
    (hp : readCount cap (word.drop k)=some (n,rest)) :
    before word k n++frame rest=frame word ∧
      (before word k n).length=2*k+2*n+2 ∧ rest.length ≤ word.length := by
  obtain ⟨_,he⟩ := RecoveryCertificateCount.readCount_some cap n (word.drop k) rest hp
  have hk : k ≤ word.length := by
    by_contra hn
    have hz : word.drop k=[] := List.drop_eq_nil_of_le (by omega)
    rw [hz] at he
    have hlen := congrArg List.length he
    simp only [List.length_nil,List.length_append,List.length_replicate,List.length_cons] at hlen
    omega
  have hframe : before word k n++frame rest=frame word := by
    unfold before
    rw [List.append_assoc,←Streaming.frame_append]
    have hs : (List.replicate n true++[false])++rest=word.drop k := by
      simpa only [List.append_assoc,List.singleton_append] using he.symm
    rw [hs,←Streaming.frame_append,List.take_append_drop]
  refine ⟨hframe,?_,?_⟩
  · simp only [before,List.length_append,Streaming.marks_length,List.length_take,
      Nat.min_eq_left hk,List.length_replicate,List.length_singleton]
    omega
  · have hlen := congrArg List.length he
    simp only [List.length_drop,List.length_append,List.length_replicate,List.length_cons] at hlen
    omega

end NearCubicWires.RepairOrdinary.RecoveryColdTableSlice
