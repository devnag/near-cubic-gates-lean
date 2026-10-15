import Proof.Amplification.RecoveryCertificateCount

/-! All-input correctness of the same capped physical count parser. Both
missing and oversized counts reject within a budget fixed by the query cap,
even when the arbitrary witness has an enormous unread suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateCount
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readCount_eq (cap : Nat) (word : List Bool) :
    readCount cap word=(unary word).bind (fun pair => if pair.1≤cap then some pair else none) := by
  induction word generalizing cap with
  | nil => simp [readCount,unary]
  | cons bit word ih =>
    cases bit with
    | false => simp [readCount,unary]
    | true =>
      cases cap with
      | zero => cases hu : unary word <;> simp [readCount,unary,hu]
      | succ cap =>
        cases hu : unary word with
        | none => simp [readCount,unary,ih,hu]
        | some pair =>
          rcases pair with ⟨n,rest⟩
          by_cases hn : n≤cap <;> simp [readCount,unary,ih,hu,hn]

theorem missing_run (n cap : Nat) (pre : List Bool) (hn : n≤cap) :
    let source := pre++frame (List.replicate n true)
    ∃ receipt : ExecutionReceipt 3 5,
      runFrom machine (2*n+1) (scan 0 source pre.length 0 cap)=some receipt ∧
      receipt.final=scan 4 source (pre.length+2*n+1) n cap ∧ receipt.steps=2*n+1 := by
  let source := pre++frame (List.replicate n true)
  let before := pre++Streaming.marks (List.replicate n true)
  have hs : before++[false]=source := by
    have h := Streaming.frame_append (List.replicate n true) []
    simp only [List.append_nil,RepairOrdinary.frame] at h
    change (pre++Streaming.marks (List.replicate n true))++[false]=
      pre++RepairOrdinary.frame (List.replicate n true)
    rw [List.append_assoc]
    exact congrArg (fun bits : List Bool => pre++bits) h.symm
  have hb : before.length=pre.length+2*n := by simp [before,Streaming.marks_length]
  have ht := Timed.single (by rfl : machine.halted (0 : Fin 5)=false)
    (by simpa [hs] using marker_step before [] n cap false)
  rw [hb] at ht
  have hp := true_prefix n pre [false] 0 cap (by omega)
  dsimp only at hp
  rw [hs] at hp
  simp only [Nat.zero_add] at hp
  exact (hp.trans ht).run (by rfl)

theorem oversized_run (cap : Nat) (pre fields : List Bool) :
    let source := pre++frame (List.replicate (cap+1) true++fields)
    ∃ receipt : ExecutionReceipt 3 5,
      runFrom machine (2*cap+2) (scan 0 source pre.length 0 cap)=some receipt ∧
      receipt.final=scan 4 source (pre.length+2*cap+2) cap cap ∧ receipt.steps=2*cap+2 := by
  let source := pre++frame (List.replicate (cap+1) true++fields)
  let before := pre++Streaming.marks (List.replicate cap true)
  have hs : before++true::true::frame fields=source := by
    simp [before,source,List.replicate_add,Streaming.frame_append,
      RepairOrdinary.frame,Streaming.marks,List.append_assoc]
  have hb : before.length=pre.length+2*cap := by simp [before,Streaming.marks_length]
  have h1 := Timed.single (by rfl : machine.halted (1 : Fin 5)=false)
    (by simpa [hs,List.append_assoc] using full_step (before++[true]) (frame fields) cap)
  have h0 := Timed.step (by rfl : machine.halted (0 : Fin 5)=false)
    (by simpa [hs] using marker_step before (true::frame fields) cap cap true) h1
  rw [hb] at h0
  have hp := true_prefix cap pre (true::true::frame fields) 0 cap (by omega)
  dsimp only at hp
  rw [hs] at hp
  simp only [Nat.zero_add] at hp
  exact (hp.trans h0).run (by rfl)

theorem bounded_parse (cap : Nat) (pre word : List Bool) :
    ∃ receipt : ExecutionReceipt 3 5,
      runFrom machine (3*cap+3) (scan 0 (pre++frame word) pre.length 0 cap)=some receipt ∧
      (receipt.final.control=3 ↔ (readCount cap word).isSome=true) := by
  have widen : ∀ (cost : Nat) (r : ExecutionReceipt 3 5),cost≤3*cap+3 →
      runFrom machine cost (scan 0 (pre++frame word) pre.length 0 cap)=some r →
      runFrom machine (3*cap+3) (scan 0 (pre++frame word) pre.length 0 cap)=some r := by
    intro cost r hc hr
    have hm := runFrom_moreFuel machine cost (3*cap+3-cost) _ r hr
    rwa [Nat.add_sub_of_le hc] at hm
  cases hu : unary word with
  | none =>
    have hw := UnaryMachine.unary_none hu
    by_cases hn : word.length≤cap
    · obtain ⟨r,hr,hf,_⟩ := missing_run word.length cap pre hn
      rw [← hw] at hr
      refine ⟨r,widen _ r (by omega) hr,?_⟩
      rw [hf,readCount_eq,hu]
      simp [scan,cfg]
    · have hlen : cap+1≤word.length := by omega
      have hsplit : word=List.replicate (cap+1) true++List.replicate (word.length-(cap+1)) true := by
        rw [← List.replicate_add,Nat.add_sub_of_le hlen]
        exact hw
      obtain ⟨r,hr,hf,_⟩ := oversized_run cap pre (List.replicate (word.length-(cap+1)) true)
      rw [← hsplit] at hr
      refine ⟨r,widen _ r (by omega) hr,?_⟩
      rw [hf,readCount_eq,hu]
      simp [scan,cfg]
  | some pair =>
    rcases pair with ⟨n,fields⟩
    have hw := UnaryMachine.unary_decomposition hu
    by_cases hn : n≤cap
    · obtain ⟨r,hr,hf,_⟩ := parse_run n cap pre fields hn
      rw [← hw] at hr
      refine ⟨r,widen _ r (by omega) hr,?_⟩
      rw [hf,readCount_eq,hu]
      simp [cfg,hn]
    · have hlen : cap+1≤n := by omega
      have hsplit : word=List.replicate (cap+1) true++(List.replicate (n-(cap+1)) true++false::fields) := by
        rw [← List.append_assoc,← List.replicate_add,Nat.add_sub_of_le hlen]
        exact hw
      obtain ⟨r,hr,hf,_⟩ := oversized_run cap pre (List.replicate (n-(cap+1)) true++false::fields)
      rw [← hsplit] at hr
      refine ⟨r,widen _ r (by omega) hr,?_⟩
      rw [hf,readCount_eq,hu]
      simp [scan,cfg,hn]

end NearCubicWires.RepairOrdinary.RecoveryCertificateCount
