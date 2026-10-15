import Proof.PCP.VerifierDecodingHeaderRejection

/-! Total bounded header execution, including both missing unary terminators.
This consumer exposes the real successful fields or the physical reject state. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parts (bits : List Bool) : Option (ℕ × ℕ × List Bool) :=
  (unary bits).bind fun first => (unary first.2).map fun second => (first.1,second.1,second.2)

def Result (bits : List Bool) (final : Configuration 3 8) : Prop :=
  match parts bits with
  | none => final.control=7
  | some (t,s,fields) => final=finished t s fields

theorem parts_word (t s : ℕ) (fields : List Bool) : parts (word t s fields)=some (t,s,fields) := by
  simp [parts,word,unary_encoded]

theorem total_run (bits : List Bool) :
    ∃ r, run machine (2*bits.length+5) ![frame bits,[],[]]=some r ∧
      r.steps≤2*bits.length+5 ∧ Result bits r.final := by
  cases hfirst : unary bits with
  | none =>
    have hb := UnaryMachine.unary_none hfirst
    obtain ⟨r,hr,hf,hs⟩ := missing_first bits.length
    rw [←hb] at hr
    have hm := runFrom_moreFuel machine (2*bits.length+3) 2 _ r hr
    have he : (2*bits.length+3)+2=2*bits.length+5 := by omega
    rw [he] at hm
    exact ⟨r,hm,by omega,by simp [Result,parts,hfirst,hf]⟩
  | some first =>
    rcases first with ⟨t,tail⟩
    have hlength := unary_bounded hfirst
    cases hsecond : unary tail with
    | none =>
      have hb : bits=missingWord t tail.length := by
        rw [UnaryMachine.unary_decomposition hfirst,UnaryMachine.unary_none hsecond]
        simp [missingWord]
      obtain ⟨r,hr,hf,hs⟩ := missing_second t tail.length
      rw [←hb] at hr
      have htime : 2*t+2*tail.length+4≤2*bits.length+5 := by omega
      have hm := runFrom_moreFuel machine (2*t+2*tail.length+4)
        (2*bits.length+5-(2*t+2*tail.length+4)) _ r hr
      rw [Nat.add_sub_of_le htime] at hm
      exact ⟨r,hm,by omega,by simp [Result,parts,hfirst,hsecond,hf]⟩
    | some second =>
      rcases second with ⟨s,fields⟩
      have htail := unary_bounded hsecond
      have hb : bits=word t s fields := by
        rw [UnaryMachine.unary_decomposition hfirst,UnaryMachine.unary_decomposition hsecond]
        rfl
      obtain ⟨r,hr,hf,hs,_⟩ := header_run t s fields
      rw [←hb] at hr
      have htime : 2*t+2*s+5≤2*bits.length+5 := by omega
      have hm := runFrom_moreFuel machine (2*t+2*s+5) (2*bits.length+5-(2*t+2*s+5)) _ r hr
      rw [Nat.add_sub_of_le htime] at hm
      exact ⟨r,hm,by omega,by simpa only [Result,parts,hfirst,Option.bind_some,hsecond,Option.map_some] using hf⟩

end NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
