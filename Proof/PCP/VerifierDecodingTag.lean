import Proof.PCP.VerifierDecodingTagRead

/-! Total literal small-field reader and exact canonical write/move tests.
This is the first sequential record consumer: it covers malformed short
fields as well as all sixteen possible four-bit action tag words. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TagMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend (bits : List Bool) : Word := fun i => bits[i.val]?.getD false

theorem prefixWord_extend (bits : List Bool) (n : ℕ) (hn : n ≤ bits.length) (h4 : n ≤ 4) :
    prefixWord (extend bits) n = bits.take n := by
  apply List.ext_getElem
  · simp [prefixWord_length _ _ h4,Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa only [List.length_take,Nat.min_eq_left hn] using hj
    have hib : i < bits.length := lt_of_lt_of_le hin hn
    simp only [prefixWord,List.getElem_take]
    rw [List.getElem_ofFn]
    simp only [extend,List.getElem?_eq_getElem hib,Option.getD_some]

noncomputable def Result (limit : Fin 5) (pre bits : List Bool)
    (result : Configuration 1 (Fintype.card Control)) : Prop :=
  if limit.val ≤ bits.length then
    result = cfg ⟨2*limit.val,by omega⟩ (received (extend bits) limit.val)
      (pre++frame bits) (pre.length+2*limit.val)
  else result = rejected (pre++frame bits) (pre.length+2*bits.length+1)

/-- Actual total execution on every suffix of a framed literal code. -/
theorem bounded_run (pre bits : List Bool) (limit : Fin 5) :
    ∃ receipt,
      runFrom (machine limit) (2*limit.val+1)
        (cfg 0 (fun _ => false) (pre++frame bits) pre.length) = some receipt ∧
      receipt.steps ≤ 2*limit.val+1 ∧ Result limit pre bits receipt.final := by
  by_cases h : limit.val ≤ bits.length
  · obtain ⟨r,hr,hf,hs,_⟩ := read_run pre (frame (bits.drop limit.val)) (extend bits) limit
    have he : pre++Streaming.marks (prefixWord (extend bits) limit.val)++frame (bits.drop limit.val) = pre++frame bits := by
      rw [prefixWord_extend bits limit.val h (by omega),List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    rw [he] at hr hf
    have hm := runFrom_moreFuel (machine limit) (2*limit.val) 1 _ r hr
    exact ⟨r,hm,by omega,by simpa [Result,h] using hf⟩
  · obtain ⟨r,hr,hf,hs,_⟩ := reject_run pre (extend bits) limit bits.length (by omega)
    have he : prefixWord (extend bits) bits.length = bits := by
      simpa using prefixWord_extend bits bits.length (Nat.le_refl _) (by omega)
    rw [he] at hr hf
    have ht : 2*bits.length+1 ≤ 2*limit.val+1 := by omega
    have hm := runFrom_moreFuel (machine limit) (2*bits.length+1) (2*limit.val+1-(2*bits.length+1)) _ r hr
    rw [Nat.add_sub_of_le ht] at hm
    exact ⟨r,hm,by omega,by simpa [Result,h] using hf⟩

def tagWord (bits : Word) : List Bool := [bits 0,bits 1,bits 2,bits 3]
def valid (present : Bool) (bits : Word) : Bool :=
  if present then (bits 0 || !(bits 1)) && (!(bits 2) || !(bits 3))
  else !(bits 0) && !(bits 1) && !(bits 2) && !(bits 3)

theorem valid_present (bits : Word) :
    valid true bits = true ↔
      writeCode (decodeWrite [bits 0,bits 1]) ++ moveCode (decodeMove [bits 2,bits 3]) = tagWord bits := by
  cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;> cases h3 : bits 3 <;>
    simp [valid,tagWord,decodeWrite,decodeMove,writeCode,moveCode,h0,h1,h2,h3]

theorem valid_absent (bits : Word) : valid false bits = true ↔ tagWord bits = List.replicate 4 false := by
  cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;> cases h3 : bits 3 <;>
    simp [valid,tagWord,List.replicate_succ,h0,h1,h2,h3]

noncomputable def accepted (present : Bool) (state : Fin (Fintype.card Control)) : Bool :=
  match code.symm state with
  | none => false
  | some (phase,bits) => decide (phase.val = 8) && valid present bits

theorem tag_run (pre tail : List Bool) (bits : Word) (present : Bool) :
    let source := pre++Streaming.marks (tagWord bits)++tail
    ∃ receipt,
      runFrom (machine 4) 8 (cfg 0 (fun _ => false) source pre.length) = some receipt ∧
      receipt.final = cfg 8 bits source (pre.length+8) ∧ receipt.steps = 8 ∧
      accepted present receipt.final.control = valid present bits := by
  have he : prefixWord bits 4 = tagWord bits := by simp [prefixWord,tagWord,List.ofFn_succ]
  obtain ⟨r,hr,hf,hs,_⟩ := read_run pre tail bits 4
  change runFrom (machine 4) 8
    (cfg 0 (fun _ => false) (pre++Streaming.marks (prefixWord bits 4)++tail) pre.length) = some r at hr
  change r.final = cfg 8 (received bits 4)
    (pre++Streaming.marks (prefixWord bits 4)++tail) (pre.length+8) at hf
  rw [he] at hr
  rw [he,received_four] at hf
  refine ⟨r,hr,hf,hs,?_⟩
  simp [hf,cfg,accepted]

end NearCubicWires.RepairSource.VerifierDecoding.TagMachine
