import Proof.MachineModel.Machine

/-! Paid execution of the incidence producer: the seek/return/copy/zero loops,
one monomial, the whole ordered stream, the receipt, and a coarse linear
cost bound `(B+2) * streamLength + 1`. -/
namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Reading inside appended words -/

theorem read_prefix (l rest : List Bool) (j : ℕ) (hj : j < l.length) :
    readTapeBit (l ++ rest) j = readTapeBit l j := by
  simp only [readTapeBit, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

theorem read_suffix (l rest : List Bool) (j : ℕ) :
    readTapeBit (l ++ rest) (l.length + j) = readTapeBit rest j := by
  simp only [readTapeBit, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem read_shift (pre mid rest : List Bool) (j : ℕ) (hj : j < mid.length) :
    readTapeBit (pre ++ mid ++ rest) (pre.length + j) = readTapeBit mid j := by
  rw [List.append_assoc, read_suffix, read_prefix _ _ j hj]

theorem read_block_mark (d j : ℕ) (hj : j ≤ d) : readTapeBit (block d) j = true := by
  rw [block, read_prefix _ _ j (by simp only [List.length_replicate]; omega)]
  have hj' : j < d+1 := by omega
  simp [readTapeBit, List.getD_eq_getElem?_getD, hj']

theorem read_block_end (d : ℕ) : readTapeBit (block d) (d+1) = false := by
  have h := Streaming.read_append (List.replicate (d+1) true) [] false
  simpa [block] using h

theorem read_monomial_block (m : List ℕ) (j : ℕ) (hj : j < (m.flatMap block).length) :
    readTapeBit (monomialWord m) (j+1) = readTapeBit (m.flatMap block) j := by
  simp only [monomialWord, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_left hj]

theorem read_monomial_end (m : List ℕ) :
    readTapeBit (monomialWord m) ((m.flatMap block).length+1) = false := by
  simp only [monomialWord, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_concat_length]
  rfl

/-! ## Loops -/

theorem seek_loop (W : List Bool) (ih B th : ℕ) (L : List Bool) (sh : ℕ) (out : List Bool) (c r : ℕ)
    (hr : ∀ j < r, readTapeBit W (ih+j) = true) :
    Timed machine r (cfg 2 W ih B th L sh out c) (cfg 2 W (ih+r) B (th+r) L (sh+r) out c) := by
  induction r generalizing ih th sh with
  | zero => exact Timed.refl machine _
  | succ r ih' =>
    have h1 := Timed.single (p := machine) (by rfl)
      (seek_step W ih B th L sh out c (hr 0 (Nat.succ_pos r)))
    have h2 := ih' (ih+1) (th+1) (sh+1) (fun j hj => by
      have e : ih+1+j = ih+(j+1) := by omega
      rw [e]; exact hr (j+1) (by omega))
    have h := h1.trans h2
    rw [cfg_congr 2 W B L out (by omega : ih+1+r = ih+(r+1)) (by omega : th+1+r = th+(r+1))
      (by omega : sh+1+r = sh+(r+1)) rfl] at h
    have e : 1 + r = r + 1 := Nat.add_comm 1 r
    rw [e] at h; exact h

theorem return_loop (W : List Bool) (ih B k : ℕ) (hk : k < B) (L out : List Bool) (c : ℕ) :
    Timed machine (k+1) (cfg 3 W ih B (k+1) L k out c) (cfg 3 W ih B 0 L 0 out c) := by
  induction k with
  | zero => exact Timed.single (by rfl) (return_step W ih B 0 hk L out c)
  | succ k ih' =>
    have h1 := return_step W ih B (k+1) hk L out c
    rw [Nat.add_sub_cancel] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ih' (by omega))
    have e : 1 + (k+1) = k+1+1 := by omega
    rw [e] at h; exact h

theorem copy_loop (W : List Bool) (ih B : ℕ) (L out : List Bool) (c k r : ℕ) (hkr : k + r = B) :
    Timed machine r (cfg 4 W ih B (k+1) L k (out ++ copied L k) c)
      (cfg 4 W ih B (B+1) L B (out ++ copied L B) c) := by
  induction r generalizing k with
  | zero =>
    have hk : k = B := by omega
    subst hk
    exact Timed.refl machine _
  | succ r ih' =>
    have h1 := copy_step W ih B k (by omega) L (out ++ copied L k) c
    rw [List.append_assoc, ← copied_succ] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ih' (k+1) (by omega))
    have e : 1 + r = r + 1 := Nat.add_comm 1 r
    rw [e] at h; exact h

theorem zero_loop (W : List Bool) (ih B k : ℕ) (hk : k < B) (g : Fin B → Bool) (out : List Bool) (c : ℕ) :
    Timed machine (k+1) (cfg 5 W ih B (k+1) (List.ofFn (zeroed g (k+1))) k out c)
      (cfg 5 W ih B 0 (List.ofFn (zeroed g 0)) 0 out c) := by
  induction k with
  | zero =>
    have h := zero_step W ih B 0 hk (List.ofFn (zeroed g 1)) out c
    rw [zeroed_write g 0 hk] at h
    exact Timed.single (by rfl) h
  | succ k ih' =>
    have h1 := zero_step W ih B (k+1) hk (List.ofFn (zeroed g (k+1+1))) out c
    rw [zeroed_write g (k+1) hk, Nat.add_sub_cancel] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ih' (by omega))
    have e : 1 + (k+1) = k+1+1 := by omega
    rw [e] at h; exact h

theorem zero_phase (W : List Bool) (ih B : ℕ) (g : Fin B → Bool) (out : List Bool) (c : ℕ) :
    Timed machine B (cfg 5 W ih B B (List.ofFn g) (B-1) out c)
      (cfg 5 W ih B 0 (List.replicate B false) 0 out c) := by
  cases B with
  | zero =>
    rw [List.ofFn_zero]
    exact Timed.refl machine _
  | succ k =>
    have h := zero_loop W ih (k+1) k (Nat.lt_succ_self k) g out c
    rw [zeroed_top g, zeroed_zero g] at h
    simpa only [Nat.add_sub_cancel] using h

/-! ## One block, all blocks of a monomial, one monomial -/

theorem block_timed (W : List Bool) (ih B d : ℕ) (hd : d < B) (S : List ℕ) (out : List Bool) (c : ℕ)
    (hmark : ∀ j ≤ d, readTapeBit W (ih+j) = true) (hend : readTapeBit W (ih+(d+1)) = false) :
    Timed machine (blockCost d) (cfg 1 W ih B 1 (maskOf B S) 0 out c)
      (cfg 1 W (ih+(d+2)) B 1 (maskOf B (d :: S)) 0 out c) := by
  have s1 : Timed machine 1 (cfg 1 W ih B 1 (maskOf B S) 0 out c)
      (cfg 2 W (ih+1) B 1 (maskOf B S) 0 out c) :=
    Timed.single (by rfl) (row_seek W ih B 1 (maskOf B S) 0 out c (hmark 0 (Nat.zero_le d)))
  have s2 : Timed machine d (cfg 2 W (ih+1) B 1 (maskOf B S) 0 out c)
      (cfg 2 W (ih+1+d) B (d+1) (maskOf B S) d out c) := by
    have h := seek_loop W (ih+1) B 1 (maskOf B S) 0 out c d (fun j hj => by
      have e : ih+1+j = ih+(j+1) := by omega
      rw [e]; exact hmark (j+1) (by omega))
    rw [cfg_congr 2 W B (maskOf B S) out rfl (Nat.add_comm 1 d) (Nat.zero_add d) rfl] at h
    exact h
  have s3 : Timed machine 1 (cfg 2 W (ih+1+d) B (d+1) (maskOf B S) d out c)
      (cfg 3 W (ih+1+d+1) B (d+1) (maskOf B (d :: S)) d out c) := by
    have h := seek_write W (ih+1+d) B (d+1) (maskOf B S) d out c (by
      have e : ih+1+d = ih+(d+1) := by omega
      rw [e]; exact hend)
    rw [maskOf_write B S d hd] at h
    exact Timed.single (by rfl) h
  have s4 : Timed machine (d+1) (cfg 3 W (ih+1+d+1) B (d+1) (maskOf B (d :: S)) d out c)
      (cfg 3 W (ih+1+d+1) B 0 (maskOf B (d :: S)) 0 out c) :=
    return_loop W (ih+1+d+1) B d hd (maskOf B (d :: S)) out c
  have s5 : Timed machine 1 (cfg 3 W (ih+1+d+1) B 0 (maskOf B (d :: S)) 0 out c)
      (cfg 1 W (ih+1+d+1) B 1 (maskOf B (d :: S)) 0 out c) :=
    Timed.single (by rfl) (return_done W (ih+1+d+1) B (maskOf B (d :: S)) 0 out c)
  have h := (((s1.trans s2).trans s3).trans s4).trans s5
  rw [cfg_congr 1 W B (maskOf B (d :: S)) out (by omega : ih+1+d+1 = ih+(d+2)) rfl rfl rfl] at h
  have e : 1 + d + 1 + (d+1) + 1 = blockCost d := by unfold blockCost; omega
  rw [e] at h; exact h

theorem blocks_timed (W : List Bool) (ih B : ℕ) (m : List ℕ) (hm : ∀ d ∈ m, d < B) (S : List ℕ)
    (out : List Bool) (c : ℕ)
    (hread : ∀ j < (m.flatMap block).length, readTapeBit W (ih+j) = readTapeBit (m.flatMap block) j) :
    Timed machine ((m.map blockCost).sum) (cfg 1 W ih B 1 (maskOf B S) 0 out c)
      (cfg 1 W (ih+(m.flatMap block).length) B 1 (maskOf B (m.reverse ++ S)) 0 out c) := by
  induction m generalizing ih S with
  | nil => simpa using Timed.refl machine (cfg 1 W ih B 1 (maskOf B S) 0 out c)
  | cons d m ihm =>
    have hd : d < B := hm d (List.mem_cons_self ..)
    have hlen : ((d :: m).flatMap block).length = (d+2) + (m.flatMap block).length := by
      rw [List.flatMap_cons, List.length_append, block_length]
    have hmark : ∀ j ≤ d, readTapeBit W (ih+j) = true := by
      intro j hj
      rw [hread j (by rw [hlen]; omega), List.flatMap_cons, read_prefix _ _ j (by rw [block_length]; omega)]
      exact read_block_mark d j hj
    have hend : readTapeBit W (ih+(d+1)) = false := by
      rw [hread (d+1) (by rw [hlen]; omega), List.flatMap_cons, read_prefix _ _ (d+1) (by rw [block_length]; omega)]
      exact read_block_end d
    have s1 := block_timed W ih B d hd S out c hmark hend
    have s2 := ihm (ih+(d+2)) (fun e he => hm e (List.mem_cons_of_mem d he)) (d :: S) (fun j hj => by
      have e : ih+(d+2)+j = ih+((d+2)+j) := by omega
      rw [e, hread ((d+2)+j) (by rw [hlen]; omega), List.flatMap_cons]
      have h := read_suffix (block d) (m.flatMap block) j
      rw [block_length] at h
      exact h)
    have h := s1.trans s2
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, hlen]
    rw [cfg_congr 1 W B (maskOf B (m.reverse ++ d :: S)) out
      (by omega : ih+(d+2)+(m.flatMap block).length = ih+((d+2)+(m.flatMap block).length)) rfl rfl rfl] at h
    simpa only [List.map_cons, List.sum_cons] using h

theorem monomial_timed (pre rest : List Bool) (B : ℕ) (m : List ℕ) (hm : ∀ d ∈ m, d < B)
    (out : List Bool) (c : ℕ) :
    Timed machine (monomialCost B m)
      (cfg 0 (pre ++ monomialWord m ++ rest) pre.length B 1 (List.replicate B false) 0 out c)
      (cfg 0 (pre ++ monomialWord m ++ rest) (pre.length+(monomialWord m).length) B 1
        (List.replicate B false) 0 (out ++ maskOf B m) (c+1)) := by
  have hstart : readTapeBit (pre ++ monomialWord m ++ rest) pre.length = true := by
    have h := read_shift pre (monomialWord m) rest 0 (by simp [monomialWord])
    rw [Nat.add_zero] at h
    rw [h]; rfl
  have hblocks : ∀ j < (m.flatMap block).length,
      readTapeBit (pre ++ monomialWord m ++ rest) (pre.length+1+j) = readTapeBit (m.flatMap block) j := by
    intro j hj
    have e : pre.length+1+j = pre.length+(j+1) := by omega
    rw [e, read_shift pre _ rest (j+1) (by rw [monomialWord_length]; omega)]
    exact read_monomial_block m j hj
  have hend : readTapeBit (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length) = false := by
    have e : pre.length+1+(m.flatMap block).length = pre.length+((m.flatMap block).length+1) := by omega
    rw [e, read_shift pre _ rest _ (by rw [monomialWord_length]; omega)]
    exact read_monomial_end m
  have s1 : Timed machine 1
      (cfg 0 (pre ++ monomialWord m ++ rest) pre.length B 1 (List.replicate B false) 0 out c)
      (cfg 1 (pre ++ monomialWord m ++ rest) (pre.length+1) B 1 (maskOf B []) 0 out c) := by
    rw [maskOf_nil]
    exact Timed.single (by rfl) (start_row _ pre.length B 1 (List.replicate B false) 0 out c hstart)
  have s2 : Timed machine ((m.map blockCost).sum)
      (cfg 1 (pre ++ monomialWord m ++ rest) (pre.length+1) B 1 (maskOf B []) 0 out c)
      (cfg 1 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length) B 1 (maskOf B m) 0 out c) := by
    have h := blocks_timed _ (pre.length+1) B m hm [] out c hblocks
    rw [List.append_nil, maskOf_congr B (fun i => List.mem_reverse)] at h
    exact h
  have s3 : Timed machine 1
      (cfg 1 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length) B 1 (maskOf B m) 0 out c)
      (cfg 4 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B 1 (maskOf B m) 0
        (out ++ copied (maskOf B m) 0) c) := by
    rw [copied_zero, List.append_nil]
    exact Timed.single (by rfl) (row_copy _ _ B 1 (maskOf B m) 0 out c hend)
  have s4 : Timed machine B
      (cfg 4 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B 1 (maskOf B m) 0
        (out ++ copied (maskOf B m) 0) c)
      (cfg 4 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B (B+1) (maskOf B m) B
        (out ++ maskOf B m) c) := by
    have h := copy_loop (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B
      (maskOf B m) out c 0 B (Nat.zero_add B)
    rw [copied_full (maskOf B m) B (maskOf_length B m)] at h
    exact h
  have s5 : Timed machine 1
      (cfg 4 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B (B+1) (maskOf B m) B
        (out ++ maskOf B m) c)
      (cfg 5 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B B (maskOf B m) (B-1)
        (out ++ maskOf B m) c) :=
    Timed.single (by rfl) (copy_done _ _ B (maskOf B m) (out ++ maskOf B m) c)
  have s6 : Timed machine B
      (cfg 5 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B B (maskOf B m) (B-1)
        (out ++ maskOf B m) c)
      (cfg 5 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B 0
        (List.replicate B false) 0 (out ++ maskOf B m) c) :=
    zero_phase _ _ B (fun i : Fin B => decide (i.val ∈ m)) (out ++ maskOf B m) c
  have s7 : Timed machine 1
      (cfg 5 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B 0
        (List.replicate B false) 0 (out ++ maskOf B m) c)
      (cfg 0 (pre ++ monomialWord m ++ rest) (pre.length+1+(m.flatMap block).length+1) B 1
        (List.replicate B false) 0 (out ++ maskOf B m) (c+1)) :=
    Timed.single (by rfl) (zero_done _ _ B (List.replicate B false) 0 (out ++ maskOf B m) c)
  have h := (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7
  rw [cfg_congr 0 _ B (List.replicate B false) (out ++ maskOf B m)
    (by rw [monomialWord_length]; omega : pre.length+1+(m.flatMap block).length+1 = pre.length+(monomialWord m).length)
    rfl rfl rfl] at h
  have e : 1 + (m.map blockCost).sum + 1 + B + 1 + B + 1 = monomialCost B m := by unfold monomialCost; omega
  rw [e] at h; exact h

/-! ## The whole ordered stream -/

theorem stream_timed (pre tail : List Bool) (B : ℕ) (ms : List (List ℕ))
    (hms : ∀ m ∈ ms, ∀ d ∈ m, d < B) (out : List Bool) (c : ℕ) :
    Timed machine (cost B ms)
      (cfg 0 (pre ++ stream ms ++ tail) pre.length B 1 (List.replicate B false) 0 out c)
      (cfg 6 (pre ++ stream ms ++ tail) (pre.length+(stream ms).length) B 1 (List.replicate B false) 0
        (out ++ table B ms) (c+ms.length)) := by
  induction ms generalizing pre out c with
  | nil =>
    have hr : readTapeBit (pre ++ stream [] ++ tail) pre.length = false := by
      have h := read_shift pre (stream []) tail 0 (by simp [stream_nil])
      rw [Nat.add_zero] at h
      rw [h]; rfl
    have h := Timed.single (p := machine) (by rfl)
      (start_halt (pre ++ stream [] ++ tail) pre.length B 1 (List.replicate B false) 0 out c hr)
    simpa [cost, stream_nil, table_nil] using h
  | cons m ms ih =>
    have hw : pre ++ stream (m :: ms) ++ tail = pre ++ monomialWord m ++ (stream ms ++ tail) := by
      rw [stream_cons, List.append_assoc, List.append_assoc, List.append_assoc]
    have s1 := monomial_timed pre (stream ms ++ tail) B m (hms m (List.mem_cons_self ..)) out c
    have s2 := ih (pre ++ monomialWord m) (fun m' hm' => hms m' (List.mem_cons_of_mem m hm'))
      (out ++ maskOf B m) (c+1)
    have hw2 : pre ++ monomialWord m ++ stream ms ++ tail = pre ++ monomialWord m ++ (stream ms ++ tail) := by
      simp only [List.append_assoc]
    rw [hw2, List.length_append] at s2
    have h := s1.trans s2
    rw [hw, cost_cons,
      show out ++ table B (m :: ms) = out ++ maskOf B m ++ table B ms by rw [table_cons, List.append_assoc],
      show (stream (m :: ms)).length = (monomialWord m).length + (stream ms).length by
        rw [stream_cons, List.length_append],
      List.length_cons]
    rw [cfg_congr 6 _ B (List.replicate B false) (out ++ maskOf B m ++ table B ms)
      (by omega : pre.length+(monomialWord m).length+(stream ms).length =
        pre.length+((monomialWord m).length+(stream ms).length)) rfl rfl
      (by omega : c+1+ms.length = c+(ms.length+1))] at h
    exact h

theorem stream_run (pre tail : List Bool) (B : ℕ) (ms : List (List ℕ))
    (hms : ∀ m ∈ ms, ∀ d ∈ m, d < B) (out : List Bool) (c : ℕ) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom machine (cost B ms)
        (cfg 0 (pre ++ stream ms ++ tail) pre.length B 1 (List.replicate B false) 0 out c) = some r ∧
      r.final = cfg 6 (pre ++ stream ms ++ tail) (pre.length+(stream ms).length) B 1
        (List.replicate B false) 0 (out ++ table B ms) (c+ms.length) ∧
      r.steps = cost B ms :=
  (stream_timed pre tail B ms hms out c).run rfl

/-- The final tapes, spelled out for consumers. -/
theorem stream_run_tapes (pre tail : List Bool) (B : ℕ) (ms : List (List ℕ))
    (hms : ∀ m ∈ ms, ∀ d ∈ m, d < B) (out : List Bool) (c : ℕ) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom machine (cost B ms)
        (cfg 0 (pre ++ stream ms ++ tail) pre.length B 1 (List.replicate B false) 0 out c) = some r ∧
      r.final.control = 6 ∧
      r.final.tapes 0 = pre ++ stream ms ++ tail ∧ r.final.heads 0 = pre.length+(stream ms).length ∧
      r.final.tapes 1 = UnaryTemplate.tape B ∧ r.final.heads 1 = 1 ∧
      r.final.tapes 2 = List.replicate B false ∧ r.final.heads 2 = 0 ∧
      r.final.tapes 3 = out ++ table B ms ∧ r.final.heads 3 = (out ++ table B ms).length ∧
      r.final.tapes 4 = List.replicate (c+ms.length) true ∧ r.final.heads 4 = c+ms.length ∧
      r.steps = cost B ms := by
  obtain ⟨r, hr, hf, hs⟩ := stream_run pre tail B ms hms out c
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs⟩ <;> rw [hf] <;> rfl

/-! ## Coarse cost: linear in the stream length, times the child count -/

theorem monomialCost_le (B : ℕ) (m : List ℕ) : monomialCost B m ≤ (B+2)*(monomialWord m).length := by
  induction m with
  | nil =>
    rw [monomialWord_length]
    simp only [monomialCost, List.map_nil, List.sum_nil, List.flatMap_nil, List.length_nil]
    omega
  | cons d m ih =>
    rw [monomialCost_cons]
    have hl : (monomialWord (d :: m)).length = (monomialWord m).length + (d+2) := by
      rw [monomialWord_length, monomialWord_length, List.flatMap_cons, List.length_append, block_length]
      omega
    rw [hl, Nat.mul_add]
    have hb : blockCost d ≤ (B+2)*(d+2) := by
      have e : (B+2)*(d+2) = B*d+2*B+2*d+4 := by ring
      unfold blockCost
      omega
    omega

theorem cost_le (B : ℕ) (ms : List (List ℕ)) : cost B ms ≤ (B+2)*(stream ms).length+1 := by
  induction ms with
  | nil => simp [cost, stream_nil]
  | cons m ms ih =>
    rw [cost_cons, stream_cons, List.length_append, Nat.mul_add]
    have := monomialCost_le B m
    omega

end NearCubicWires.ExtIncidence
