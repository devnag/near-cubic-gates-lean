import Proof.MachineModel.OrdinaryMemoryInitial

/-! Paid initial key generation and rewind in the actual checker's layout.
The rewind counter is retained on tape14 and never assumed cleared. -/
namespace NearCubicWires.RepairOrdinary.MemoryPrepared
open LocalBitMultitape MemoryLog MemorySort MemoryCompare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 15 ≃ Fin 15 where
  toFun := ![7,8,13,14,0,1,2,3,4,5,6,9,10,11,12]
  invFun := ![4,5,6,7,8,9,10,0,1,11,12,13,14,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 15 → Fin 15) =
    ![4,5,6,7,8,9,10,0,1,11,12,13,14,2,3] := rfl
def prepare : Machine 15 7 :=
  TapeRenaming.machine layout (TapeEmbedding.machine 11 (Rewind.machine MemoryInitial.machine))
def sourceInput (source : List Bool) : Fin 15 → List Bool :=
  fun i => if i = 7 then source else []
def check : Machine 15 43 := TapeEmbedding.machine 1 MemoryLoop.machine
def machine : Machine 15 50 := Composition.machine prepare check

theorem prepare_run (n : ℕ) (bits suffix : List Bool) (hlen : bits.length = 2*n) :
    ∃ r : ExecutionReceipt 15 7,
      run prepare (8*n+4) (sourceInput (frame bits++suffix)) = some r ∧
      (∀ i : Fin 14, r.final.tapes (i.castAdd 1) =
        MemoryBlank.tapes (frame bits++suffix) (List.replicate n false) i) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 8*n+4 := by
  obtain ⟨base, hb, ht, hs, _⟩ := MemoryInitial.initial_run n bits suffix hlen
  obtain ⟨reset, hr, ho, hh, hsteps, _⟩ := Rewind.reset_run MemoryInitial.machine
    (4*n+1) ![frame bits++suffix,[],[]] base hb
  have htime : 2*base.steps+2 = 8*n+4 := by rw [hs]; omega
  rw [htime] at hr hsteps
  let otherHeads := fun _ : Fin 11 => 0
  let otherTapes := fun _ : Fin 11 => ([] : List Bool)
  have htapes : (fun i : Fin (3+1) => Fin.addCases
      (![frame bits++suffix,[],[]] : Fin 3 → List Bool) (fun _ : Fin 1 => []) i) =
      ![frame bits++suffix,[],[],[]] := by
    funext i
    fin_cases i <;> rfl
  rw [htapes] at hr
  have he := TapeEmbedding.run_embed (Rewind.machine MemoryInitial.machine)
    otherHeads otherTapes _ _ reset hr
  have renamed := TapeRenaming.run_rename layout
    (TapeEmbedding.machine 11 (Rewind.machine MemoryInitial.machine)) _ _ _ he
  let r := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes reset)
  have hi : TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
        (initialConfiguration (Rewind.machine MemoryInitial.machine)
          (![frame bits++suffix,[],[],[]]))) =
      initialConfiguration prepare (sourceInput (frame bits++suffix)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, initialConfiguration,
        otherHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, initialConfiguration,
        otherTapes, sourceInput, Fin.addCases]
  rw [hi] at renamed
  refine ⟨r, renamed, ?_, ?_, hsteps⟩
  · intro i
    have h0 := ho 0
    have h1 := ho 1
    have h2 := ho 2
    rw [ht] at h0 h1 h2
    change reset.final.tapes 0 = frame bits++suffix at h0
    change reset.final.tapes 1 = frame (List.replicate n false) at h1
    change reset.final.tapes 2 = [true] at h2
    fin_cases i <;> simp [r, TapeRenaming.receipt, TapeRenaming.config,
      TapeEmbedding.receipt, TapeEmbedding.config, MemoryBlank.tapes,
      otherTapes, Fin.addCases, h0, h1, h2]
  · intro i
    fin_cases i <;> simp [r, TapeRenaming.receipt, TapeRenaming.config,
      TapeEmbedding.receipt, TapeEmbedding.config, otherHeads, Fin.addCases, hh]

theorem checked_run {N : ℕ} (I W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^(I+2))
    (ha : ∀ i, (events i).cell.2 < 2^W)
    (bits suffix : List Bool) (hlen : bits.length = 2*(I+2))
    (hsource : frame bits++suffix =
      StablePartition.stream (SortCarrier.sorted (request I (I+2) W events)))
    (hkey : key I W MemoryScan.blank = List.replicate (I+2) false) :
    ∃ r : ExecutionReceipt 15 50,
      run machine (8*(I+2)+4+1+(N*(240*(I+2)+182)+1))
        (sourceInput (frame bits++suffix)) = some r ∧
      r.final.tapes 13 =
        [(MemoryLog.run (fun _ => false) ((List.finRange N).map events)).isSome] ∧
      r.final.heads 13 = 0 := by
  obtain ⟨pre, hp, hpt, hph, _⟩ := prepare_run (I+2) bits suffix hlen
  obtain ⟨body, hb, hbo, hbh, _⟩ := MemoryBlank.blank_run I W events hN hc ha
  rw [← hsource, hkey] at hb
  let extraHeads := fun _ : Fin 1 => 0
  let extraTapes := fun _ : Fin 1 => pre.final.tapes 14
  have he := TapeEmbedding.run_embed MemoryLoop.machine extraHeads extraTapes _ _ body hb
  have hi : Composition.restart pre.final check.start =
      TapeEmbedding.config extraHeads extraTapes
        (initialConfiguration MemoryLoop.machine
          (MemoryBlank.tapes (frame bits++suffix) (List.replicate (I+2) false))) := by
    apply configuration_ext
    · rfl
    · funext i
      change pre.final.heads i = _
      rw [hph]
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, extraHeads, Fin.addCases]
    · funext i
      change pre.final.tapes i = Fin.addCases
        (MemoryBlank.tapes (frame bits++suffix) (List.replicate (I+2) false)) extraTapes i
      refine Fin.addCases (n := 1) (m := 14)
        (motive := fun j => pre.final.tapes j = Fin.addCases
          (MemoryBlank.tapes (frame bits++suffix) (List.replicate (I+2) false)) extraTapes j)
        (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.addCases_left] using hpt j
      · fin_cases j; rfl
  rw [← hi] at he
  have hj := Composition.run_join prepare check (8*(I+2)+4) (N*(240*(I+2)+182)+1)
    (initialConfiguration prepare (sourceInput (frame bits++suffix))) pre
    (TapeEmbedding.receipt extraHeads extraTapes body) hp he
  refine ⟨Composition.joinedReceipt pre (TapeEmbedding.receipt extraHeads extraTapes body),
    hj, ?_, ?_⟩
  · simpa [Composition.joinedReceipt, Composition.rightConfig, TapeEmbedding.receipt,
      TapeEmbedding.config, Fin.addCases] using hbo
  · simpa [Composition.joinedReceipt, Composition.rightConfig, TapeEmbedding.receipt,
      TapeEmbedding.config, Fin.addCases] using hbh

theorem zero_key (I W : ℕ) :
    key I W MemoryScan.blank = List.replicate (I+2) false := by
  have hz (n : ℕ) : SignedSortKey.binary n 0 = List.replicate n false := by
    induction n with
    | zero => rfl
    | succ n ih => simp [SignedSortKey.binary, ih, List.replicate_succ]
  simpa only [key, MemoryScan.blank, cellCode, Nat.zero_mul, Nat.add_zero] using hz (I+2)

theorem sorted_run {N : ℕ} (I W : ℕ) (events : Fin N → Event)
    (hn : 0 < N) (hN : N ≤ 2^I)
    (hc : ∀ i, cellCode W (events i).cell < 2^(I+2))
    (ha : ∀ i, (events i).cell.2 < 2^W) :
    ∃ r : ExecutionReceipt 15 50,
      run machine (8*(I+2)+4+1+(N*(240*(I+2)+182)+1))
        (sourceInput (StablePartition.stream (SortCarrier.sorted (request I (I+2) W events)))) =
          some r ∧
      r.final.tapes 13 =
        [(MemoryLog.run (fun _ => false) ((List.finRange N).map events)).isSome] ∧
      r.final.heads 13 = 0 := by
  have hperm := SortCarrier.sorted_perm (request I (I+2) W events)
  have hlength : (SortCarrier.sorted (request I (I+2) W events)).length = N := by
    simpa [request, DominanceSort.fixedRequest] using hperm.length_eq
  cases he : SortCarrier.sorted (request I (I+2) W events) with
  | nil => simp [he] at hlength; omega
  | cons first rest =>
    have hm : first ∈ (request I (I+2) W events).records :=
      hperm.mem_iff.mp (by simp [he])
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
    have hwidth : (RadixSemantics.word first).length = 2*(I+2) := by
      rw [← hi, encoded_width]
      omega
    have hsource : frame (RadixSemantics.word first)++StablePartition.stream rest =
        StablePartition.stream (SortCarrier.sorted (request I (I+2) W events)) := by
      rw [he]
      simp [StablePartition.stream, StablePartition.recordsBits, List.append_assoc,
        RadixSemantics.word, StablePartition.recordBits, frame]
    obtain ⟨r, hr, ho, hh⟩ := checked_run I W events hN hc ha
      (RadixSemantics.word first) (StablePartition.stream rest) hwidth hsource (zero_key I W)
    rw [hsource, he] at hr
    exact ⟨r, hr, ho, hh⟩

end NearCubicWires.RepairOrdinary.MemoryPrepared
