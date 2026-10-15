import Proof.MachineModel.ClockDyadicLedger

/-! Compute 2+v₂(N) by the literal leading-zero scan of the counted binary
word, with two constant initial output marks and a paid head reset. -/
namespace NearCubicWires.RepairOrdinary.ClockDegree
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem first_one (bits : List Bool) (h : value bits ≠ 0) :
    ∃ k tail, bits=List.replicate k false++true::tail := by
  induction bits with
  | nil => exact (h rfl).elim
  | cons b bs ih =>
    cases b with
    | true => exact ⟨0,bs,rfl⟩
    | false =>
      have hb : value bs≠0 := by intro he; apply h; simp [value,he]
      obtain ⟨k,tail,ht⟩ := ih hb
      exact ⟨k+1,tail,by simp [List.replicate_succ,ht]⟩

theorem split_value (k : ℕ) (tail : List Bool) :
    value (List.replicate k false++true::tail) = 2^k*(2*value tail+1) := by
  induction k with
  | zero => simp [value,Nat.add_comm]
  | succ k ih => simp only [List.replicate_succ,List.cons_append,value,Bool.toNat_false,Nat.zero_add,ih,pow_succ]; ring

theorem split_degree (k : ℕ) (tail : List Bool) :
    PowerSlice.degree (value (List.replicate k false++true::tail)) = k+2 := by
  have hodd : ¬2 ∣ 2*value tail+1 := by omega
  have hn : 2*value tail+1≠0 := by omega
  rw [PowerSlice.degree,split_value,Nat.factorization_mul (by positivity) hn]
  simp only [Finsupp.add_apply,Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hodd]
  omega

def raw : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 4
  rule := fun s scanned =>
    if s.val=0 then some ⟨1,fun i => if i.val=1 then some true else none,
      fun i => if i.val=1 then .right else .stay⟩
    else if s.val=1 then some ⟨2,fun i => if i.val=1 then some true else none,
      fun i => if i.val=1 then .right else .stay⟩
    else if s.val=2 then some ⟨3,fun _ => none,fun i => if i.val=0 then .right else .stay⟩
    else if s.val=3 then some (if scanned 0 then
      ⟨4,fun _ => none,fun _ => .stay⟩ else
      ⟨2,fun i => if i.val=1 then some true else none,fun _ => .right⟩)
    else none

def config (s : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 5 :=
  ⟨s,![pos,out.length],![source,out]⟩
@[simp] theorem config_cells (s : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (config s source pos out).tapeCells=source.length+out.length := by
  simp [config,Configuration.tapeCells,Fin.sum_univ_succ]

theorem mark_step (source out : List Bool) (pos : ℕ) :
    step raw (config 2 source pos out)=some (config 3 source (pos+1) out) := by
  simp [step,raw,config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem zero_step (pre tail out : List Bool) :
    step raw (config 3 (pre++false::tail) pre.length out)=
      some (config 2 (pre++false::tail) (pre.length+1) (out++[true])) := by
  simp [step,raw,config,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem one_step (pre tail out : List Bool) :
    step raw (config 3 (pre++true::tail) pre.length out)=
      some (config 4 (pre++true::tail) pre.length out) := by
  simp [step,raw,config,Configuration.scanned,Streaming.read_append]
  rfl

theorem scan_prefix (k : ℕ) (pre tail out : List Bool) :
    Prefix raw ((pre++frame (List.replicate k false++true::tail)).length+out.length+k)
      (2*k+2)
      (config 2 (pre++frame (List.replicate k false++true::tail)) pre.length out)
      (config 4 (pre++frame (List.replicate k false++true::tail)) (pre.length+2*k+1)
        (out++List.replicate k true)) := by
  induction k generalizing pre out with
  | zero =>
    have h1 := one_step (pre++[true]) (frame tail) out
    have h1' : step raw (config 3 (pre++frame (true::tail)) (pre.length+1) out)=
        some (config 4 (pre++frame (true::tail)) (pre.length+1) out) := by
      simpa [frame,List.append_assoc] using h1
    have hp := Prefix.step (by simp :
        (config 3 (pre++frame (true::tail)) (pre.length+1) out).tapeCells≤
          (pre++frame (true::tail)).length+out.length)
      (by rfl : raw.halted (3 : Fin 5)=false) h1' (Prefix.refl _ (by simp))
    simpa using Prefix.step (by simp) (by rfl : raw.halted (2 : Fin 5)=false)
      (mark_step (pre++frame (true::tail)) out pre.length) hp
  | succ k ih =>
    let source := pre++frame (List.replicate (k+1) false++true::tail)
    have hsource : (pre++[true,false])++frame (List.replicate k false++true::tail)=source := by
      simp [source,List.replicate_succ,frame,List.append_assoc]
    have hi := ih (pre++[true,false]) (out++[true])
    rw [hsource] at hi
    have hspace : source.length+(out++[true]).length+k = source.length+out.length+(k+1) := by simp; omega
    rw [hspace] at hi
    have htail : Prefix raw (source.length+out.length+(k+1)) (2*k+2)
        (config 2 source (pre.length+2) (out++[true]))
        (config 4 source (pre.length+2*(k+1)+1) (out++List.replicate (k+1) true)) := by
      have hrep : List.replicate (k+1) true = [true]++List.replicate k true := by simp [List.replicate_succ]
      rw [hrep]
      have hpos : (pre++[true,false]).length+2*k+1=pre.length+2*(k+1)+1 := by simp; omega
      rw [hpos] at hi
      simpa [List.append_assoc] using hi
    have hz := zero_step (pre++[true]) (frame (List.replicate k false++true::tail)) out
    have hz' : step raw (config 3 source (pre.length+1) out)=
        some (config 2 source (pre.length+2) (out++[true])) := by
      simpa [source,List.replicate_succ,frame,List.append_assoc] using hz
    have hp := Prefix.step (by simp :
        (config 3 source (pre.length+1) out).tapeCells≤ source.length+out.length+(k+1))
      (by rfl : raw.halted (3 : Fin 5)=false) hz' htail
    have result := Prefix.step (by simp :
        (config 2 source pre.length out).tapeCells≤ source.length+out.length+(k+1))
      (by rfl : raw.halted (2 : Fin 5)=false) (mark_step source out pre.length) hp
    simpa [source,Nat.mul_add,Nat.add_assoc] using result

theorem boot_step (state : Fin 5) (h : state.val<2) (source out : List Bool) (pos : ℕ) :
    step raw (config state source pos out)=
      some (config ⟨state.val+1,by omega⟩ source pos (out++[true])) := by
  have hs : state=0 ∨ state=1 := by omega
  rcases hs with rfl | rfl <;> simp [step,raw,config] <;> apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Streaming.write_append])

theorem raw_run (k : ℕ) (tail : List Bool) :
    ∃ r : ExecutionReceipt 2 5,
      run raw (2*k+4) ![frame (List.replicate k false++true::tail),[]]=some r ∧
      r.final.tapes 0=frame (List.replicate k false++true::tail) ∧
      r.final.tapes 1=List.replicate (k+2) true ∧ r.steps=2*k+4 := by
  let source := frame (List.replicate k false++true::tail)
  have hp := scan_prefix k [] tail [true,true]
  have h0 := boot_step 0 (by decide) source [] 0
  have h1 := boot_step 1 (by decide) source [true] 0
  have hbody : Prefix raw (source.length+2+k) (2*k+2)
      (config 2 source 0 [true,true])
      (config 4 source (2*k+1) (List.replicate (k+2) true)) := by
    have he : List.replicate (k+2) true=[true,true]++List.replicate k true := by
      rw [show k+2=2+k by omega,List.replicate_add]
      rfl
    simpa [source,he] using hp
  have h := Prefix.step (by simp; omega : (config 0 source 0 []).tapeCells≤ source.length+2+k)
    (by rfl : raw.halted (0 : Fin 5)=false) h0
    (Prefix.step (by simp; omega) (by rfl : raw.halted (1 : Fin 5)=false) h1 hbody)
  obtain ⟨r,hr,hf,hs,_⟩ := h.run (by rfl) (by simp; omega)
  refine ⟨r,?_,by simp [hf,config,source],by simp [hf,config],by omega⟩
  have hi : initialConfiguration raw ![source,[]] = config 0 source 0 [] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  change runFrom raw _ (initialConfiguration raw ![source,[]])=some r
  rw [hi]
  simpa [Nat.add_assoc] using hr

def machine : Machine 3 7 := Rewind.machine raw

theorem degree_run (N : ℕ) (hn : 0<N) :
    ∃ scratch, scratch≤2*(ClockBinary.word N).length+4 ∧
      ∃ r : ExecutionReceipt 3 7,
        run machine (4*(ClockBinary.word N).length+10)
          ![frame (ClockBinary.word N),[],[]]=some r ∧
        r.final.tapes 0=frame (ClockBinary.word N) ∧
        r.final.tapes 1=List.replicate (PowerSlice.degree N) true ∧
        r.final.tapes 2=List.replicate scratch false ∧
        (∀ i,r.final.heads i=0) ∧ r.steps≤4*(ClockBinary.word N).length+10 := by
  obtain ⟨k,tail,he⟩ := first_one (ClockBinary.word N) (by rw [ClockBinary.word_value]; omega)
  have hlen : k+1+tail.length=(ClockBinary.word N).length := by
    have := congrArg List.length he
    simp at this
    omega
  have hd : PowerSlice.degree N=k+2 := by
    rw [← ClockBinary.word_value N,he]
    exact split_degree k tail
  obtain ⟨base,hb,h0,h1,hs⟩ := raw_run k tail
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have htime : 2*base.steps+2≤4*(ClockBinary.word N).length+10 := by omega
  have hmore := run_moreFuel machine (2*base.steps+2)
    (4*(ClockBinary.word N).length+10-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hmore
  refine ⟨base.steps,by omega,r,?_,?_,?_,?_,hh,by omega⟩
  · have hin : (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
        ![frame (List.replicate k false++true::tail),[]] (fun _ : Fin 1 => [])) =
          ![frame (List.replicate k false++true::tail),[],[]] := by
        funext i; fin_cases i <;> rfl
    change run machine _ (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![frame (List.replicate k false++true::tail),[]] (fun _ : Fin 1 => []))=some r at hmore
    rw [hin] at hmore
    simpa [he] using hmore
  · simpa [he] using (ht 0).trans h0
  · simpa [hd] using (ht 1).trans h1
  · simpa using hcounter

end NearCubicWires.RepairOrdinary.ClockDegree
