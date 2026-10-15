import Proof.Assembly.FamilyInit
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
namespace PaidDriverBank
namespace Driver

/-- The two optional letters emitted at each true driver cell. -/
def block (p q : Option Bool) : Nat → List Bool
 | 0 => []
 | n+1 => block p q n ++ p.toList ++ q.toList

@[simp] theorem block_zero (p q : Option Bool) : block p q 0=[] := rfl
@[simp] theorem block_none (n : Nat) : block none none n=[] := by
 induction n with
 | zero => rfl
 | succ n ih => simp [block,ih]

theorem block_front (p q : Option Bool) (n : Nat) :
 block p q (n+1)=p.toList++q.toList++block p q n := by
 induction n with
 | zero => simp [block]
 | succ n ih =>
   calc
    block p q (n+1+1) = block p q (n+1)++p.toList++q.toList := rfl
    _ = (p.toList++q.toList++block p q n)++p.toList++q.toList := by rw [ih]
    _ = p.toList++q.toList++block p q (n+1) := by simp only [block,List.append_assoc]

@[simp] theorem block_single (b : Bool) (n : Nat) :
 block (some b) none n=List.replicate n b := by
 induction n with
 | zero => rfl
 | succ n ih => rw [block_front]; simp [ih,List.replicate_succ]

@[simp] theorem block_double (b : Bool) (n : Nat) :
 block (some b) (some b) n=List.replicate (2*n) b := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [block_front,ih]
   have he : 2*(n+1)=2+2*n := by omega
   rw [he]
   simp [List.replicate_add,List.append_assoc]

@[simp] theorem block_frame (n : Nat) :
 block (some true) (some false) n++[false]=frame (SignedSortKey.binary n 0) := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [block_front]
   simpa [SignedSortKey.binary,frame,List.append_assoc] using congrArg (fun l => true::false::l) ih

variable {t : Nat}

def output (p q z : Fin t → Option Bool) (A : Fin t → List Bool) (n : Nat) :
 Fin t → List Bool := fun i => A i++block (p i) (q i) n++(z i).toList

def machine (src : Fin t) (p q z : Fin t → Option Bool) : Machine t 5 where
 descriptionBits:=0
 start:=0
 halted:=fun s=>s.val==4
 rule:=fun s bits=>
  if s.val=0 then
   if bits src then some ⟨1,p,fun i=>if i=src then .stay else match p i with | none=>.stay | some _=>.right⟩
   else some ⟨2,z,fun i=>if i=src then .left else .stay⟩
  else if s.val=1 then
   some ⟨0,q,fun i=>if i=src then .right else match q i with | none=>.stay | some _=>.right⟩
  else if s.val=2 then
   if bits src then some ⟨3,fun _=>none,fun i=>if i=src then .stay else match p i with | none=>.stay | some _=>.left⟩
   else some ⟨4,fun _=>none,fun i=>if i=src then .right else .stay⟩
  else if s.val=3 then
   some ⟨2,fun _=>none,fun i=>if i=src then .left else match q i with | none=>.stay | some _=>.left⟩
  else none

def forward (src : Fin t) (p q : Fin t → Option Bool)
 (H : Fin t → Nat) (A : Fin t → List Bool) (k : Nat) : Configuration t 5 :=
 ⟨0,fun i=>if i=src then k+1 else H i+(block (p i) (q i) k).length,
   fun i=>A i++block (p i) (q i) k⟩
def middle (src : Fin t) (p q : Fin t → Option Bool)
 (H : Fin t → Nat) (A : Fin t → List Bool) (k : Nat) : Configuration t 5 :=
 ⟨1,fun i=>if i=src then k+1 else H i+(block (p i) (q i) k).length+(p i).toList.length,
   fun i=>A i++block (p i) (q i) k++(p i).toList⟩
def backward (src : Fin t) (p q z : Fin t → Option Bool)
 (H : Fin t → Nat) (A : Fin t → List Bool) (n k : Nat) : Configuration t 5 :=
 ⟨2,fun i=>if i=src then k else H i+(block (p i) (q i) k).length,output p q z A n⟩
def backMiddle (src : Fin t) (p q z : Fin t → Option Bool)
 (H : Fin t → Nat) (A : Fin t → List Bool) (n k : Nat) : Configuration t 5 :=
 ⟨3,fun i=>if i=src then k+1 else H i+(block (p i) (q i) k).length+(q i).toList.length,
   output p q z A n⟩

def Ready (src : Fin t) (p q z : Fin t → Option Bool)
 (H : Fin t → Nat) (A : Fin t → List Bool) (n : Nat) : Prop :=
 H src=1 ∧ A src=CompareMachine.word n ∧ p src=none ∧ q src=none ∧ z src=none ∧
 ∀ i, (p i≠none ∨ q i≠none ∨ z i≠none) → H i=(A i).length

variable (src : Fin t) (p q z : Fin t → Option Bool)
 (H : Fin t → Nat) (A : Fin t → List Bool) (n : Nat)
 (h : Ready src p q z H A n)

include h

theorem forward_step (k : Nat) (hk : k<n) :
 step (machine src p q z) (forward src p q H A k)=some (middle src p q H A k) := by
 obtain ⟨hh,ha,hp,hq,hz,he⟩:=h
 simp [step,machine,forward,Configuration.scanned,hp,hq,ha,hk]
 apply configuration_ext
 · rfl
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,middle,HeadMove.apply]
   · cases hpi:p i <;> simp [applyAction,middle,hi,hpi,HeadMove.apply]
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,middle,hp,hq]
   · cases hpi:p i with
     | none => simp [applyAction,middle,hpi]
     | some b =>
       have hie : H i=(A i).length := he i (Or.inl (by simp [hpi]))
       simp [applyAction,middle,hpi,hi,hie,←List.length_append,Streaming.write_append,List.append_assoc]

theorem middle_step (k : Nat) :
 step (machine src p q z) (middle src p q H A k)=some (forward src p q H A (k+1)) := by
 obtain ⟨hh,ha,hp,hq,hz,he⟩:=h
 simp [step,machine,middle]
 apply configuration_ext
 · rfl
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,forward,HeadMove.apply]
   · cases hqi:q i <;> simp [applyAction,forward,hi,hqi,HeadMove.apply,block,List.length_append,Nat.add_assoc]
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,forward,hp,hq]
   · cases hqi:q i with
     | none => simp [applyAction,forward,hqi,block,List.append_assoc]
     | some b =>
       have hie : H i=(A i).length := he i (Or.inr (Or.inl (by simp [hqi])))
       simp [applyAction,forward,hqi,hi,hie,block,←List.length_append,Streaming.write_append,List.append_assoc]

theorem turn_step :
 step (machine src p q z) (forward src p q H A n)=some (backward src p q z H A n n) := by
 obtain ⟨hh,ha,hp,hq,hz,he⟩:=h
 simp [step,machine,forward,Configuration.scanned,hp,hq,ha]
 apply configuration_ext
 · rfl
 · funext i
   by_cases hi:i=src <;> simp [applyAction,backward,hi,HeadMove.apply]
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,backward,output,hp,hq,hz]
   · cases hzi:z i with
     | none => simp [applyAction,backward,output,hzi]
     | some b =>
       have hie : H i=(A i).length := he i (Or.inr (Or.inr (by simp [hzi])))
       simp [applyAction,backward,output,hzi,hi,hie,←List.length_append,Streaming.write_append]

theorem backward_step (k : Nat) (hk : k<n) :
 step (machine src p q z) (backward src p q z H A n (k+1))=
  some (backMiddle src p q z H A n k) := by
 obtain ⟨hh,ha,hp,hq,hz,he⟩:=h
 simp [step,machine,backward,Configuration.scanned,output,hp,hq,hz,ha,hk]
 apply configuration_ext
 · rfl
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,backMiddle,HeadMove.apply]
   · cases hpi:p i <;> cases hqi:q i <;>
       simp [applyAction,backMiddle,hi,hpi,hqi,HeadMove.apply,block,List.length_append,Nat.add_assoc]
 · rfl

omit h in
theorem backMiddle_step (k : Nat) :
 step (machine src p q z) (backMiddle src p q z H A n k)=
  some (backward src p q z H A n k) := by
 simp [step,machine,backMiddle]
 apply configuration_ext
 · rfl
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,backward,HeadMove.apply]
   · cases hqi:q i <;> simp [applyAction,backward,hi,hqi,HeadMove.apply]
 · rfl

theorem halt_step :
 step (machine src p q z) (backward src p q z H A n 0)=
  some (⟨4,H,output p q z A n⟩ : Configuration t 5) := by
 obtain ⟨hh,ha,hp,hq,hz,he⟩:=h
 simp [step,machine,backward,Configuration.scanned,output,hp,hq,hz,ha]
 apply configuration_ext
 · rfl
 · funext i
   by_cases hi:i=src
   · subst i; simp [applyAction,HeadMove.apply,hh]
   · simp [applyAction,hi,HeadMove.apply]
 · rfl

theorem forward_timed (k : Nat) (hk : k≤n) :
 Timed (machine src p q z) (2*k) (forward src p q H A 0) (forward src p q H A k) := by
 induction k with
 | zero => exact Timed.refl _ _
 | succ k ih =>
   have hs := (Timed.single (by rfl) (forward_step src p q z H A n h k (by omega))).trans
     (Timed.single (by rfl) (middle_step src p q z H A n h k))
   have ht := (ih (by omega)).trans hs
   have hc : 2*k+(1+1)=2*(k+1) := by omega
   simpa only [hc] using ht

theorem backward_timed (k : Nat) (hk : k≤n) :
 Timed (machine src p q z) (2*k+1) (backward src p q z H A n k)
  (⟨4,H,output p q z A n⟩ : Configuration t 5) := by
 induction k with
 | zero => exact Timed.single (by rfl) (halt_step src p q z H A n h)
 | succ k ih =>
   have hs := (Timed.single (by rfl) (backward_step src p q z H A n h k (by omega))).trans
     ((Timed.single (by rfl) (backMiddle_step src p q z H A n k)).trans (ih (by omega)))
   have hc : 1+(1+(2*k+1))=2*(k+1)+1 := by omega
   simpa only [hc] using hs

theorem run : Step (machine src p q z) (4*n+2) H A H (output p q z A n) := by
 have ht := (forward_timed src p q z H A n h n (Nat.le_refl n)).trans
   ((Timed.single (by rfl) (turn_step src p q z H A n h)).trans
    (backward_timed src p q z H A n h n (Nat.le_refl n)))
 have hc : 2*n+(1+(2*n+1))=4*n+2 := by omega
 rw [hc] at ht
 have hi : forward src p q H A 0=(⟨(machine src p q z).start,H,A⟩ : Configuration t 5) := by
  apply configuration_ext
  · rfl
  · funext i
    by_cases he:i=src
    · subst i; simp [forward,h.1]
    · simp [forward,he]
  · funext i; simp [forward]
 rw [hi] at ht
 obtain ⟨r,hr,hf,hs⟩:=ht.run (by rfl)
 exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

end Driver
end PaidDriverBank
