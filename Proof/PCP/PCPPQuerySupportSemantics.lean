import Proof.PCP.PCPPQuerySourceCall

/-! The physical support parser returns the literal selected support mask
from the same source PCPP object. The index driver is the actual unary
template produced by the query entry, including its trailing zero. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupport
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mask {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin p.systematicBits) : List Bool :=
  List.ofFn fun j : Fin r.arity => decide (j∈p.systematicSupport i)
def supportRows {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) := List.ofFn (mask r p)
def clauseTail {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :=
  natListWord ((List.ofFn fun i : Fin (2^p.clauseBits) =>
    [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right]).flatten)
def headerBits {n0 : ℕ} {r : PCPPRequest n0} (p : PointwisePCPP r.circuit) :=
  PCPPQueryField.fourBits 3 p.systematicBits p.auxiliaryBits p.clauseBits

theorem output_word {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :
    pcppOutput r p=headerBits p++(supportRows r p).flatten++clauseTail r p := by
  simp [pcppOutput,headerBits,supportRows,clauseTail,natListWord,
    PCPPQueryField.fourBits,PCPPQueryField.pairBits,PCPPQueryField.fieldBits,List.append_assoc]
  rfl

noncomputable def ready (source : List Bool) (arity index : ℕ) :=
  (⟨machine.start,![0,0,0,1,0,1],![source,[],[],UnaryTemplate.tape arity,[],UnaryTemplate.tape index]⟩ :
    Configuration 6 (16+(Fintype.card (RepeatMachine.Control 5)+5)))
def capacity (index : ℕ) : Fin 6→ℕ := fun i => if i=5 then index+2 else 0

theorem template_pad (index : ℕ) : ZeroPadding.pad (index+2) (CompareMachine.word index)=UnaryTemplate.tape index := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem ready_eq (source : List Bool) (arity index : ℕ) :
    ZeroPadding.config (capacity index) (entry source arity index)=ready source arity index := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,entry,ready,capacity,template_pad]

theorem lookup_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin p.systematicBits) :
    ∃ receipt,runFrom machine (budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity i.val)
      (ready (pcppOutput r p) r.arity i.val)=some receipt ∧
      receipt.steps=budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity i.val ∧
      receipt.final.tapes 4=mask r p i ∧ receipt.final.heads 4=r.arity := by
  let rows := supportRows r p
  have hi : i.val<rows.length := by simp [rows,supportRows]
  have hs : (rows.take i.val).flatten++rows[i.val]++(rows.drop (i.val+1)).flatten=rows.flatten :=
    MatrixCropCells.split_at rows i.val hi
  have hm : rows[i.val]=mask r p i := by simp [rows,supportRows]
  have hw : ∀ row∈rows.take i.val,row.length=r.arity := by
    intro row hrow
    have hmem := List.mem_of_mem_take hrow
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hmem
    rw [← hj]
    simp [mask]
  have hrow : (rows[i.val]).length=r.arity := by rw [hm]; simp [mask]
  obtain ⟨base,hb,_,_,_,_,hout,hhead,_,_,hsteps⟩ := support_run p.systematicBits p.auxiliaryBits p.clauseBits
    r.arity (rows.take i.val) rows[i.val] ((rows.drop (i.val+1)).flatten++clauseTail r p) hw hrow
  have hsource : headerBits p++(rows.take i.val).flatten++rows[i.val]++
      ((rows.drop (i.val+1)).flatten++clauseTail r p)=pcppOutput r p := by
    rw [output_word]
    rw [← hs]
    simp only [rows,List.append_assoc]
  change runFrom machine (budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity (rows.take i.val).length)
    (entry (headerBits p++(rows.take i.val).flatten++rows[i.val]++
      ((rows.drop (i.val+1)).flatten++clauseTail r p)) r.arity (rows.take i.val).length)=some base at hb
  have hlen : (rows.take i.val).length=i.val := by simp [List.length_take,Nat.min_eq_left hi.le]
  rw [hsource,hlen] at hb
  rw [hlen] at hsteps
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config machine (capacity i.val) _ _ base hb
  rw [ready_eq] at ha
  refine ⟨actual,ha,has.trans hsteps,?_,?_⟩
  · rw [haf]
    simpa [ZeroPadding.config,capacity,hm] using hout
  · rw [haf]
    exact hhead

end NearCubicWires.RepairOrdinary.PCPPQuerySupport
