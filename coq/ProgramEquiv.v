Require Import Paco.paco.
Require Import List.
Require Import String.
Set Implicit Arguments.
Open Scope string_scope.


(*In this example, it will be shown how a simple program optimisation can be proven correct by showing the original program bisimulates the result of the optimisation*)


(*This is just a useful tactic*)
Ltac inv H := inversion H; subst; try clear H.


(*Basic do notation*)
Definition err (A: Type) := sum string A.

Definition raise A (s: string) : err A := inl s.
Definition ret A (a: A) : err A := inr a.


Definition bind A B (s: err A) (f: A -> err B) : err B :=
  match s with
  | inl s => inl s
  | inr t => f t              
  end.

Notation "m >>= f"  := (bind m f) (at level 60, right associativity).





(*A trace consists of a potentially infinite list of silent actions (Tau steps) followed by either an error state or a final state.*)
CoInductive Trace :=
| Tau (t: Trace)
| Err (s: string)
| Fin (n: nat).



(*Now the language is defined*)

(*A program counter is just a natural number*)
Definition pc := nat.
Definition pc_eqb := Nat.eqb.

(*A variable is defined as a string*)
Definition var := string.
Definition var_eqb := eqb.


(*A value, is also a natural number*)
Definition value := nat.


Inductive expr :=
| Add (_ _: expr)
| Var (_: var)
| Value (n: nat).

Inductive instr :=
| Asn (_: var) (_: expr) (_: pc)
| If (_: expr) (_ _: pc)
| Ret (_: expr).

Definition program := list (pc * instr).







(*Now, the semantics of the toy langauge*)


(*Fetches an instruction from a program associated to a given program counter*)
Fixpoint fetch_instr (l: program) (p: pc) : err instr :=
  match l with
  | nil => raise instr "Instruction not found"
  | (h :: s)%list => if pc_eqb p (fst h) then ret (snd h) else fetch_instr s p                                                          
  end.


(* A local enviroment is defined as a list linking variables with values:*)
Definition env := list (var * value).


(*Functions for interacting with the local environment*)
Fixpoint get_value (l: env) (v: var) : err value :=
  match l with
  | nil => raise value "Value not found in env"
  | (h :: s)%list => if var_eqb v (fst h) then ret (snd h) else get_value s v
  end.

Definition set_value (l: env) (v: var) (val: value) : env :=
  ((v, val) :: l)%list.


(*A state is a tuple consisting of a program counter and a local environment*)
Definition state : Set := (pc * env).

(*A transition state is defined as follows*)
Inductive transition :=
| Step (s: state)
| Return (n: nat).




(*Evaluates a given expression under a local environment*)
Fixpoint eval_expr (e: expr) (e1: env) : err value :=
  match e with
  | Add v v1 => (eval_expr v e1) >>=
                                (fun x => eval_expr v1 e1 >>=
                                                 (fun y => ret (x + y)))
  | Var v => get_value e1 v
  | Value v => ret v                    
  end.

(*Evaluates a given instruction*)

Definition eval_instr (i: instr) (e: env) : err transition :=
  match i with
  | Asn var expr next_pc =>
    eval_expr expr e >>= (fun v => ret (Step (next_pc, set_value e var v)))
  | If expr p p1 =>
    eval_expr expr e >>= (fun v => match v with
                                  | 1 => ret (Step (p1, e))
                                  | _ => ret (Step (p, e))
                                end)
  | Ret r =>
    eval_expr r e >>= (fun v => ret (Return v))
  end.


(*Defines a single step of computation from a given state*)
Definition eval_single_step (s: state) (p: program) : err transition :=
  fetch_instr p (fst s) >>= (fun v => eval_instr v (snd s)).


(*The overall semantics of the language*)
CoFixpoint step_sem (s: state) (p: program) : Trace :=
  match eval_single_step s p with
  | inr (Step s') => Tau (step_sem s' p)
  | inr (Return r) => Fin r
  | inl l => Err l              
  end.



(*Now lets define a weak bisimulation*)


(*A tau relation between t and t1*)
Definition tau_step (t t1: Trace) : Prop := t = Tau t1.

(*The transitive closure of a tau step*)
Inductive tau_star : Trace -> Trace -> Prop :=
| tau_star_refl : forall t, tau_star t t
| tau_star_cons : forall t t1 (CONS: tau_star t1 t), tau_star (Tau t1) t.
Hint Constructors tau_star.


Definition weak_tau_step (t t1: Trace) := exists t' t1', tau_star t t' /\ tau_step t' t1' /\ tau_star t1' t1.

Definition weak_fin_step (t: Trace) (v: value) := tau_star t (Fin v).

Definition weak_error_step (t: Trace) := exists s, tau_star t (Err s).



Inductive weak_sim_step (P: Trace -> Trace -> Prop) : Trace -> Trace -> Prop :=
| weak_tau_sim_step : forall t t' t1 t1' (WEAKTAUSTEP: weak_tau_step t t')
                        (WEAKTAUSTAR: tau_star t1 t1')
                        (HWeakSimStep: P t' t1'),
    weak_sim_step P t t1
| weak_err_sim_step : forall t t1 (WEAKVERRSTEP: weak_error_step t)
                        (WEAKTAUSTAR: weak_error_step t1),
    weak_sim_step P t t1
| weak_fin_sim_step : forall t t1 v (WEAKVERRSTEP: weak_fin_step t v)
                        (WEAKTAUSTAR: weak_fin_step t1 v),
    weak_sim_step P t t1.

Hint Constructors weak_sim_step.


Definition weak_sim (p p1: Trace) := paco2 weak_sim_step bot2 p p1.

Definition weak_bisim (p p1: Trace) := weak_sim p p1 /\ weak_sim p1 p.






(*Some useful lemmas about traces*)

Lemma err_sim_step_refl:
  forall (r : Trace -> Trace -> Prop) (s0 : string), weak_sim_step (upaco2 weak_sim_step r) (Err s0) (Err s0).
Proof.
  intros r s0.
  eapply weak_err_sim_step; unfold weak_error_step; eauto. Qed.
Hint Resolve err_sim_step_refl.


Lemma fin_sim_step_refl:
  forall (r : Trace -> Trace -> Prop) (n : nat), weak_sim_step r (Fin n) (Fin n).
Proof.
  intros r n.
  eapply weak_fin_sim_step with (v := n);
    unfold weak_fin_step; auto. Qed.
Hint Resolve fin_sim_step_refl.






(** Constant folding is an optimisation which attempts to replace expression in which all values are constant for the result of its computation*)


Fixpoint const_fold_expr (v: expr) : expr :=
  match v with
  | Add e e1 =>
    let val := const_fold_expr e in
    let val1 := const_fold_expr e1 in
    match val, val1 with
    | Value n, Value n1 => Value (n + n1)
    | t, t1 => Add t t1                            
    end
  | _ => v
  end.

Definition const_fold_instr (i: instr) : instr :=
  match i with
  | Asn var exp next_pc => Asn var (const_fold_expr exp) next_pc
  | If exp p p1 => If (const_fold_expr exp) p p1
  | Ret r => Ret (const_fold_expr r)                   
  end.

Definition const_fold_program (p: program) : program := map (fun i => (fst i, const_fold_instr (snd i))) p.








(** Now let's prove some useful lemmas that show constant folding is correct: **)

Lemma const_fold_expr_correct : forall e e1,
    eval_expr e e1 = eval_expr (const_fold_expr e) e1.
Proof.
  induction e; simpl; auto.
  intros.
  erewrite IHe1.
  erewrite IHe2.
  destruct ( eval_expr (const_fold_expr e1) e0) eqn:EVALE1;
    destruct (eval_expr (const_fold_expr e2) e0) eqn:EVALE2; simpl in *; destruct (const_fold_expr e1) eqn:CONSTE1; simpl in *;
      try rewrite EVALE1; try rewrite EVALE2; simpl; auto;
        destruct (const_fold_expr e2) eqn:CONSTE2; try discriminate;
          inv EVALE1; simpl in *;
            try rewrite EVALE2; simpl; auto;
  inv EVALE2; auto. Qed.

Lemma const_fold_instr_correct : forall i e,
    eval_instr i e = eval_instr (const_fold_instr i) e.
Proof.
  unfold const_fold_instr.
  unfold eval_instr.
  intros.
  destruct i; rewrite const_fold_expr_correct; auto. Qed.

Lemma const_fold_eval_single_step_correct : forall p s, eval_single_step s p = eval_single_step s (const_fold_program p).
Proof.
  induction p; simpl; auto.
  intros.
  unfold eval_single_step.
  unfold fetch_instr. simpl.
  destruct (pc_eqb (fst s) (fst a)) eqn:?; auto.
  +apply const_fold_instr_correct.
  +unfold eval_single_step in *.
   unfold fetch_instr in *.
   auto. Qed.




(*This is a simple trick that allows a single element of the trace to be evaluated*)

Definition trace_unroll_func (t: Trace) : Trace :=
  match t with
  | Tau t => Tau t
  | Err s => Err s
  | Fin f => Fin f          
  end.


Lemma trace_unroll : forall t, t = trace_unroll_func t.
Proof. destruct t; simpl; auto. Qed.




(*This is a simple tactic that tries to simplifying according to betaiota reduction*)

Ltac simplify_tau_steps := try red; repeat esplit; eauto.



(**Now let's prove the overall correctness of the optimisation**)
Lemma const_fold_correct : forall p s, weak_bisim (step_sem s p) (step_sem s (const_fold_program p)).
Proof.
  intros p s.
  unfold weak_bisim. split.
  +revert s.
   pcofix CIH. intros.
   pfold.
   rewrite trace_unroll at 1.
   rewrite trace_unroll; simpl.

   rewrite const_fold_eval_single_step_correct.
   destruct (eval_single_step s
                              (const_fold_program p)) eqn:?; simpl; eauto.
   destruct t; auto.
   eapply weak_tau_sim_step with (t' := (step_sem s0 p)) (t1' := (step_sem s0 (const_fold_program p)));
     simplify_tau_steps.


   
   +revert s.
       pcofix CIH. intros.
   pfold.
   rewrite trace_unroll at 1.
   rewrite trace_unroll; simpl.

   rewrite <- const_fold_eval_single_step_correct.
   destruct (eval_single_step s p) eqn:?; auto.
   destruct t; auto.
   eapply weak_tau_sim_step with (t' := (step_sem s0 (const_fold_program p))) (t1' := (step_sem s0 p));
     simplify_tau_steps.
Qed.

