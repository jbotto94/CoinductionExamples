Require Import Paco.paco.
Require Import String.



Open Scope string_scope.

CoInductive Trace :=
| Tau (_: Trace)
| Vis (_: string) (_: Trace).




Definition tau_step (t t1: Trace) : Prop := t = Tau t1.

Definition vis_step (t t1: Trace) (s: string) : Prop := t = Vis s t1.


Inductive tau_star : Trace -> Trace -> Prop :=
| tau_star_refl : forall t, tau_star t t
| tau_star_cons : forall t t1 (CONS: tau_star t1 t), tau_star (Tau t1) t.
Hint Constructors tau_star.

Definition weak_tau_step (t t1: Trace) := exists t' t1', tau_star t t' /\ tau_step t' t1' /\ tau_star t1' t1.

Definition weak_vis_step (t t1: Trace) (s: string) := exists t' t1', tau_star t t' /\ vis_step t' t1' s /\ tau_star t1' t1.


Inductive weak_sim_step (P: Trace -> Trace -> Prop) : Trace -> Trace -> Prop :=
| weak_tau_sim_step : forall t t' t1 t1' (WEAKTAUSTEP: weak_tau_step t t')
                        (WEAKTAUSTAR: tau_star t1 t1')
                        (HWeakSimStep: P t' t1'),
    weak_sim_step P t t1
| weak_vis_sim_step : forall t t' t1 t1' s (WEAKVISSTEP: weak_vis_step t t' s)
                        (WEAKTAUSTAR: weak_vis_step t1 t1' s)
                        (HWeakSimStep: P t' t1'),
    weak_sim_step P t t1.

Hint Constructors weak_sim_step.



Definition weak_sim (p p1: Trace) := paco2 weak_sim_step bot2 p p1.

Definition weak_bisim (p p1: Trace) := weak_sim p p1 /\ weak_sim p1 p.


CoFixpoint graph := Vis "A" (Vis "B" graph).
CoFixpoint graph1 := Vis "A" (Tau (Tau (Vis "B" graph1))).



Definition unroll_trace_func (t: Trace) : Trace :=
  match t with
  | Tau a => Tau a
  | Vis a b => Vis a b
  end.

Lemma unroll_trace : forall t, t = unroll_trace_func t.
Proof.
  destruct t; auto. Qed.

Lemma graph_equiv : weak_bisim graph graph1.
Proof.
  constructor.
  +pcofix CIH. pfold.
   unfold graph, graph1.
   rewrite unroll_trace at 1; simpl.
   rewrite unroll_trace; simpl.
   eapply weak_vis_sim_step with (s := "A") (t' := (Vis "B" graph)) (t1' := (Tau (Tau (Vis "B" graph1))));
     unfold weak_vis_step; try repeat esplit; eauto.

   
  left. pfold.
  eapply weak_vis_sim_step with (s := "B") (t' := graph) (t1' := graph1);
    unfold weak_vis_step; try repeat esplit; eauto.



  +pcofix CIH. pfold.
   unfold graph, graph1.
   rewrite unroll_trace at 1; simpl.
   rewrite unroll_trace; simpl.

   eapply weak_vis_sim_step with (s := "A") (t' := (Tau (Vis "B" graph1)));
     unfold weak_vis_step; repeat esplit; eauto.

   left. pfold.


   eapply weak_tau_sim_step with (t' := (Vis "B" graph1));
     unfold weak_tau_step, weak_vis_step; repeat esplit; eauto.


   left. pfold.


   eapply weak_vis_sim_step with (t1' := graph) (t' := graph1);
   unfold weak_vis_step; repeat esplit; eauto. Qed.

   

   
