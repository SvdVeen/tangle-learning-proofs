theory PredicateTermination
  imports Main
begin
(**
  Authors:
    - Suzanne van der Veen
    - Peter Lammich
    - Tom van Dijk

  This theory focuses on defining termination for predicate relations.
  We give an inductive definition that identifies whether a predicate terminates from some state.
*)
chapter \<open>Predicate Termination\<close>
(** This inductive definition shows that a predicate relation terminates from some state
    if all successor states in the relation terminate. *)
inductive trm for r where
  "\<forall>b. r a b \<longrightarrow> trm r b \<Longrightarrow> trm r a"

(** If we have a state that does not have successors in the relation, the relation
    terminates from that state. *)
lemma trm_endpoint:
  "\<nexists>b. r a b \<Longrightarrow> trm r a"
  by (simp add: trm.intros)

(** Any predicate that terminates from some state has a final state that can be reached
    from that initial state. *)
lemma trm_final_state:
  "trm r a \<Longrightarrow> \<exists>b. r\<^sup>*\<^sup>* a b \<and> \<not>Domainp r b"
  apply (induction rule: trm.induct)
  apply (simp add: Domainp.simps)
  using rtranclp_trans[of r] by blast

section \<open>Well-Founded Predicates\<close>
(** A well-founded predicate relation terminates from any state. *)
lemma wfP_terminates:
  "wfP r\<inverse>\<inverse> \<Longrightarrow> trm r a"
  apply (induction rule: wfP_induct_rule)
  by (blast intro: trm.intros)

(** A predicate relation that is well-founded under some invariant that is preserved
    by that relation terminates from any state that satisfies the invariant. *)
lemma wfP_I_terminates:
  assumes I_init: "I a"
  assumes I_preserved: "\<And>a b. I a \<Longrightarrow> r a b \<Longrightarrow> I b"
  assumes wfP_under_I: "wfP (\<lambda>b a. r a b \<and> I a)"
  shows "trm r a"
  using wfP_under_I I_init
  apply (induction rule: wfP_induct_rule)
  by (blast intro: trm.intros I_preserved)
end
