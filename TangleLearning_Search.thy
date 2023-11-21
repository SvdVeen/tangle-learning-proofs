theory TangleLearning_Search
imports Main TangleAttractors
begin

context paritygame begin

(** I may want to use this and move it to paritygames.thy.
    More, similar abbreviations for using concepts in a restricted subgame may be useful for
    legibility.*)
abbreviation (input) valid_subgame :: "'v set \<Rightarrow> bool" where
  "valid_subgame R \<equiv> R\<subseteq>V \<and> paritygame (Restr E R) R (V\<^sub>0\<inter>R)"

context
  fixes T :: "'v set set"
  assumes tangles_T: "\<forall>t\<in>T. tangle EVEN t \<or> tangle ODD t"
  assumes fin_T: "finite T"
begin

(** search_step represents a single iteration of the while-loop in the search algorithm. *)
inductive search_step ::
  "'v set \<times> ('v set \<times> 'v strat) set \<Rightarrow> 'v set \<times> ('v set \<times> 'v strat) set \<Rightarrow> bool" where
  step: "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R);
          p = pr_set R; \<alpha> = player_wins_pr p;
          A = {v. v \<in> R \<and> pr v = p};
          T\<^sub>\<alpha> = {t. t \<in> T \<and> paritygame.tangle (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> t};
          paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T\<^sub>\<alpha> A Z \<sigma>;
          V\<^sub>\<alpha> = V_player \<alpha>; V\<^sub>\<beta> = V_opponent \<alpha>;
          Ov = {v. v \<in> V\<^sub>\<alpha>\<inter>A \<and> E `` {v} \<inter> Z \<noteq> {}} \<union> {v. v \<in> V\<^sub>\<beta>\<inter>A \<and> (E `` {v}) \<inter> R \<subseteq> Z};
          Y' = (if Ov \<noteq> {} then Y \<union> {(S,\<sigma>). nt_bottom_SCC S} else Y);
          R' = R-Z\<rbrakk> \<Longrightarrow> search_step (R,Y) (R',Y')"

(** search_step is inversely monotonous on R: R strictly decreases with every step. *)
lemma search_step_R_anti_mono: "search_step S S' \<Longrightarrow> fst S' \<subset> fst S"
proof (induction rule: search_step.induct)
  case (step R p \<alpha> A T\<^sub>\<alpha> Z \<sigma> V\<^sub>\<alpha> V\<^sub>\<beta> Ov Y' Y R')
  from step(7) have tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V \<inter> R) (V\<^sub>0 \<inter> R) pr \<alpha> t"
    by blast
  from step(7) have fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by simp

  from finite_subset[OF step(2) fin_V] have fin_R: "finite R" .
  from step(1) step(6) step(4) have A_notempty: "A \<noteq> {}"
    using pr_set_exists[OF fin_R step(1)] by blast
  from step(6) have A_in_R: "A \<subseteq> R" by simp

  from A_notempty paritygame.target_in_tangle_attractor[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)]
  have Z_notempty: "Z \<noteq> {}" by blast
  from A_in_R paritygame.tangle_attractor_ss[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)] step(2)
  have Z_in_V_int_R: "Z \<subseteq> V \<inter> R" by blast

  from step(13) Z_notempty Z_in_V_int_R show ?case by auto
qed

(** If a step can be applied, both R and R' are subsets of V. *)
lemma search_step_R_in_V: "search_step S S' \<Longrightarrow> fst S \<subseteq> V \<and> fst S' \<subseteq> V"
  by (induction rule: search_step.induct) auto

(** If a step can be applied, both R and R' are finite. *)
lemma search_step_R_finite: "search_step S S' \<Longrightarrow> finite (fst S) \<and> finite (fst S')"
  using search_step_R_in_V finite_subset[OF _ fin_V] by auto

(** Because R is finite and decreases with every step, search_step is a well-founded relation. *)
lemma search_step_wellfounded: "wfP (search_step\<inverse>\<inverse>)"
  unfolding wfP_def
  apply (rule wf_subset[of "inv_image (finite_psubset) (\<lambda>(R,Y). R)"]; clarsimp)
  subgoal for R' Y' R Y
    using search_step_R_anti_mono[of "(R,Y)" "(R',Y')"] search_step_R_finite[of "(R,Y)"]
    by simp
  done

(** If a step is applied from some S, R' in S' is always a valid parity game. *)
lemma step_result_R_is_paritygame:
  "search_step S S' \<Longrightarrow> paritygame (Restr E (fst S')) (V\<inter>fst S') (V\<^sub>0\<inter>fst S')"
proof (induction rule: search_step.induct)
  case (step R p \<alpha> A T\<^sub>\<alpha> Z \<sigma> V\<^sub>\<alpha> V\<^sub>\<beta> Ov Y' Y R')

  from step(7) have tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V \<inter> R) (V\<^sub>0 \<inter> R) pr \<alpha> t"
    by simp
  from step(7) have fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by simp

  from step(13) have "(V \<inter> R-Z) = (V \<inter> R')" by blast
  moreover from step(13) have "(V\<^sub>0 \<inter> R-Z) = (V\<^sub>0 \<inter> R')" by blast
  moreover from step(13) have "(Restr (Restr E R) (V \<inter> R')) = Restr E R'" using E_in_V by auto
  ultimately show ?case
    using paritygame.remove_tangle_attractor_subgame[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)] by auto
qed

(** If R is a valid non-empty subgame, then search_step can always be applied.
    The specifics of Y are not relevant, as it has no preconditions in the step. *)
lemma search_step_continues_on_valid_R:
  "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)\<rbrakk> \<Longrightarrow> Domainp search_step (R,Y)"
proof -
  assume R_notempty: "R\<noteq>{}" and
         R_in_V: "R \<subseteq> V" and
         R_valid_subgame: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  (** All we have to do is define the local variables with their conditions in the step. *)
  moreover define p where "p = pr_set R"
  moreover define \<alpha> where "\<alpha> = player_wins_pr p"
  moreover define A where "A = {v. v\<in>R \<and> pr v = p}"
  moreover define T\<^sub>\<alpha> where "T\<^sub>\<alpha> = {t. t \<in> T \<and> paritygame.tangle (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> t}"
  moreover from T\<^sub>\<alpha>_def have
    tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> t" and
    fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by auto
  moreover obtain Z \<sigma> where
    "paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T\<^sub>\<alpha> A Z \<sigma>"
    using paritygame.tangle_attractor_exists[OF R_valid_subgame tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha>] by blast
  moreover define V\<^sub>\<alpha> where "V\<^sub>\<alpha> = V_player \<alpha>"
  moreover define V\<^sub>\<beta> where "V\<^sub>\<beta> = V_opponent \<alpha>"
  moreover define Ov where
    "Ov = {v. v \<in> V\<^sub>\<alpha>\<inter>A \<and> E `` {v} \<inter> Z \<noteq> {}} \<union> {v. v \<in> V\<^sub>\<beta>\<inter>A \<and> (E `` {v}) \<inter> R \<subseteq> Z}"
  moreover define Y' where "Y' = (if Ov \<noteq> {} then Y \<union> {(S,\<sigma>). nt_bottom_SCC S} else Y)"
  moreover define R' where "R' = R-Z"
  (** Now, we can put them in their place in the step, and our thesis follows automatically. *)
  ultimately have "search_step (R,Y) (R',Y')"
    using search_step.step by blast
  thus ?thesis by blast
qed

(** TODO: invariant, prove property of Y on termination. *)

(** The search algorithm applies the search_step until it reaches the end.
    We do not have to specify that ({},Y) is not in the domain of the step,
    as this follows automatically because an empty R is not allowed.
    (see next lemma) *)
definition search :: "'v set \<Rightarrow> ('v set \<times> 'v strat) set \<Rightarrow> bool" where
  "search R Y \<equiv> search_step\<^sup>*\<^sup>* (R,{}) ({},Y)"

lemma search_terminates_on_empty_R: "\<not>Domainp search_step ({},Y)"
  using search_step_R_anti_mono[of "({},Y)"]
  by auto

(** If we start from a valid, non-empty subgame, through applying search_step, we will always reach
    a final state with a corresponding Y. *)
lemma search_step_terminates_with_Y:
  "\<lbrakk>fst S \<noteq> {}; fst S \<subseteq> V; paritygame (Restr E (fst S)) (V\<inter>fst S) (V\<^sub>0\<inter>fst S)\<rbrakk>
  \<Longrightarrow> \<exists>Y. search_step\<^sup>*\<^sup>* S ({},Y)"
  using search_step_wellfounded
  unfolding wfP_def
proof (induction S rule: wf_induct_rule)
  case (less x)
  (** Because R in x is a valid non-empty subgame, we know there is a state y that succeeds
      it in search_step. *)
  from search_step_continues_on_valid_R[OF less.prems, of "snd x"]
  have "Domainp search_step x" by simp
  then obtain y where step_x_y: "search_step x y" by blast
  (** Now we consider whether R' in the successor y is empty or not. *)
  consider (empty_R') "fst y = {}" | (nonempty_R') "fst y \<noteq> {}" by blast
  thus ?case proof cases
    (** If R' in y is already empty, we clearly have a step from x to an endpoint. *)
    case empty_R'
    with step_x_y have "search_step x ({}, snd y)"
      using surjective_pairing[of y] by auto
    thus ?thesis by blast
  next
    (** If R' is not empty, then we know it is a valid subgame in V by the properties of the
        step. *)
    case nonempty_R'
    moreover from search_step_R_in_V[OF step_x_y] have "fst y \<subseteq> V" ..
    moreover from step_result_R_is_paritygame[OF step_x_y]
    have "paritygame (Restr E (fst y)) (V \<inter> fst y) (V\<^sub>0 \<inter> fst y)" .
    moreover note step_x_y
    (** By the induction hypothesis, we then know that from y, we can reach a state with an empty
        R and a valid Y.*)
    ultimately obtain Y where "search_step\<^sup>*\<^sup>* y ({}, Y)"
      using less.IH by blast
    (** We also know you can reach y from x. By the transitivity of the reflexive transitive
        closure, we can now say that we can reach the state with an empty R from x, via y. *)
    moreover from step_x_y have "search_step\<^sup>*\<^sup>* x y" by simp
    ultimately show ?thesis using rtranclp_trans by fast
  qed
qed


(** For every valid, non-empty subgame R, the search algorithm finds a Y. *)
lemma search_has_result:
  "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)\<rbrakk> \<Longrightarrow> \<exists>Y. search R Y"
  unfolding search_def
  using search_step_terminates_with_Y by simp

end (** End of context with fixed T. *)

end (** End of context paritygame *)

end